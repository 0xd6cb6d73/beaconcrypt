-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication

/-! Public native World effects retain every operational coordinate when the external selected-KEM interface omits only private uniform accounting. Lazy hidden seed resolution and the shared hash cache keep their exact draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects
open PqxdhRecordLiftInterface (Role KernelRef CapabilitySpec EnvEffects)
open PqxdhRecordLiftWorld (State resolve installServer installBeacon capability effects)
open RegistrationNativeKemWorldUniform (mask)
variable {n : Nat}

private theorem resolve_canonical (role : Role) (ref : KernelRef n) (before : State n) :
    Prod.map id mask <$> (resolve role ref).run before =
      match ref with
      | .known kernel => pure (kernel, mask before)
      | .hidden slot => (fun result => (PqxdhRecordLiftWorld.kernel role result.1,
          { mask before with seeds := result.2 })) <$>
          (PqxdhRecordLiftLazyTable.impl slot).run before.seeds := by
  cases ref with
  | known kernel => simp only [resolve, StateT.run_pure, map_pure, Prod.map, id_eq]
  | hidden slot =>
      have law := congrArg (fun work => (fun result =>
          (PqxdhRecordLiftWorld.kernel role result.1.1, { result.2 with seeds := result.1.2 })) <$> work)
        (RegistrationNativeKemWorldUniform.sampled_mask ((PqxdhRecordLiftLazyTable.impl slot).run before.seeds) before)
      simpa only [resolve, StateT.run, map_bind, bind_pure_comp, Functor.map_map,
        Function.comp_def, Prod.map, id_eq, mask] using law

/-- Both known and lazily sampled hidden installations preserve the same whole projected seed state. -/
theorem resolve_input (role : Role) (ref : KernelRef n) (before : State n) :
    Prod.map id mask <$> (resolve role ref).run before =
      Prod.map id mask <$> (resolve role ref).run (mask before) := by
  rw [resolve_canonical, resolve_canonical]
  cases ref <;> rfl

private theorem installServer_input (keyId : Std.U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (ref : KernelRef n) (before : State n) :
    Prod.map id mask <$> (installServer keyId binding ref).run before =
      Prod.map id mask <$> (installServer keyId binding ref).run (mask before) := by
  cases server : before.server with
  | none => simp only [installServer, StateT.run, mask, server, map_pure, Prod.map, id_eq]
  | some owner =>
      by_cases admitted : owner.records.server.peers keyId = none ∧ PqxdhRecordLiftWorld.Unused before .server ref
      · have law := congrArg (fun work => (fun (result : ConcreteRatchetKernel × State n) => (true,
            { PqxdhRecordLiftWorld.markUsed result.2 .server ref with server := some { owner with records :=
                { owner.records with server := { owner.records.server with peers := Function.update owner.records.server.peers keyId (some ⟨binding.identity, result.1, binding.associatedArray owner.records.server.identity⟩) } } } })) <$> work)
          (resolve_input .server ref before)
        simp only [installServer, StateT.run, mask, server, PqxdhRecordLiftWorld.Unused] at admitted ⊢
        simp only [admitted, and_self, ite_true, bind_pure_comp]
        cases ref <;> simp only [Functor.map_map, Prod.map, id_eq, mask,
          PqxdhRecordLiftWorld.markUsed, server, StateT.run] at law ⊢ <;>
          convert law using 1
      · simp only [installServer, StateT.run, mask, server, PqxdhRecordLiftWorld.Unused] at admitted ⊢
        simp only [admitted, ite_false, map_pure, Prod.map, id_eq]
        simp only [mask, server]

private theorem installBeacon_input (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (ref : KernelRef n) (before : State n) :
    Prod.map id mask <$> (installBeacon owner shell ref).run before =
      Prod.map id mask <$> (installBeacon owner shell ref).run (mask before) := by
  by_cases admitted : PqxdhRecordLiftWorld.BeaconReady before owner ∧ PqxdhRecordLiftWorld.Unused before .beacon ref
  · have law := congrArg (fun work => (fun (result : ConcreteRatchetKernel × State n) => (true,
        { PqxdhRecordLiftWorld.markUsed result.2 .beacon ref with owners := before.owners.set owner (.established shell result.1) })) <$> work)
      (resolve_input .beacon ref before)
    simp only [installBeacon, StateT.run, mask, PqxdhRecordLiftWorld.BeaconReady,
      PqxdhRecordLiftWorld.Unused] at admitted ⊢
    simp only [admitted, and_self, ite_true, bind_pure_comp]
    cases ref <;> simp only [Functor.map_map, Prod.map, id_eq, mask,
      PqxdhRecordLiftWorld.markUsed, StateT.run] at law ⊢ <;>
      convert law using 1
  · simp only [installBeacon, StateT.run, mask, PqxdhRecordLiftWorld.BeaconReady,
      PqxdhRecordLiftWorld.Unused] at admitted ⊢
    simp only [admitted, ite_false, map_pure, Prod.map, id_eq, mask]

/-- Every administrative request retains actual capability refusal, lazy seed, phase and hash-cache behavior. -/
theorem capability_input (query : (CapabilitySpec n).Domain) (before : State n) :
    Prod.map id mask <$> (capability query).run before =
      Prod.map id mask <$> (capability query).run (mask before) := by
  cases query with
  | peerPresent keyId | ownerPresent owner | appendOwner sender identity phase =>
      simp only [capability, StateT.run, map_pure, Prod.map, id_eq, mask]
  | advanceOwner owner phase =>
      cases found : before.owners[owner]? with
      | none => simp only [capability, StateT.run, mask, found, map_pure, Prod.map, id_eq]
      | some current =>
          cases current with
          | established shell kernel => simp only [capability, StateT.run, mask, found, map_pure, Prod.map, id_eq]
          | inactive previous =>
              by_cases legal : PqxdhRecordLiftWorld.LegalAdvance previous phase <;>
                simp only [capability, StateT.run, mask, found, legal, ite_true, ite_false,
                  map_pure, Prod.map, id_eq]
  | installServer keyId binding ref => exact installServer_input keyId binding ref before
  | installBeacon owner shell ref => exact installBeacon_input owner shell ref before
  | hash bytes => exact RegistrationNativeKemWorldAuthentication.hash_input bytes before

/-- All original native environment effects, including direct coins and every refused capability, preserve their complete projected source outcome. -/
theorem effects_input (query : (EnvEffects n).Domain) (before : State n) :
    Prod.map id mask <$> (effects query).run before =
      Prod.map id mask <$> (effects query).run (mask before) := by
  cases query with
  | inl coin =>
      change Prod.map id mask <$> (PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _)).run
          (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before) = _
      rw [RegistrationNativeKemWorldUniform.sampled_mask]
      change _ = Prod.map id mask <$> (PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _)).run
        (PqxdhRecordLiftWorld.chargeEffect (.inl coin) (mask before))
      rw [RegistrationNativeKemWorldUniform.sampled_mask]
      rfl
  | inr request =>
      exact capability_input request (PqxdhRecordLiftWorld.chargeEffect (.inr request) before)

end BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects.resolve_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects.resolve_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects.capability_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects.capability_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects.effects_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects.effects_input
