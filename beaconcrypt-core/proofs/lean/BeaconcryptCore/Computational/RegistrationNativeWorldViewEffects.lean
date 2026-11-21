-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldView

/-! Public native World effects retain every operational coordinate when the external selected-KEM interface omits only private native and coin-effect accounting. Lazy hidden seed resolution and the shared hash cache keep their exact draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects
open PqxdhRecordLiftInterface (Role KernelRef CapabilitySpec EnvEffects)
open PqxdhRecordLiftWorld (State resolve installServer installBeacon capability effects)
open RegistrationNativeWorldView (project)
variable {n : Nat}

private theorem sampled_input {Value : Type} (work : ProbComp Value) (before : State n) :
    Prod.map id project <$> (PqxdhRecordLiftWorld.sampled work).run before =
      Prod.map id project <$> (PqxdhRecordLiftWorld.sampled work).run (project before) := by
  rw [RegistrationNativeWorldView.sampled, RegistrationNativeWorldView.sampled,
    RegistrationNativeWorldView.project_idempotent]

/-- Both known and lazily sampled hidden installations preserve the same whole projected seed state. -/
theorem resolve_input (role : Role) (ref : KernelRef n) (before : State n) :
    Prod.map id project <$> (resolve role ref).run before =
      Prod.map id project <$> (resolve role ref).run (project before) := by
  cases ref with
  | known kernel =>
      simp only [resolve, StateT.run_pure, map_pure, Prod.map, id_eq,
        RegistrationNativeWorldView.project_idempotent]
  | hidden slot =>
      have law := congrArg (fun distribution => (fun result =>
        (PqxdhRecordLiftWorld.kernel role result.1.1, { result.2 with seeds := result.1.2 })) <$> distribution)
        (sampled_input ((PqxdhRecordLiftLazyTable.impl slot).run before.seeds) before)
      simpa only [resolve, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq,
        Function.comp_def, project, RegistrationNativeWorldView.eraseNative,
        RegistrationWorldCoinCompiler.eraseCoin] using law

private theorem charge_input (query : (EnvEffects n).Domain) (before : State n) :
    project (PqxdhRecordLiftWorld.chargeEffect query before) =
      project (PqxdhRecordLiftWorld.chargeEffect query (project before)) := by
  simp only [project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin, PqxdhRecordLiftWorld.chargeEffect]
  congr 3
  funext kind
  cases kind <;> cases selected : PqxdhRecordLiftInterface.effectKind query <;>
    simp []

private theorem hash_input (bytes : Pqxdh.Bytes) (before : State n) :
    Prod.map id project <$> (capability (.hash bytes)).run before =
      Prod.map id project <$> (capability (.hash bytes)).run (project before) := by
  have law := congrArg (fun distribution => (fun result => (result.1.1,
    { result.2 with primitive := (result.2.primitive.1, result.1.2) })) <$> distribution)
    (sampled_input ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.primitive.2) before)
  simpa only [capability, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq,
    Function.comp_def, project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin] using law

private theorem installServer_input (keyId : Std.U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (ref : KernelRef n) (before : State n) :
    Prod.map id project <$> (installServer keyId binding ref).run before =
      Prod.map id project <$> (installServer keyId binding ref).run (project before) := by
  cases server : before.server with
  | none => simp only [installServer, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem, server, map_pure, Prod.map, id_eq]
  | some owner =>
      by_cases admitted : owner.records.server.peers keyId = none ∧ PqxdhRecordLiftWorld.Unused before .server ref
      · have law := congrArg (fun work => (fun (result : ConcreteRatchetKernel × State n) => (true,
            { PqxdhRecordLiftWorld.markUsed result.2 .server ref with server := some { owner with records :=
                { owner.records with server := { owner.records.server with peers := Function.update owner.records.server.peers keyId (some ⟨binding.identity, result.1, binding.associatedArray owner.records.server.identity⟩) } } } })) <$> work)
          (resolve_input .server ref before)
        simp only [installServer, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, server, PqxdhRecordLiftWorld.Unused] at admitted ⊢
        simp only [admitted, and_self, ite_true, bind_pure_comp]
        cases ref <;> simp only [Functor.map_map, Prod.map, id_eq, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, PqxdhRecordLiftWorld.markUsed, server, StateT.run] at law ⊢ <;>
          convert law using 1
      · simp only [installServer, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, server, PqxdhRecordLiftWorld.Unused] at admitted ⊢
        simp only [admitted, ite_false, map_pure, Prod.map, id_eq]
        simp only [project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem, server]

private theorem installBeacon_input (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (ref : KernelRef n) (before : State n) :
    Prod.map id project <$> (installBeacon owner shell ref).run before =
      Prod.map id project <$> (installBeacon owner shell ref).run (project before) := by
  by_cases admitted : PqxdhRecordLiftWorld.BeaconReady before owner ∧ PqxdhRecordLiftWorld.Unused before .beacon ref
  · have law := congrArg (fun work => (fun (result : ConcreteRatchetKernel × State n) => (true,
        { PqxdhRecordLiftWorld.markUsed result.2 .beacon ref with owners := before.owners.set owner (.established shell result.1) })) <$> work)
      (resolve_input .beacon ref before)
    simp only [installBeacon, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, PqxdhRecordLiftWorld.BeaconReady,
      PqxdhRecordLiftWorld.Unused] at admitted ⊢
    simp only [admitted, and_self, ite_true, bind_pure_comp]
    cases ref <;> simp only [Functor.map_map, Prod.map, id_eq, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, PqxdhRecordLiftWorld.markUsed, StateT.run] at law ⊢ <;>
      convert law using 1
  · simp only [installBeacon, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, PqxdhRecordLiftWorld.BeaconReady,
      PqxdhRecordLiftWorld.Unused] at admitted ⊢
    simp only [admitted, ite_false, map_pure, Prod.map, id_eq, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

/-- Every administrative request retains actual capability refusal, lazy seed, phase and hash-cache behavior. -/
theorem capability_input (query : (CapabilitySpec n).Domain) (before : State n) :
    Prod.map id project <$> (capability query).run before =
      Prod.map id project <$> (capability query).run (project before) := by
  cases query with
  | peerPresent keyId | ownerPresent owner | appendOwner sender identity phase =>
      simp only [capability, StateT.run, map_pure, Prod.map, id_eq, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]
  | advanceOwner owner phase =>
      cases found : before.owners[owner]? with
      | none => simp only [capability, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem, found, map_pure, Prod.map, id_eq]
      | some current =>
          cases current with
          | established shell kernel => simp only [capability, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem, found, map_pure, Prod.map, id_eq]
          | inactive previous =>
              by_cases legal : PqxdhRecordLiftWorld.LegalAdvance previous phase <;>
                simp only [capability, StateT.run, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem, found, legal, ite_true, ite_false,
                  map_pure, Prod.map, id_eq]
  | installServer keyId binding ref => exact installServer_input keyId binding ref before
  | installBeacon owner shell ref => exact installBeacon_input owner shell ref before
  | hash bytes => exact hash_input bytes before

/-- All original native environment effects, including direct coins and every refused capability, preserve their complete projected source outcome. -/
theorem effects_input (query : (EnvEffects n).Domain) (before : State n) :
    Prod.map id project <$> (effects query).run before =
      Prod.map id project <$> (effects query).run (project before) := by
  cases query with
  | inl coin =>
      change Prod.map id project <$> (PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _)).run
          (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before) = _
      rw [RegistrationNativeWorldView.sampled]
      change _ = Prod.map id project <$> (PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _)).run
        (PqxdhRecordLiftWorld.chargeEffect (.inl coin) (project before))
      rw [RegistrationNativeWorldView.sampled]
      rw [charge_input]
  | inr request =>
      change Prod.map id project <$> (capability request).run
          (PqxdhRecordLiftWorld.chargeEffect (.inr request) before) = _
      rw [capability_input, charge_input]
      exact (capability_input request
        (PqxdhRecordLiftWorld.chargeEffect (.inr request) (project before))).symm

end BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects.resolve_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects.resolve_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects.capability_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects.capability_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects.effects_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects.effects_input
