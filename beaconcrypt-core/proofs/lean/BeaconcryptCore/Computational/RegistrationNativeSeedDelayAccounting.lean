-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayWorld
import BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform

/-! The seed-delay interpreter is linked to the original counted World by a derived query and adaptive-program projection. Lazy lookup/draw counts never select a branch or influence a reply; uniform counts have the existing actual-source nonread law. This removes only accounting, retaining the complete private seed cache and every semantic field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting
open PqxdhRecordLiftWorld (State resolve installServer installBeacon capability effects)
open PqxdhRecordLiftInterface (Role KernelRef CapabilitySpec EnvEffects WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSeedDelayCore (mask)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def counts (before : State n) : State n :=
  { before with seeds := (before.seeds.1, ⟨0, 0⟩) }

/-- Actual hit/miss selection reads the persistent cache, never its logical accounting. -/
theorem resolve_counts (role : Role) (ref : KernelRef n) (before : State n) :
    Prod.map id counts <$> (resolve role ref).run before =
      Prod.map id counts <$> (resolve role ref).run (counts before) := by
  cases ref with
  | known kernel => simp only [resolve, StateT.run_pure, map_pure, counts, Prod.map_def, id_eq]
  | hidden slot =>
      cases found : before.seeds.1 slot with
      | none =>
          rw [PqxdhRecordLiftWorld.resolve_miss role slot before found,
            PqxdhRecordLiftWorld.resolve_miss role slot (counts before) found]
          simp only [Functor.map_map, Prod.map_def, id_eq, counts]
      | some seed =>
          rw [PqxdhRecordLiftWorld.resolve_hit role slot before seed found,
            PqxdhRecordLiftWorld.resolve_hit role slot (counts before) seed found]
          simp only [map_pure, Prod.map_def, id_eq, counts]

private theorem server_counts (keyId : U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (ref : KernelRef n) (before : State n) :
    Prod.map id counts <$> (installServer keyId binding ref).run before =
      Prod.map id counts <$> (installServer keyId binding ref).run (counts before) := by
  cases server : before.server with
  | none => simp only [installServer, StateT.run, counts, server, map_pure, Prod.map_def, id_eq]
  | some owner =>
      by_cases admitted : owner.records.server.peers keyId = none ∧ PqxdhRecordLiftWorld.Unused before .server ref
      · have law := congrArg (fun work => (fun (result : ConcreteRatchetKernel × State n) => (true,
            { PqxdhRecordLiftWorld.markUsed result.2 .server ref with server := some { owner with records :=
                { owner.records with server := { owner.records.server with peers := Function.update owner.records.server.peers keyId (some ⟨binding.identity, result.1, binding.associatedArray owner.records.server.identity⟩) } } } })) <$> work)
          (resolve_counts .server ref before)
        simp only [installServer, StateT.run, counts, server, PqxdhRecordLiftWorld.Unused] at admitted ⊢
        simp only [admitted, and_self, ite_true, bind_pure_comp]
        cases ref <;> simp only [Functor.map_map, Prod.map_def, id_eq, counts,
          PqxdhRecordLiftWorld.markUsed, server, StateT.run] at law ⊢ <;>
          convert law using 1
      · simp only [installServer, StateT.run, counts, server, PqxdhRecordLiftWorld.Unused] at admitted ⊢
        simp only [admitted, ite_false, map_pure, Prod.map_def, id_eq]
        simp only [counts, server]

private theorem beacon_counts (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (ref : KernelRef n) (before : State n) :
    Prod.map id counts <$> (installBeacon owner shell ref).run before =
      Prod.map id counts <$> (installBeacon owner shell ref).run (counts before) := by
  by_cases admitted : PqxdhRecordLiftWorld.BeaconReady before owner ∧ PqxdhRecordLiftWorld.Unused before .beacon ref
  · have law := congrArg (fun work => (fun (result : ConcreteRatchetKernel × State n) => (true,
        { PqxdhRecordLiftWorld.markUsed result.2 .beacon ref with owners := before.owners.set owner (.established shell result.1) })) <$> work)
      (resolve_counts .beacon ref before)
    simp only [installBeacon, StateT.run, counts, PqxdhRecordLiftWorld.BeaconReady,
      PqxdhRecordLiftWorld.Unused] at admitted ⊢
    simp only [admitted, and_self, ite_true, bind_pure_comp]
    cases ref <;> simp only [Functor.map_map, Prod.map_def, id_eq, counts,
      PqxdhRecordLiftWorld.markUsed, StateT.run] at law ⊢ <;>
      convert law using 1
  · simp only [installBeacon, StateT.run, counts, PqxdhRecordLiftWorld.BeaconReady,
      PqxdhRecordLiftWorld.Unused] at admitted ⊢
    simp only [admitted, ite_false, map_pure, Prod.map_def, id_eq, counts]

/-- Every actual capability ignores seed accounting, including current phase/role refusal and optional hash paths. -/
theorem capability_counts (query : (CapabilitySpec n).Domain) (before : State n) :
    Prod.map id counts <$> (capability query).run before =
      Prod.map id counts <$> (capability query).run (counts before) := by
  cases query with
  | peerPresent keyId | ownerPresent owner | appendOwner sender identity phase =>
      simp only [capability, StateT.run, map_pure, Prod.map_def, id_eq, counts]
  | advanceOwner owner phase =>
      cases found : before.owners[owner]? with
      | none => simp only [capability, StateT.run, counts, found, map_pure, Prod.map_def, id_eq]
      | some current =>
          cases current with
          | established shell kernel => simp only [capability, StateT.run, counts, found, map_pure, Prod.map_def, id_eq]
          | inactive previous =>
              by_cases legal : PqxdhRecordLiftWorld.LegalAdvance previous phase <;>
                simp only [capability, StateT.run, counts, found, legal, ite_true, ite_false,
                  map_pure, Prod.map_def, id_eq]
  | installServer keyId binding ref => exact server_counts keyId binding ref before
  | installBeacon owner shell ref => exact beacon_counts owner shell ref before
  | hash bytes =>
      simp only [capability, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp,
        Functor.map_map, Prod.map_def, id_eq, counts]

theorem effects_counts (query : (EnvEffects n).Domain) (before : State n) :
    Prod.map id counts <$> (effects query).run before =
      Prod.map id counts <$> (effects query).run (counts before) := by
  cases query with
  | inl coin =>
      simp only [effects, PqxdhRecordLiftWorld.sampled, PqxdhRecordLiftWorld.chargeEffect,
        StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, counts]
  | inr request => exact capability_counts request (PqxdhRecordLiftWorld.chargeEffect (.inr request) before)

/-- The full native World surface never reads logical seed lookup/draw counts. -/
theorem handler_counts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id counts <$> (PqxdhRecordLiftWorld.handler setup codec route query).run before =
      Prod.map id counts <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (counts before) := by
  cases query with
  | inl created =>
      cases found : before.server <;> simp only [PqxdhRecordLiftWorld.handler,
        PqxdhRecordLiftWorld.initializeServer, StateT.run, counts, found, map_pure, Prod.map_def, id_eq]
  | inr query => cases query with
    | inl effect => exact effects_counts effect before
    | inr record => cases record with
      | inl server => cases server with
        | inl query =>
            cases found : before.server <;> simp only [PqxdhRecordLiftWorld.handler,
              PqxdhRecordLiftWorld.serverStep, StateT.run, counts, found, map_pure, bind_pure_comp,
              Functor.map_map, Prod.map_def, id_eq, PqxdhRecordLiftWorld.produce]
        | inr raw =>
            cases found : before.server <;> simp only [PqxdhRecordLiftWorld.handler,
              PqxdhRecordLiftWorld.serverStep, StateT.run, counts, found, map_pure, bind_pure_comp,
              Functor.map_map, Prod.map_def, id_eq, PqxdhRecordLiftWorld.produce]
      | inr beacon =>
          rcases beacon with ⟨owner, query⟩
          cases query <;> cases found : before.owners[owner]? <;>
            simp only [PqxdhRecordLiftWorld.handler, PqxdhRecordLiftWorld.beaconStep, StateT.run,
              counts, found, map_pure, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq,
              PqxdhRecordLiftWorld.produce]

/-- The actual combined accounting projection is stable on the input of every native World query. -/
theorem handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id mask <$> (PqxdhRecordLiftWorld.handler setup codec route query).run before =
      Prod.map id mask <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (mask before) := by
  have uniform := congrArg (fun distribution => Prod.map id mask <$> distribution)
    (RegistrationNativeKemWorldRecordUniform.handler_input setup codec route query before)
  have logical := congrArg (fun distribution => Prod.map id mask <$> distribution)
    (handler_counts setup codec route query (RegistrationNativeKemWorldUniform.mask before))
  simp only [Functor.map_map, Prod.map_def, id_eq, mask, counts, RegistrationNativeKemWorldUniform.mask] at uniform logical ⊢
  exact uniform.trans logical

/-- Complete actual adaptive World execution projects to the normalized seed-delay interpreter, with the canonical seed cache and every semantic coordinate still literal. -/
theorem program_mask (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.map id mask <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before =
      (simulateQ (RegistrationNativeSeedDelayWorld.handler setup codec route) work).run (mask before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  change Prod.map id mask <$> (PqxdhRecordLiftWorld.handler setup codec route query).run current =
    Prod.map id mask <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (mask (mask current))
  rw [RegistrationNativeSeedDelayCore.mask_idempotent]
  exact handler_input setup codec route query current

end BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.resolve_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.resolve_counts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.capability_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.capability_counts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.effects_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.effects_counts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.handler_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.handler_counts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.program_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting.program_mask
