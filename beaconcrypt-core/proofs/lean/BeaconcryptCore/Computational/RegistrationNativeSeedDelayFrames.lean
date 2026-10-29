-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore

/-! Actual World constructors, primitives, record routing and non-installation administration do not inspect the seed cache. These exact frame equations retain the cache's independent value while preserving the complete native poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State SeedSpec)
open RegistrationNativeSeedDelayCore (lens)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

theorem initialize_frame (created : PqxdhLiveServerConstruction.Created Unit)
    (before : State n) (cache : (SeedSpec n).QueryCache) :
    (PqxdhRecordLiftWorld.initializeServer created).run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$> (PqxdhRecordLiftWorld.initializeServer created).run before := by
  cases found : before.server <;>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, lens, found, map_pure, Prod.map_def, id_eq]

theorem server_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (before : State n) (cache : (SeedSpec n).QueryCache) :
    (PqxdhRecordLiftWorld.serverStep setup codec route query).run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$>
        (PqxdhRecordLiftWorld.serverStep setup codec route query).run before := by
  cases found : before.server with
  | none => cases query <;>
      simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, lens, found, map_pure, Prod.map_def, id_eq]
  | some server =>
      simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, lens, found, bind_pure_comp,
        Functor.map_map, Prod.map_def, id_eq, PqxdhRecordLiftWorld.produce]

theorem beacon_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : State n) (cache : (SeedSpec n).QueryCache) :
    (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$>
        (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run before := by
  cases found : before.owners[owner]? <;>
    simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, lens, found, map_pure, bind_pure_comp,
      Functor.map_map, Prod.map_def, id_eq, PqxdhRecordLiftWorld.produce]

def ReadsSeed : (PqxdhRecordLiftInterface.CapabilitySpec n).Domain → Prop
  | .installServer _ _ (.hidden _) | .installBeacon _ _ (.hidden _) => True
  | _ => False

/-- Every actual capability outside hidden resolution frames the seed cache, including all refused branches and known-kernel installations. -/
theorem capability_frame (query : (PqxdhRecordLiftInterface.CapabilitySpec n).Domain) (quiet : ¬ReadsSeed query)
    (before : State n) (cache : (SeedSpec n).QueryCache) :
    (PqxdhRecordLiftWorld.capability query).run (lens.set before cache) =
      Prod.map id (fun after => lens.set after cache) <$> (PqxdhRecordLiftWorld.capability query).run before := by
  cases query with
  | peerPresent keyId => simp only [PqxdhRecordLiftWorld.capability, StateT.run, lens, map_pure, Prod.map_def, id_eq]
  | ownerPresent owner => simp only [PqxdhRecordLiftWorld.capability, StateT.run, lens, map_pure, Prod.map_def, id_eq]
  | appendOwner identity keyId phase => simp only [PqxdhRecordLiftWorld.capability, StateT.run, lens, map_pure, Prod.map_def, id_eq]
  | advanceOwner owner phase =>
      cases found : before.owners[owner]? with
      | none => simp only [PqxdhRecordLiftWorld.capability, StateT.run, lens, found, map_pure, Prod.map_def, id_eq]
      | some current =>
          cases current <;>
            simp only [PqxdhRecordLiftWorld.capability, StateT.run, lens, found, map_pure, Prod.map_def, id_eq]
          all_goals split <;> simp only [map_pure]
  | installServer keyId binding ref =>
      cases ref with
      | hidden slot => exact False.elim (quiet trivial)
      | known kernel =>
          cases found : before.server with
          | none => simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer, StateT.run,
              lens, found, map_pure, Prod.map_def, id_eq]
          | some server =>
              simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer, StateT.run, lens, found,
                PqxdhRecordLiftWorld.Unused, and_true]
              split <;> simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed,
                state_pure_apply, pure_bind, map_pure, Prod.map_def, id_eq]
              all_goals simp only [found]
  | installBeacon owner shell ref =>
      cases ref with
      | hidden slot => exact False.elim (quiet trivial)
      | known kernel =>
          simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installBeacon, StateT.run, lens,
            PqxdhRecordLiftWorld.Unused, and_true, PqxdhRecordLiftWorld.BeaconReady]
          split <;> simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.markUsed,
            state_pure_apply, pure_bind, map_pure, Prod.map_def, id_eq]
  | hash bytes =>
      simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled, StateT.run, lens,
        bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]

end BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.initialize_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.initialize_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.server_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.server_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.beacon_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.beacon_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.capability_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames.capability_frame
