-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation
/-! Actual native bundle publication advances either fresh World slot and stores the reached pending capability with exact complete Native state. The update uses the current owner and retains its accumulated Ed signing history. The sole administrative attempt is charged explicitly. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundleTerminal
open RegistrationNativeBeaconFrontend (M Owner)
variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def Ready (world : PqxdhRecordLiftWorld.State n) (index : Nat) : Prop :=
  world.owners[index]? = some (.inactive .fresh) ∨ world.owners[index]? = some (.inactive .freshWithCoins)

def advancedWorld (index : Nat) (world : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  {PqxdhRecordLiftWorld.chargeEffect (.inr (.advanceOwner index .initSent)) world with
    owners := world.owners.set index (.inactive .initSent)}

theorem advance_effect (index : Nat) (world : PqxdhRecordLiftWorld.State n) (ready : Ready world index) :
    (PqxdhRecordLiftWorld.effects (.inr (.advanceOwner index .initSent))).run world = pure (true, advancedWorld index world) := by
  change (PqxdhRecordLiftWorld.capability (.advanceOwner index .initSent)).run
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.advanceOwner index .initSent)) world) = _
  rcases ready with fresh | supplied
  · simp only [PqxdhRecordLiftWorld.capability, StateT.run, PqxdhRecordLiftWorld.chargeEffect, fresh,
      PqxdhRecordLiftWorld.LegalAdvance, ite_true]
    rfl
  · simp only [PqxdhRecordLiftWorld.capability, StateT.run, PqxdhRecordLiftWorld.chargeEffect, supplied,
      PqxdhRecordLiftWorld.LegalAdvance, ite_true]
    rfl

theorem native_effect (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (before : Native) (ready : Ready before.server.world.world.1 index) :
    (RegistrationNativeExperiment.trusted setup checks representation created source (.inl (.inr (.advanceOwner index .initSent)))).run before =
      pure (true, {before with server := {before.server with world := {before.server.world with world :=
        (advancedWorld index before.server.world.world.1, before.server.world.world.2)}}}) := by
  simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server, StateT.run, Functor.map_map]
  change (fun result => (result.1, {before with server := {before.server with world := {before.server.world with world :=
    (result.2, before.server.world.world.2)}}})) <$>
      (PqxdhRecordLiftWorld.effects (.inr (.advanceOwner index .initSent))).run before.server.world.world.1 = _
  rw [advance_effect index _ ready, map_pure]

def after (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native) : Native :=
  {before with
    beacons := RegistrationNativeFinishTerminal.setPhase index (.initSent pending scalar) before.beacons
    server := {before.server with world := {before.server.world with world :=
      (advancedWorld owner.worldOwner before.server.world.world.1, before.server.world.world.2)}}}

def install (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8)) :
    M n KemSK source RegistrationServerRoleBackend.State (RustM (Option (alloc.vec.Vec U8))) := do
  RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending scalar)
  let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
  pure (.ok (some finished.encoded))

theorem install_native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8)) (before : Native)
    (ready : Ready before.server.world.world.1 owner.worldOwner) :
    (RegistrationNativeExperiment.beacon setup checks representation created (install index owner scalar finished)).run before =
      pure (.ok (some finished.encoded), after index owner finished.pending scalar before) := by
  rw [RegistrationNativeLocalStatePatch.beacon_run]
  simp only [install, RegistrationNativeBeaconFrontend.updatePhase, RegistrationNativeBeaconFrontend.effect,
    StateT.run_bind, StateT.run_modify, StateT.run_lift, StateT.run_map, bind_pure_comp, pure_bind,
    Functor.map_map, simulateQ_map, simulateQ_spec_query]
  rw [native_effect setup checks representation created owner.worldOwner before ready, map_pure]
  rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m]
theorem install_interpret (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8)) (before : Native)
    (ready : Ready before.server.world.world.1 owner.worldOwner) :
    (RegistrationNativePlatformFrontend.interpret
      (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (install index owner scalar finished))).run before =
      pure (.ok (some finished.encoded), after index owner finished.pending scalar before) := by
  rw [RegistrationNativeBundleInterpretation.legacy]
  change simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created (install index owner scalar finished)).run before) = _
  rw [install_native setup checks representation created index owner scalar finished before ready, simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativeBundleTerminal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.advance_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.advance_effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.native_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.native_effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.install_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.install_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.install_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleTerminal.install_interpret
