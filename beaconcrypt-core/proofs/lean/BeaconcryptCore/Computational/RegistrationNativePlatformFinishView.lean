-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower

/-! The corrected assigned-ID finish reads no erased native accounting input. Actual authentication, agreement, first-record opening, source byte copy and installation remain literal through every failed prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformFinishView
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeBeaconEnvView (Stable pure_stable bind_stable program_stable)
open RegistrationNativeBeaconEnvCallbacks
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {KemSK Auxiliary Value Platform ι : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem abort_pure (owner : Owner source) (value : Value) :
    Stable (RegistrationNativeBeaconFrontend.abort owner *> pure value : M n KemSK source Auxiliary Value) := by
  simp only [seqRight_eq_bind]
  exact bind_stable _ _ (abort_stable owner) (fun _ => pure_stable value)

private theorem install (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    Stable (RegistrationNativePlatformBeaconFinish.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_stable _ _ (effect_stable _)
  intro installed
  cases installed with
  | false => exact abort_pure owner _
  | true => exact bind_stable _ _ (phase_stable index _) (fun _ => pure_stable _)

private theorem after (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) :
    Stable (RegistrationNativePlatformBeaconFinish.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime accepted) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_stable _ _ (program_stable _ (agreement_stable setup owner oneTime) _)
  intro agreed
  cases agreed with
  | fail error | div => exact abort_pure owner _
  | ok effect =>
    cases effect
    all_goals first
      | exact abort_pure owner _
      | apply bind_stable _ _ (program_stable _ (record_stable setup wire) _)
        intro opened
        cases opened with
        | fail error | div => exact abort_pure owner _
        | ok answer => cases answer with
          | Err prior => exact abort_pure owner _
          | Ok completed => exact install index owner completed

/-- Actual corrected source finish is independent of the separate local record-kind ledger, including assigned-ID installation. -/
theorem finish_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Stable (RegistrationNativePlatformBeaconFinish.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  unfold RegistrationNativePlatformBeaconFinish.finish RegistrationNativePlatformBeaconFinish.finishWith
  apply bind_stable _ _ RegistrationNativeBeaconEnvView.get_stable
  intro owners
  cases owners[index]? with
  | none => exact pure_stable _
  | some owner =>
    dsimp only
    cases owner.phase with
    | fresh | freshWithCoins oneTime | established completed | aborted prior => exact pure_stable _
    | initSent pending oneTime =>
      dsimp only
      cases pending.aborted_state with
      | fail error | div => exact pure_stable _
      | ok aborted =>
        apply bind_stable _ _ (phase_stable index _)
        intro _changed
        apply bind_stable _ _ (program_stable _ (authentication_stable setup) _)
        intro authenticated
        cases authenticated with
        | fail error | div => exact abort_pure owner _
        | ok answer => cases answer with
          | Err prior => exact abort_pure owner _
          | Ok accepted => exact after setup wire index owner oneTime accepted

private def openState (before : RegistrationNativeExperiment.State n KemSK source) : RegistrationNativeMldsaShared.Local n KemSK source :=
  (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))
private theorem open_project (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativeMldsaCountLower.localProject (openState before) = openState (RegistrationNativeMldsaMainView.project before) := rfl
private theorem close_project (before : RegistrationNativeMldsaShared.Local n KemSK source) :
    RegistrationNativeMldsaShared.close (RegistrationNativeMldsaCountLower.localProject before) =
      RegistrationNativeMldsaMainView.project (RegistrationNativeMldsaShared.close before) := rfl
private theorem beacon_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$>
        (RegistrationNativeMldsaShared.lower setup checks representation created work).run (openState before) := by
  simp only [RegistrationNativeExperiment.beacon, RegistrationNativeMldsaShared.lower, RegistrationNativeMldsaShared.close,
    openState, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq]

/-- The complete actual native lift of corrected finish ignores all omitted accounting coordinates while preserving its exact protocol state. -/
theorem native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativeKemCounterIndependence.Stable RegistrationNativeMldsaMainView.project
      (RegistrationNativeExperiment.beacon (n := n) setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)) := by
  intro before
  have same := congrArg (fun action => Prod.map id RegistrationNativeMldsaShared.close <$> action)
    (RegistrationNativeMldsaCountLower.lower_stable setup checks representation created _ (finish_stable setup wire index packet)
      (openState before))
  simp only [Functor.map_map, Prod.map, id_eq, close_project, open_project] at same
  simp only [beacon_source, Functor.map_map, Prod.map, id_eq]
  exact same

/-- Actual corrected shared-state finish has both free count laws, with complete external platform state retained. -/
theorem count (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativePlatformMldsaCountRules.Correct (source := source) (Platform := Platform) RegistrationNativeMldsaMainView.project
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeExperiment.beacon (n := n) setup checks representation created
            (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)))) :=
  RegistrationNativePlatformMldsaCountRules.native _ _ (native setup checks representation created wire index packet)
end BeaconcryptCore.Computational.RegistrationNativePlatformFinishView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishView.finish_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishView.finish_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishView.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishView.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishView.count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishView.count
