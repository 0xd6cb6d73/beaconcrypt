-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon
/-! The corrected full Beacon owner/environment continuation retains exact source KDF markers and assigned-ID installation under known versus private fixed-seed interpretation. The comparison follows the actual public paired branch and literal phase settlement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconProgram
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativePlatformMaterializedBeacon (realize)
variable {n : Nat} {Auxiliary : Type} {mlSource : RegistrationNativeMldsa.Source}

private theorem after_free (owner current : SelectedOwner mlSource) (seeds : Seeds n)
    (result : RustM RegistrationNativePairedBeaconService.Result) (env : EnvState Auxiliary) :
    simulateQ (realize seeds)
      (((RegistrationNativePlatformBeaconMaterialFrontend.after
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner result).run current).run env) =
      ((RegistrationNativePlatformBeaconMaterialFrontend.after
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner result).run current).run env := by
  cases result with
  | fail error | div =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,
        RegistrationNativePlatformBeaconMaterialFrontend.abort, seqRight_eq_bind,
        StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift, simulateQ_map, simulateQ_spec_query, realize]
  | ok result => cases result with
    | Err aborted =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,
        RegistrationNativePlatformBeaconMaterialFrontend.abort, seqRight_eq_bind,
        StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift, simulateQ_map, simulateQ_spec_query, realize]
    | Ok completed =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, StateT.run_bind,
        StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]

/-- The actual complete first-record program preserves the full selected owner and local environment while materializing only the private installed kernel. -/
theorem program_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (seeds : Seeds n) (env : EnvState Auxiliary) :
    ((RegistrationNativePlatformBeaconMaterialFrontend.program source writer owner ready
      (RegistrationNativeG3MaterializedFrontend.materialize seeds choice)).run current).run env =
      simulateQ (realize seeds)
        (((RegistrationNativePlatformBeaconMaterialFrontend.program source writer owner ready choice).run current).run env) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.program
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals simp only [valid, ite_true, ite_false, StateT.run_bind, StateT.run_lift,
    RegistrationBeaconMaterialRead.charge, StateT.run_modify, pure_bind, simulateQ_bind,
    bind_pure_comp, bind_map_left]
  all_goals simp only [QueryImpl.ofLift]
  all_goals rw [RegistrationNativePlatformMaterializedBeacon.branch (Auxiliary := Auxiliary) source writer owner.worldOwner ready.descriptor choice seeds]
  all_goals apply bind_congr
  all_goals rintro ⟨result, reached⟩
  all_goals exact (after_free owner current seeds result reached).symm
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconProgram.program_source
