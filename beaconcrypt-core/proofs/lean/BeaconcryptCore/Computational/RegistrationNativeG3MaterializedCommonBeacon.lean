-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon

/-! The actual canonical Beacon known stage has its public material44/reference representation when the private table materializes hidden references as known kernels. All native opening, admission and installation failures retain their exact replies and complete receipt/World poststate. No cached-seed, unused-role or successful-installation condition is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon
open PqxdhRecordLiftInterface (Slot)
open RegistrationNativeG3Common (State publication)
open RegistrationNativeG3MaterializedCommon (effect handler)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {Value : Type}

private theorem raw_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    simulateQ (RegistrationNativeG3Common.handler (n := n) source writer sign)
      (simulateQ RegistrationNativePairedBeaconService.rawLift work) =
      simulateQ (publication source writer sign) (simulateQ RegistrationBoundPublication.rawLift work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1

private theorem raw_lift (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    simulateQ (handler source writer sign seeds) (simulateQ RegistrationNativePairedBeaconService.rawLift work) =
      simulateQ (publication source writer sign) (simulateQ RegistrationBoundPublication.rawLift work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1

/-- Every supported actual Beacon completion has the same canonical native installation in its public fixed-table representation. -/
theorem after_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n)
    (result : RustM RegistrationBeaconRecordExecutor.Result)
    (supported : result ∈ support (RegistrationNativePairedBeaconService.program source descriptor
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))) (before : State n) :
    (simulateQ RegistrationNativeG3Common.effect (RegistrationNativePairedBeaconService.after owner sender
      (fun value => .known value.kernel) result)).run before =
      (simulateQ (effect seeds) (RegistrationNativePairedBeaconService.after owner sender
        (fun _ => .hidden slot) result)).run before := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result with
    | Err aborted => rfl
    | Ok completed =>
        have canonical := RegistrationNativeG3BeaconInsertion.program_kernel source descriptor material (seeds slot) completed supported
        simp only [RegistrationNativePairedBeaconService.after]
        rw [canonical]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
        rfl

/-- The complete actual known Beacon stage equals its private hidden-reference stage under fixed canonical materialization, retaining every shared state field. -/
theorem private_stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n) (before : State n) :
    (simulateQ (RegistrationNativeG3Common.handler source writer sign)
      (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor
        (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before =
      (simulateQ (handler source writer sign seeds)
        (RegistrationNativePairedBeaconService.privateHiddenStage source owner sender slot descriptor
          (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before := by
  simp only [RegistrationNativePairedBeaconService.knownStage, RegistrationNativePairedBeaconService.privateHiddenStage,
    simulateQ_bind, raw_source, raw_lift, StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reached supported
  have original : reached.1 ∈ support (RegistrationNativePairedBeaconService.program source descriptor
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot))) := by
    apply support_simulateQ_run'_subset (publication source writer sign ∘ₛ RegistrationBoundPublication.rawLift) _ before
    rw [StateT.run'_eq, support_map, QueryImpl.simulateQ_compose]
    exact ⟨reached, supported, rfl⟩
  simpa only [RegistrationNativeG3Common.effect_lift, RegistrationNativeG3MaterializedCommon.effect_lift] using
    after_program source owner sender slot descriptor material seeds reached.1 original reached.2

/-- The actual known108 Beacon stage materializes the public44/reference stage without any hidden-cache or unused-role premise. -/
theorem stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n) (before : State n) :
    (simulateQ (RegistrationNativeG3Common.handler source writer sign)
      (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor
        (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before =
      (simulateQ (handler source writer sign seeds)
        (RegistrationNativePairedBeaconService.hiddenStage source owner sender descriptor ⟨slot, material⟩)).run before := by
  rw [← RegistrationNativePairedBeaconService.hidden_split source owner sender slot descriptor material (seeds slot)]
  exact private_stage source writer sign owner sender slot descriptor material seeds before

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon.after_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon.after_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon.private_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon.private_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonBeacon.stage
