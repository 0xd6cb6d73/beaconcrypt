-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommon

/-! A fixed private seed table gives an exact source anchor for the public native Server continuation. Its hidden installation reference is interpreted as the canonical known kernel of that table entry, so the full chronological receipts and World equal the actual known-kernel stage. No cached-seed, unused-role, audit or projected-state condition enters this representation equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer
open PqxdhRecordLiftInterface (Slot)
open RegistrationNativeG3Common (State)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {Encoded : Type}

/-- The actual native peer insertion uses the same assigned ID, populated binding, finish decision and concrete kernel under fixed-table materialization. -/
theorem install (control : pqxdh.ServerState) (slot : Slot n)
    (published : registration.PublishedServerResponse Encoded) (seeds : Seeds n)
    (canonical : published.kernel = PqxdhRecordLiftWorld.kernel .server (seeds slot)) (before : State n) :
    (simulateQ RegistrationNativeG3Common.effect
      (RegistrationNativePairedServerService.knownInstall control published)).run before =
      (simulateQ (RegistrationNativeG3MaterializedCommon.effect seeds)
        (RegistrationHiddenInstall.install control slot published)).run before := by
  obtain ⟨result, prepared, retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases result with
  | Err previous =>
      simp only [RegistrationNativePairedServerService.knownInstall, RegistrationHiddenInstall.install, prepared]
      rfl
  | Ok pending =>
      have kernel := retained.2.2.2.1
      rw [RegistrationNativePairedServerService.knownInstall_native control published pending prepared,
        RegistrationHiddenInstall.install_native control slot published pending prepared, kernel, canonical]
      rfl

/-- Publication support derives the canonical consumed source kernel, with every signing, encoding and native insertion failure retained. -/
theorem after_publication (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (supported : published ∈ support (RegistrationBoundPublication.program encode initial
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))) (before : State n) :
    (simulateQ RegistrationNativeG3Common.effect
      (RegistrationNativePairedServerService.knownAfter control published)).run before =
      (simulateQ (RegistrationNativeG3MaterializedCommon.effect seeds)
        (RegistrationHiddenInstall.after control slot published)).run before := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok published =>
        exact install control slot published seeds
          (RegistrationBoundPublication.published_kernel encode initial material (seeds slot) published supported) before

/-- The actual complete known Server stage equals its full-output hidden-reference stage under the fixed-table materializing interpreter, including exact receipts and all World fields. -/
theorem private_stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n) (before : State n) :
    (simulateQ (RegistrationNativeG3Common.handler source writer sign)
      (RegistrationNativePairedServerService.knownStage encode control initial
        (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before =
      (simulateQ (RegistrationNativeG3MaterializedCommon.handler source writer sign seeds)
        (RegistrationHiddenInstall.stage encode control slot initial
          (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before := by
  simp only [RegistrationNativePairedServerService.knownStage, RegistrationHiddenInstall.stage, simulateQ_bind,
    RegistrationNativeG3Common.publication_lift, RegistrationNativeG3MaterializedCommon.publication_lift, StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reached supported
  have actual : reached.1 ∈ support (RegistrationBoundPublication.program encode initial
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot))) := by
    apply support_simulateQ_run'_subset (RegistrationNativeG3Common.publication source writer sign) _ before
    rw [StateT.run'_eq, support_map]
    exact ⟨reached, supported, rfl⟩
  rw [RegistrationNativeG3Common.effect_lift, RegistrationNativeG3MaterializedCommon.effect_lift]
  exact after_publication encode control slot initial material seeds reached.1 actual reached.2

/-- The public Server continuation receives only material44 and its slot; interpreting that slot at the fixed private seed gives exactly the actual full native stage, with no cache/use premise. -/
theorem stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n) (before : State n) :
    (simulateQ (RegistrationNativeG3Common.handler source writer sign)
      (RegistrationNativePairedServerService.knownStage encode control initial
        (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before =
      (simulateQ (RegistrationNativeG3MaterializedCommon.handler source writer sign seeds)
        (RegistrationNativePairedServerService.hiddenStage encode control initial ⟨slot, material⟩)).run before := by
  have actual := private_stage source writer sign encode control slot initial material seeds before
  have publicStage : RegistrationHiddenInstall.stage encode control slot initial
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)) =
      RegistrationNativePairedServerService.hiddenStage encode control initial ⟨slot, material⟩ := by
    simpa only [RegistrationNativePairedServerService.hiddenStage] using
      RegistrationHiddenInstall.stage_split encode control slot initial material (seeds slot)
  rw [publicStage] at actual
  exact actual

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.install
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.after_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.after_publication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.private_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.private_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer.stage
