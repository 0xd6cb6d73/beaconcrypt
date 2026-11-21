-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer
import BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-! Fixed materialization preserves the actual chronological Server installation trace. The monitor records the original frontend effect before materializing its hidden reference; its attempt and successful-install updates therefore use the same actual descriptor on the known and hidden paths. Publication retains the same chronological receipts and the entire World. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon
open PqxdhRecordLiftInterface (Slot EnvEffects)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {Value Encoded : Type}

abbrev State (n : Nat) := RegistrationNativeG2Trace.State × RegistrationNativeG3Common.State n

def effectQuery (query : (EnvEffects n).Domain) : (RegistrationNativePublicFrontend.Spec n Unit).Domain :=
  .inl (.inr (.inl (.inr (.inr query))))

def onCommon (work : StateT (RegistrationNativeG3Common.State n) ProbComp Value) : StateT (State n) ProbComp Value := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$> work.run before.2

noncomputable def effect (full : Bool) (seeds : Seeds n) : QueryImpl (EnvEffects n) (StateT (State n) ProbComp) := fun query before =>
  (fun result => (result.1, (RegistrationNativeG2Trace.finish (effectQuery query) result.1
    (RegistrationNativeG2Trace.begin (effectQuery query) before.1), result.2))) <$>
      ((if full then RegistrationNativeG3Common.effect query else RegistrationNativeG3MaterializedCommon.effect seeds query).run before.2)

noncomputable def handler (full : Bool) (seeds : Seeds n)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePairedServerService.Common n) (StateT (State n) ProbComp)
  | .inl query => onCommon (RegistrationNativeG3Common.publication source writer sign query)
  | .inr query => effect full seeds query

theorem publication_lift (full : Bool) (seeds : Seeds n)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Value) :
    simulateQ (handler full seeds source writer sign) (simulateQ RegistrationHiddenInstall.publicationLift work) =
      simulateQ (fun query => onCommon (RegistrationNativeG3Common.publication source writer sign query)) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, RegistrationHiddenInstall.publicationLift, simulateQ_spec_query, handler]

theorem effect_lift (full : Bool) (seeds : Seeds n)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (EnvEffects n) Value) :
    simulateQ (handler full seeds source writer sign) (simulateQ RegistrationHiddenInstall.effectLift work) =
      simulateQ (effect full seeds) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, RegistrationHiddenInstall.effectLift, simulateQ_spec_query, handler]

/-- The two literal native insertions retain the same chronological attempt and success events, alongside all source state. -/
theorem install (control : pqxdh.ServerState) (slot : Slot n)
    (published : registration.PublishedServerResponse Encoded) (seeds : Seeds n)
    (canonical : published.kernel = PqxdhRecordLiftWorld.kernel .server (seeds slot)) (before : State n) :
    (simulateQ (effect true seeds) (RegistrationNativePairedServerService.knownInstall control published)).run before =
      (simulateQ (effect false seeds) (RegistrationHiddenInstall.install control slot published)).run before := by
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

theorem after_publication (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded))
    (supported : published ∈ support (RegistrationBoundPublication.program encode initial
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))) (before : State n) :
    (simulateQ (effect true seeds) (RegistrationNativePairedServerService.knownAfter control published)).run before =
      (simulateQ (effect false seeds) (RegistrationHiddenInstall.after control slot published)).run before := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok published =>
        exact install control slot published seeds
          (RegistrationBoundPublication.published_kernel encode initial material (seeds slot) published supported) before

theorem private_stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n) (before : State n) :
    (simulateQ (handler true seeds source writer sign)
      (RegistrationNativePairedServerService.knownStage encode control initial
        (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before =
      (simulateQ (handler false seeds source writer sign)
        (RegistrationHiddenInstall.stage encode control slot initial
          (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before := by
  simp only [RegistrationNativePairedServerService.knownStage, RegistrationHiddenInstall.stage, simulateQ_bind,
    publication_lift, StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reached supported
  have actual : reached.1 ∈ support (RegistrationBoundPublication.program encode initial
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot))) := by
    apply support_simulateQ_run'_subset (fun query => onCommon (RegistrationNativeG3Common.publication source writer sign query)) _ before
    rw [StateT.run'_eq, support_map]
    exact ⟨reached, supported, rfl⟩
  rw [effect_lift, effect_lift]
  exact after_publication encode control slot initial material seeds reached.1 actual reached.2

/-- The actual known and materialized hidden stages preserve the complete chronological trace, with arbitrary initial descriptor and events. -/
theorem stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n) (before : State n) :
    (simulateQ (handler true seeds source writer sign)
      (RegistrationNativePairedServerService.knownStage encode control initial
        (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot)))).run before =
      (simulateQ (handler false seeds source writer sign)
        (RegistrationNativePairedServerService.hiddenStage encode control initial ⟨slot, material⟩)).run before := by
  have actual := private_stage source writer sign encode control slot initial material seeds before
  rw [RegistrationHiddenInstall.stage_split] at actual
  exact actual

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.publication_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.publication_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.effect_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.effect_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.install

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.after_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.after_publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.private_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.private_stage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCommon.stage
