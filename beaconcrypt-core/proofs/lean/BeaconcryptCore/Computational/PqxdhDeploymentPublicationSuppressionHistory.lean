-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory

/-! Once a selected one-time message was absent at its first suppressed occurrence, the complete modified source execution never signs it. Every other actual source operation and every optional reply remain in the adaptive run. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh
open PqxdhDeploymentPublicationSuppression (Target Selection after trace)
open PqxdhDeploymentPublicationSuppressionFreshness (Fresh next_fixed after_fresh)
open PqxdhDeploymentPublicationSuppressionSchedule (State bundle source onSource)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

def Armed (target : Target) (state : State KemSK) : Prop :=
  state.2.pending = none ∧ state.2.target = some target ∧ Fresh target state.1.pool.1

/-- Every later local call keeps the selected public capability fixed. -/
theorem after_selection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection) (armed : selection.pending = none) :
    (after setup codec index owner generated pool selection).2 = selection := by
  simp only [after, next_fixed selection _ armed]
  split <;> rfl

/-- The actual Fresh one-time draw and every local failure branch preserve the armed message's absence. -/
theorem trace_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (selection : Selection) (target : Target)
    (armed : selection.pending = none) (captured : selection.target = some target) (fresh : Fresh target pool)
    (result : PqxdhDeploymentPublicationSuppression.NativeResult KemSK × Selection)
    (supported : result ∈ support (trace setup codec index owner pool selection)) :
    Fresh target result.1.2 ∧ result.2 = selection := by
  cases phase : owner.beacon.phase <;>
    simp only [trace, phase, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case fresh =>
    obtain ⟨scalar, _, rfl⟩ := supported
    exact ⟨after_fresh setup codec index owner (some scalar) pool selection target armed captured fresh,
      after_selection setup codec index owner (some scalar) pool selection armed⟩
  all_goals subst result
  all_goals exact ⟨after_fresh setup codec index owner none pool selection target armed captured fresh,
    after_selection setup codec index owner none pool selection armed⟩

/-- All existing, missing and inactive owner slots retain the selected message's freshness. -/
theorem bundle_armed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (target : Target) (armed : Armed target state)
    (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) : Armed target result.2 := by
  cases found : state.1.owners[address]? <;>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case none =>
    subst result
    simpa only [Armed, next_fixed state.2 none armed.1] using armed
  case some entry =>
    obtain ⟨reached, member, rfl⟩ := supported
    obtain ⟨fresh, selection⟩ := trace_fresh setup codec entry.identityIndex entry.owner state.1.pool.1 state.2 target
      armed.1 armed.2.1 armed.2.2 reached member
    exact ⟨by simpa only [selection] using armed.1, by simpa only [selection] using armed.2.1, fresh⟩

/-- Outside a bundle, the complete modified source callback is the original indexed source callback with unchanged selection bookkeeping. -/
theorem nonbundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notBundle : ∀ address, query ≠ .inl (.inr (.bundle address))) :
    source setup codec checks seed index query =
      onSource (PqxdhRegistrationJointServerSchedule.source setup codec checks seed index query) := by
  rcases query with (coin | request) | read
  · rfl
  · cases request
    case bundle address => exact False.elim (notBundle address rfl)
    all_goals rfl
  · rfl

/-- Every real modified source command preserves the fixed target and its absent signing message. Non-bundle operations keep the literal signing history for that slot. -/
theorem query_armed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (target : Target) (armed : Armed target state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((source setup codec checks seed index query).run state)) : Armed target result.2 := by
  by_cases bundled : ∃ address, query = .inl (.inr (.bundle address))
  · obtain ⟨address, rfl⟩ := bundled
    exact bundle_armed setup codec address state target armed result supported
  · have notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)) :=
      fun address equal => bundled ⟨address, equal⟩
    rw [nonbundle_source setup codec checks seed index query notBundle] at supported
    simp only [onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reached, member, rfl⟩ := supported
    refine ⟨armed.1, armed.2.1, ?_⟩
    have previous := armed.2.2
    unfold Fresh at previous ⊢
    rw [PqxdhDeploymentPublicationAuditHistory.source_nonbundle_messages setup codec checks seed index query notBundle
      state.1 reached member target.identityIndex]
    exact previous

/-- The whole adaptive modified source suffix preserves the genuinely unqueried one-time message and its captured capability. -/
theorem program_armed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (target : Target) (armed : Armed target state) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (source setup codec checks seed index) program).run state)) :
    Armed target result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (Armed target)
    (fun query current held reached member => query_armed setup codec checks seed index query current target held
      reached member) program state armed result supported

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.after_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.after_selection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.trace_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.trace_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.bundle_armed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.bundle_armed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.nonbundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.nonbundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.query_armed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.query_armed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.program_armed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory.program_armed
