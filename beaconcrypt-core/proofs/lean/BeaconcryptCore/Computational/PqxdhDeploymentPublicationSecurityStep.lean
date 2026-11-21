-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts

/-! Every retained real source callback has the same public reply and a concretely related full modified successor. The real failure branch supplies physical rollback; the selected first-call absence and the actual suppressed-query invariant supply ordinary signing freshness. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentPublicationSuppression (Selection Target)
open PqxdhDeploymentPublicationSuppressionTrace (Audit)
open PqxdhDeploymentPublicationSelectionFacts (targetAt fromAudit)
open PqxdhDeploymentPublicationHistoryRebase (replaceHistory rebase)
open PqxdhDeploymentPublicationSuppressionFreshness (Fresh)
open PqxdhDeploymentPublicationSuppressionHistory (Armed)
open PqxdhDeploymentPublicationAuditBounds (Valid)
open PqxdhDeploymentPublicationSecurityTransport (queryTransport bundleTransport)
open PqxdhDeploymentPublicationSecurityCoupling
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

theorem allowed_bundle (ordinal address : Nat) (before : RealState KemSK)
    (outcome : Option Pqxdh.Bytes × RealState KemSK) :
    allowed ordinal (.inl (.inr (.bundle address))) before outcome = true ↔
      (((fromAudit ordinal before.2).next (targetAt outcome.2.2.occurrences before.2.nextBundle)).blocks
        (targetAt outcome.2.2.occurrences before.2.nextBundle) = true → outcome.1 = none) ∧
      (∀ target, before.2.nextBundle = ordinal →
        targetAt outcome.2.2.occurrences before.2.nextBundle = some target → Fresh target before.1.pool.1) := by
  classical
  simp only [allowed, Bool.and_eq_true, decide_eq_true_eq]

theorem bundle_next (before : RealState KemSK)
    (replacement : PqxdhDeploymentPublicationHistoryRebase.History) (selection : Selection)
    (outcome : Option Pqxdh.Bytes × RealState KemSK) :
    (bundleTransport before replacement selection outcome).2.2 =
      selection.next (targetAt outcome.2.2.occurrences before.2.nextBundle) := by
  unfold bundleTransport
  dsimp only
  split <;> rfl

/-- Every retained real branch has exactly the modified reply and complete physical successor. -/
theorem reply_physical (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat) (query : (Spec KemSK).Domain)
    (real : RealState KemSK) (modified : ModifiedState KemSK) (related : Related ordinal real modified)
    (outcome : (Spec KemSK).Range query × RealState KemSK)
    (supported : outcome ∈ support
      ((PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query).run real))
    (admitted : allowed ordinal query real outcome = true) :
    outcome.1 = (transport query real modified outcome).1 ∧
      Physical outcome.2.1 (transport query real modified outcome).2.1 := by
  by_cases bundled : ∃ address, query = .inl (.inr (.bundle address))
  · obtain ⟨address, rfl⟩ := bundled
    obtain ⟨failed, _⟩ := (allowed_bundle ordinal address real outcome).mp admitted
    simp only [transport, queryTransport, bundleTransport, related.2.1]
    split
    · rename_i blocked
      have failure := failed blocked
      have rolled := PqxdhDeploymentPublicationSecurityStepFacts.bundle_failure_rollback
        setup codec address real outcome supported failure
      exact ⟨failure, by simpa only [Physical, replaceHistory] using rolled⟩
    · exact ⟨rfl, rfl⟩
  · have notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)) :=
      fun address equal => bundled ⟨address, equal⟩
    simp only [transport, PqxdhDeploymentPublicationSecurityTransport.queryTransport_nonbundle query notBundle]
    exact ⟨True.intro, rfl⟩

/-- Until a target is captured, the original and modified executions have identical full native states. -/
theorem uncaptured_equal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat) (query : (Spec KemSK).Domain)
    (real : RealState KemSK) (modified : ModifiedState KemSK) (related : Related ordinal real modified)
    (outcome : (Spec KemSK).Range query × RealState KemSK)
    (supported : outcome ∈ support
      ((PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query).run real))
    (absent : modified.2.target = none)
    (uncaptured : (transport query real modified outcome).2.2.target = none) :
    (transport query real modified outcome).2.1 = outcome.2.1 := by
  have sameNative := related.2.2.2.1 absent
  have own := PqxdhDeploymentPublicationHistoryRebase.source_query_rebase_self setup codec checks seed index query real.1
    (outcome.1, outcome.2.1) (native_supported setup codec checks seed index query real outcome supported)
  by_cases bundled : ∃ address, query = .inl (.inr (.bundle address))
  · obtain ⟨address, rfl⟩ := bundled
    have nextAbsent : (modified.2.next (targetAt outcome.2.2.occurrences real.2.nextBundle)).target = none := by
      simpa only [transport, queryTransport, bundle_next] using uncaptured
    have notBlocked : (modified.2.next (targetAt outcome.2.2.occurrences real.2.nextBundle)).blocks
        (targetAt outcome.2.2.occurrences real.2.nextBundle) = false := by
      cases prepared : targetAt outcome.2.2.occurrences real.2.nextBundle with
      | none => rfl
      | some target =>
          rw [prepared] at nextAbsent
          simp only [Selection.blocks, nextAbsent, reduceBEq]
    simpa only [transport, queryTransport, bundleTransport, notBlocked, Bool.false_eq_true, ite_false,
      sameNative] using own
  · have notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)) :=
      fun address equal => bundled ⟨address, equal⟩
    simpa only [transport, PqxdhDeploymentPublicationSecurityTransport.queryTransport_nonbundle query notBundle,
      sameNative] using own

/-- At the selected first prepared call, the literal suppressed operation keeps the old state and its actually absent one-time message. -/
theorem captured_armed (ordinal : Nat) (query : (Spec KemSK).Domain)
    (real : RealState KemSK) (modified : ModifiedState KemSK) (related : Related ordinal real modified)
    (outcome : (Spec KemSK).Range query × RealState KemSK)
    (admitted : allowed ordinal query real outcome = true)
    (absent : modified.2.target = none) (target : Target)
    (captured : (transport query real modified outcome).2.2.target = some target) :
    Armed target (transport query real modified outcome).2 := by
  have sameNative := related.2.2.2.1 absent
  by_cases bundled : ∃ address, query = .inl (.inr (.bundle address))
  · obtain ⟨address, rfl⟩ := bundled
    have nextCaptured : (modified.2.next (targetAt outcome.2.2.occurrences real.2.nextBundle)).target = some target := by
      simpa only [transport, queryTransport, bundle_next] using captured
    obtain ⟨selected, prepared, pending, blocked⟩ := capture modified.2 _ target absent nextCaptured
    have sameOrdinal : real.2.nextBundle = ordinal := selected_ordinal ordinal real.2 (related.2.1 ▸ selected)
    have fresh := ((allowed_bundle ordinal address real outcome).mp admitted).2 target sameOrdinal prepared
    have nextPending : (transport (.inl (.inr (.bundle address))) real modified outcome).2.2.pending = none := by
      simpa only [transport, queryTransport, bundle_next] using pending
    refine ⟨nextPending, captured, ?_⟩
    simpa only [transport, queryTransport, bundleTransport, blocked, ite_true, replaceHistory,
      PqxdhDeploymentPublicationSuppressionFreshness.Fresh, sameNative] using fresh
  · have notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)) :=
      fun address equal => bundled ⟨address, equal⟩
    simp only [transport, PqxdhDeploymentPublicationSecurityTransport.queryTransport_nonbundle query notBundle,
      absent, reduceCtorEq] at captured

/-- Every admitted callback preserves the concrete full-state relation and its original public reply. -/
theorem step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat) (query : (Spec KemSK).Domain)
    (real : RealState KemSK) (modified : ModifiedState KemSK) (related : Related ordinal real modified)
    (outcome : (Spec KemSK).Range query × RealState KemSK)
    (supported : outcome ∈ support
      ((PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query).run real))
    (admitted : allowed ordinal query real outcome = true) :
    outcome.1 = (transport query real modified outcome).1 ∧
      Related ordinal outcome.2 (transport query real modified outcome).2 := by
  obtain ⟨sameReply, physical⟩ := reply_physical setup codec checks seed index ordinal query real modified related
    outcome supported admitted
  have valid := (PqxdhDeploymentPublicationAuditBounds.query_audit setup codec checks seed index query real outcome
    supported).2 related.1
  have sameSelection : (transport query real modified outcome).2.2 = fromAudit ordinal outcome.2.2 := by
    simpa only [transport, related.2.1] using
      PqxdhDeploymentPublicationSecurityStepFacts.query_selection setup codec checks seed index query real related.1
        modified.1.pool.1.transcript ordinal outcome supported
  refine ⟨sameReply, valid, sameSelection, physical, ?_, ?_⟩
  · intro uncaptured
    cases captured : modified.2.target with
    | none =>
        exact uncaptured_equal setup codec checks seed index ordinal query real modified related outcome supported
          captured uncaptured
    | some target =>
        have preserved := PqxdhDeploymentPublicationSuppressionHistory.query_armed setup codec checks seed index query
          modified target (related.2.2.2.2 target captured) (transport query real modified outcome)
          (modified_supported setup codec checks seed index ordinal query real modified related outcome supported)
        have impossible := preserved.2.1
        rw [uncaptured] at impossible
        cases impossible
  · intro target captured
    cases previous : modified.2.target with
    | none => exact captured_armed ordinal query real modified related outcome admitted previous target captured
    | some previousTarget =>
        have preserved := PqxdhDeploymentPublicationSuppressionHistory.query_armed setup codec checks seed index query
          modified previousTarget (related.2.2.2.2 previousTarget previous) (transport query real modified outcome)
          (modified_supported setup codec checks seed index ordinal query real modified related outcome supported)
        have same : target = previousTarget := Option.some.inj (captured.symm.trans preserved.2.1)
        subst target
        exact preserved

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.allowed_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.allowed_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.bundle_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.bundle_next

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.reply_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.reply_physical

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.uncaptured_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.uncaptured_equal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.captured_armed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.captured_armed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep.step
