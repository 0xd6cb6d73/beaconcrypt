-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds

/-! Every actual initialized deployment audit obeys the public all-attempt bundle budget. Selecting the first occurrence of an unpublished one-time message uses its real global call ordinal, including missing and inactive calls in the counter. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentPublicationSuppressionTrace (Occurrence)
open PqxdhDeploymentPublicationAuditBounds (Valid)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The actual Server constructor and source execution discharge the global ordinal bound from the deployment budget, for every successful initialized outcome. -/
theorem actual_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime)) :
    Valid outcome.2.2.2 ∧ outcome.2.2.2.nextBundle ≤ budget.bundle := by
  simp only [actual, initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, _, continued⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  · simp only [support_map, Set.mem_image] at continued
    obtain ⟨executed, member, equal⟩ := continued
    have same : outcome = (PqxdhRegistrationJointServerBirth.encode created, executed.1, executed.2) :=
      (Option.some.inj (congrArg Prod.fst equal)).symm
    rw [same]
    exact PqxdhDeploymentPublicationAuditBounds.compileFull_audit setup codec checks created.seed
      created.server.server.metadata.identityIndex route bounds mode adversary budget respects _ executed member

/-- Every prepared bundle occurrence is below the all-attempt cap, including a signature block whose later writer failed. -/
theorem actual_occurrence_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime))
    (occurrence : Occurrence) (member : occurrence ∈ outcome.2.2.2.occurrences) :
    occurrence.ordinal < budget.bundle := by
  obtain ⟨valid, bounded⟩ := actual_audit setup codec checks route ensureInit bounds mode adversary budget respects
    runtime outcome after supported
  exact (valid.1 occurrence member).trans_le bounded

/-- The first matching real prepared attempt has an actual global bundle-call ordinal in the public budget, and no earlier occurrence matches it. -/
theorem actual_earliest (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime))
    (matchesMessage : Occurrence → Bool)
    (present : ∃ occurrence ∈ outcome.2.2.2.occurrences, matchesMessage occurrence = true) :
    ∃ (selected : Fin budget.bundle) (occurrence : Occurrence), occurrence ∈ outcome.2.2.2.occurrences ∧
      occurrence.ordinal = selected.val ∧ matchesMessage occurrence = true ∧
      ∀ previous ∈ outcome.2.2.2.occurrences, previous.ordinal < selected.val → matchesMessage previous = false := by
  obtain ⟨valid, bounded⟩ := actual_audit setup codec checks route ensureInit bounds mode adversary budget respects
    runtime outcome after supported
  obtain ⟨occurrence, member, ordinalBound, matched, earliest⟩ :=
    PqxdhDeploymentPublicationAuditBounds.earliest_occurrence outcome.2.2.2 valid matchesMessage present
  exact ⟨⟨occurrence.ordinal, ordinalBound.trans_le bounded⟩, occurrence, member, rfl, matched, earliest⟩

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_earliest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_earliest
