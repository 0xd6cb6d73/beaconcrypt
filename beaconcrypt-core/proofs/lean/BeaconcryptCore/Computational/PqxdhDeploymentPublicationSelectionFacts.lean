-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace

/-! The executable selection countdown is determined by the actual global bundle-call audit. Missing and inactive calls consume ordinals, and only a prepared tuple at the selected ordinal supplies the public target capability. -/

open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts
open PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppression (Selection Target)
open PqxdhDeploymentPublicationSuppressionTrace (Audit Occurrence)

def pendingAt (ordinal seen : Nat) : Option Nat :=
  if seen ≤ ordinal then some (ordinal - seen) else none

def occurrenceTarget (occurrence : Occurrence) : Target :=
  ⟨occurrence.identityIndex, occurrence.keys.oneTime⟩

def targetAt (occurrences : List Occurrence) (ordinal : Nat) : Option Target :=
  occurrences.findSome? fun occurrence =>
    if occurrence.ordinal = ordinal then some (occurrenceTarget occurrence) else none

def fromAudit (ordinal : Nat) (audit : Audit) : Selection :=
  ⟨pendingAt ordinal audit.nextBundle, targetAt audit.occurrences ordinal⟩

/-- Before the selected public-call ordinal, no already recorded prepared occurrence can supply its target. -/
theorem targetAt_future (occurrences : List Occurrence) (ordinal seen : Nat)
    (past : ∀ occurrence ∈ occurrences, occurrence.ordinal < seen) (future : seen ≤ ordinal) :
    targetAt occurrences ordinal = none := by
  induction occurrences with
  | nil => rfl
  | cons head tail ih =>
      have different : head.ordinal ≠ ordinal := by
        have bounded := past head (by simp)
        omega
      have absent := ih (fun occurrence member => past occurrence (by simp [member]))
      simpa [targetAt, different] using absent

/-- A countdown update consumes exactly one global public bundle call, including an absent or unprepared owner. -/
theorem next_countdown (ordinal seen : Nat) (previous prepared : Option Target) :
    Selection.next ⟨pendingAt ordinal seen, previous⟩ prepared =
      ⟨pendingAt ordinal (seen + 1), if seen = ordinal then prepared else previous⟩ := by
  by_cases before : seen ≤ ordinal
  · by_cases selected : seen = ordinal
    · subst ordinal
      simp [pendingAt, Selection.next, Selection.advance]
    · have nextBefore : seen + 1 ≤ ordinal := by omega
      have positive : 0 < ordinal - seen := by omega
      obtain ⟨remaining, difference⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      have nextDifference : ordinal - (seen + 1) = remaining := by omega
      simp [pendingAt, before, nextBefore, difference, nextDifference, selected, Selection.next, Selection.advance]
  · have nextAfter : ¬ seen + 1 ≤ ordinal := by omega
    have different : seen ≠ ordinal := by omega
    simp [pendingAt, before, nextAfter, different, Selection.next, Selection.advance]

/-- The real occurrence audit starts with exactly the executable initial countdown and no selected capability. -/
theorem fromAudit_empty (ordinal : Nat) : fromAudit ordinal Audit.empty = Selection.initial ordinal := by
  simp [fromAudit, pendingAt, targetAt, Audit.empty, Selection.initial]

/-- Recording a real prepared or unprepared call updates the selected capability at exactly its own global call ordinal. -/
theorem targetAt_record (audit : Audit) (ordinal address index : Nat) (reply : Option Pqxdh.Bytes)
    (keys : Option Phase1KeyTuple) (past : ∀ occurrence ∈ audit.occurrences, occurrence.ordinal < audit.nextBundle) :
    targetAt (audit.record address index reply keys.toList).occurrences ordinal =
      if audit.nextBundle = ordinal then keys.map (fun tuple => (⟨index, tuple.oneTime⟩ : Target))
      else targetAt audit.occurrences ordinal := by
  by_cases selected : audit.nextBundle = ordinal
  · have absent := targetAt_future audit.occurrences ordinal audit.nextBundle past selected.le
    simp only [targetAt, occurrenceTarget] at absent
    cases keys <;> simp [Audit.record, targetAt, List.findSome?_append, selected, absent, occurrenceTarget]
  · cases keys <;> simp [Audit.record, targetAt, List.findSome?_append, selected, occurrenceTarget]

/-- The same audit-derived selection is preserved by the executable whole-call selection update, on every real chronological audit. -/
theorem fromAudit_record (audit : Audit) (ordinal address index : Nat) (reply : Option Pqxdh.Bytes)
    (keys : Option Phase1KeyTuple) (past : ∀ occurrence ∈ audit.occurrences, occurrence.ordinal < audit.nextBundle) :
    Selection.next (fromAudit ordinal audit) (keys.map fun tuple => (⟨index, tuple.oneTime⟩ : Target)) =
      fromAudit ordinal (audit.record address index reply keys.toList) := by
  rw [fromAudit, next_countdown, fromAudit, targetAt_record audit ordinal address index reply keys past]
  rfl

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.targetAt_future' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.targetAt_future

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.next_countdown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.next_countdown

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.fromAudit_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.fromAudit_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.targetAt_record' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.targetAt_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.fromAudit_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts.fromAudit_record
