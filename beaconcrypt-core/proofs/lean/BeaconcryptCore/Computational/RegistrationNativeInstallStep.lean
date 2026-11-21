-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallHistory

/-! A callback's actual installation suffix is paired with its literal original public reply. Finite composition retains old selected hidden slots through physical forward storage and associates fresh successful handles only with the same suffix ordinal. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallStep
open PqxdhRecordLiftInterface (Role Slot)
open RegistrationNativeG2Trace (Event)
open RegistrationNativeInterface (Entry)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeInstallOrdinals (messages handles Counts At Hidden)
variable {n : Nat}

def RoleStep (role : Role) (beforeEvents afterEvents : List Event) (entry : Entry)
    (slots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop) : Prop :=
  ∃ added : List Message,
    messages role afterEvents = messages role beforeEvents ++ added ∧
    added.length = (handles role [entry]).length ∧
    ∀ (index : Nat) message handle, added[index]? = some message → (handles role [entry])[index]? = some handle →
      selected message → (slots handle).isSome

/-- A literal callback suffix preserves the per-role equality between successful messages and public handles. -/
theorem counts (role : Role) (beforeEvents afterEvents : List Event) (entries : List Entry) (entry : Entry)
    (slots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop)
    (prior : Counts role beforeEvents entries) (step : RoleStep role beforeEvents afterEvents entry slots selected) :
    Counts role afterEvents (entries ++ [entry]) := by
  obtain ⟨added, observed, count, _installed⟩ := step
  simp only [Counts, observed, RegistrationNativeInstallOrdinals.handles_append, List.length_append]
  exact congrArg₂ (· + ·) prior count

/-- The same callback suffix and forward slot storage preserve the hidden-slot association for the full chronology. -/
theorem hidden (beforeEvents afterEvents : List Event) (entries : List Entry) (entry : Entry)
    (beforeSlots afterSlots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop)
    (countsBefore : ∀ role, Counts role beforeEvents entries)
    (prior : Hidden beforeEvents entries beforeSlots selected)
    (forward : ∀ handle, (beforeSlots handle).isSome → (afterSlots handle).isSome)
    (step : ∀ role, RoleStep role beforeEvents afterEvents entry afterSlots selected) :
    Hidden afterEvents (entries ++ [entry]) afterSlots selected := by
  intro role index message handle paired selectedMessage
  obtain ⟨added, observed, _count, installed⟩ := step role
  have count : (messages role beforeEvents).length = (handles role entries).length := countsBefore role
  by_cases early : index < (messages role beforeEvents).length
  · apply forward handle
    apply prior role index message handle _ selectedMessage
    constructor
    · simpa only [observed, List.getElem?_append_left early] using paired.1
    · have bounded : index < (handles role entries).length := count ▸ early
      simpa only [RegistrationNativeInstallOrdinals.handles_append, List.getElem?_append_left bounded] using paired.2
  · have late : (messages role beforeEvents).length ≤ index := Nat.le_of_not_gt early
    have bounded : (handles role entries).length ≤ index := count ▸ late
    apply installed (index - (messages role beforeEvents).length) message handle _ _ selectedMessage
    · simpa only [observed, List.getElem?_append_right late] using paired.1
    · simpa only [RegistrationNativeInstallOrdinals.handles_append, List.getElem?_append_right bounded, count] using paired.2

/-- A callback whose literal public entry has no successful handle contributes no installation message. -/
theorem quiet (role : Role) (beforeEvents afterEvents : List Event) (entry : Entry)
    (slots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop)
    (step : RoleStep role beforeEvents afterEvents entry slots selected) (noHandle : handles role [entry] = []) :
    messages role afterEvents = messages role beforeEvents := by
  obtain ⟨added, observed, count, _installed⟩ := step
  have empty : added = [] := List.eq_nil_of_length_eq_zero (by simpa only [noHandle, List.length_nil] using count)
  simpa only [empty, List.append_nil] using observed

/-- An installation-free callback supplies its full role suffix receipt whenever its original entry has no successful handle. -/
theorem of_quiet (role : Role) (beforeEvents afterEvents : List Event) (entry : Entry)
    (slots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop)
    (unchanged : messages role afterEvents = messages role beforeEvents) (noHandle : handles role [entry] = []) :
    RoleStep role beforeEvents afterEvents entry slots selected := by
  refine ⟨[], ?_, ?_, ?_⟩
  · simpa only [List.append_nil] using unchanged
  · rw [noHandle]
    rfl
  · intro index message handle absent
    simp only [List.getElem?_nil] at absent
    cases absent

end BeaconcryptCore.Computational.RegistrationNativeInstallStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallStep.counts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallStep.counts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallStep.hidden' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallStep.hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallStep.quiet' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallStep.quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallStep.of_quiet' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallStep.of_quiet
