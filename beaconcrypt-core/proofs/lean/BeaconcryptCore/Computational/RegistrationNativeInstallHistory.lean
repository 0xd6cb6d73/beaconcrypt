-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals

/-! Chronological ordinal association retains old selected installations only through actual forward slot storage. New successful public handles are paired with the same newly recorded role installations at equal per-role offsets. These finite laws are for the full retained ledger and trace. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallHistory
open RegistrationNativeInstallOrdinals (messages handles Counts At Hidden)
open RegistrationNativeG2Trace (Event)
open RegistrationNativeInterface (Entry)
open RegistrationNativeRelatedFamily (Message)
open PqxdhRecordLiftInterface (Role Slot)
variable {n : Nat}

/-- An empty actual chronology has no selected installation obligation. -/
theorem hidden_empty (slots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop) :
    Hidden [] [] slots selected := by
  intro role index message handle paired selectedMessage
  simp only [At, messages, List.filterMap_nil, List.getElem?_nil] at paired
  cases paired.1

/-- Aligned per-role prefixes and suffixes retain their exact ordinal counts after concatenation. -/
theorem counts_append (role : Role) (beforeEvents afterEvents : List Event) (beforeEntries afterEntries : List Entry)
    (before : Counts role beforeEvents beforeEntries) (after : Counts role afterEvents afterEntries) :
    Counts role (beforeEvents ++ afterEvents) (beforeEntries ++ afterEntries) := by
  simp only [Counts, RegistrationNativeInstallOrdinals.messages_append,
    RegistrationNativeInstallOrdinals.handles_append, List.length_append] at before after ⊢
  rw [before, after]

/-- Every ordinal in an aligned original prefix refers to the same message and public handle after appending the actual chronological suffix. -/
theorem at_prefix (role : Role) (beforeEvents afterEvents : List Event) (beforeEntries afterEntries : List Entry)
    (count : Counts role beforeEvents beforeEntries) (index : Nat) (message : Message)
    (handle : PqxdhDeploymentInterface.Handle) (early : index < (messages role beforeEvents).length)
    (paired : At role (beforeEvents ++ afterEvents) (beforeEntries ++ afterEntries) index message handle) :
    At role beforeEvents beforeEntries index message handle := by
  have bounded : index < (handles role beforeEntries).length := by
    change (messages role beforeEvents).length = (handles role beforeEntries).length at count
    rw [← count]
    exact early
  constructor
  · simpa only [RegistrationNativeInstallOrdinals.messages_append, List.getElem?_append_left early] using paired.1
  · simpa only [RegistrationNativeInstallOrdinals.handles_append, List.getElem?_append_left bounded] using paired.2

/-- Every ordinal past an aligned prefix refers to the same suffix message and public handle at the common offset. -/
theorem at_suffix (role : Role) (beforeEvents afterEvents : List Event) (beforeEntries afterEntries : List Entry)
    (count : Counts role beforeEvents beforeEntries) (index : Nat) (message : Message)
    (handle : PqxdhDeploymentInterface.Handle) (late : (messages role beforeEvents).length ≤ index)
    (paired : At role (beforeEvents ++ afterEvents) (beforeEntries ++ afterEntries) index message handle) :
    At role afterEvents afterEntries (index - (messages role beforeEvents).length) message handle := by
  have bounded : (handles role beforeEntries).length ≤ index := by
    change (messages role beforeEvents).length = (handles role beforeEntries).length at count
    rw [← count]
    exact late
  constructor
  · simpa only [RegistrationNativeInstallOrdinals.messages_append, List.getElem?_append_right late] using paired.1
  · change (messages role beforeEvents).length = (handles role beforeEntries).length at count
    simpa only [RegistrationNativeInstallOrdinals.handles_append, List.getElem?_append_right bounded, count] using paired.2

/-- Old ordinal witnesses use actual forward storage; every new ordinal uses its actual successful installation receipt. -/
theorem hidden_append (beforeEvents afterEvents : List Event) (beforeEntries afterEntries : List Entry)
    (beforeSlots afterSlots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop)
    (counts : ∀ role, Counts role beforeEvents beforeEntries)
    (prior : Hidden beforeEvents beforeEntries beforeSlots selected)
    (forward : ∀ handle, (beforeSlots handle).isSome → (afterSlots handle).isSome)
    (installed : ∀ role index message handle, (messages role beforeEvents).length ≤ index →
      At role (beforeEvents ++ afterEvents) (beforeEntries ++ afterEntries) index message handle →
      selected message → (afterSlots handle).isSome) :
    Hidden (beforeEvents ++ afterEvents) (beforeEntries ++ afterEntries) afterSlots selected := by
  intro role index message handle paired selectedMessage
  by_cases early : index < (messages role beforeEvents).length
  · exact forward handle (prior role index message handle
      (at_prefix role beforeEvents afterEvents beforeEntries afterEntries (counts role) index message handle early paired) selectedMessage)
  · exact installed role index message handle (Nat.le_of_not_gt early) paired selectedMessage

/-- A suffix-local installation receipt suffices for every fresh ordinal of the full chronology. -/
theorem hidden_append_of_suffix (beforeEvents afterEvents : List Event) (beforeEntries afterEntries : List Entry)
    (beforeSlots afterSlots : PqxdhDeploymentInterface.Handle → Option (Slot n)) (selected : Message → Prop)
    (counts : ∀ role, Counts role beforeEvents beforeEntries)
    (prior : Hidden beforeEvents beforeEntries beforeSlots selected)
    (forward : ∀ handle, (beforeSlots handle).isSome → (afterSlots handle).isSome)
    (installed : Hidden afterEvents afterEntries afterSlots selected) :
    Hidden (beforeEvents ++ afterEvents) (beforeEntries ++ afterEntries) afterSlots selected := by
  apply hidden_append beforeEvents afterEvents beforeEntries afterEntries beforeSlots afterSlots selected counts prior forward
  intro role index message handle late paired selectedMessage
  exact installed role _ message handle
    (at_suffix role beforeEvents afterEvents beforeEntries afterEntries (counts role) index message handle late paired) selectedMessage

end BeaconcryptCore.Computational.RegistrationNativeInstallHistory
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallHistory.hidden_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallHistory.hidden_empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallHistory.counts_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallHistory.counts_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallHistory.at_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallHistory.at_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallHistory.hidden_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallHistory.hidden_append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallHistory.at_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallHistory.at_suffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallHistory.hidden_append_of_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallHistory.hidden_append_of_suffix
