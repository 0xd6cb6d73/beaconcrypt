-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialSessions

/-! Existing one-use Server session slots are immutable: later native accepts append and builds can only remove a capability. This relation transports an actual stored Ready backwards across arbitrary later commands without equating separate existential receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots
open RegistrationNativeSecretWordMessage (ServerReady ServerState)

def Preserves (before after : List (Option ServerReady)) : Prop :=
  before.length ≤ after.length ∧
    ∀ index, index < before.length → ∀ ready,
      after[index]? = some (some ready) → before[index]? = some (some ready)

theorem refl (sessions : List (Option ServerReady)) : Preserves sessions sessions :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem trans (first middle last : List (Option ServerReady))
    (earlier : Preserves first middle) (later : Preserves middle last) : Preserves first last := by
  refine ⟨earlier.1.trans later.1, ?_⟩
  intro index below ready found
  exact earlier.2 index below ready (later.2 index (Nat.lt_of_lt_of_le below earlier.1) ready found)

/-- Every actual accept shape preserves all older stored session values. -/
theorem shape (before after : List (Option ServerReady)) (reply : RustM (Option Nat))
    (actual : RegistrationNativeSecretWordAtomSessionShape.Shape before reply after) : Preserves before after := by
  rcases actual with same | ⟨ready, same, _returned⟩
  · rw [same]
    exact refl before
  · rw [same]
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro index below other found
    simpa only [List.getElem?_append_left below] using found

/-- The original one-use take removes its own slot and preserves every other value. -/
theorem take (handle : Nat) (before : ServerState) :
    Preserves before.sessions (RegistrationNativeSecretWordServerMaterial.take handle before).2.sessions := by
  unfold RegistrationNativeSecretWordServerMaterial.take
  cases found : before.sessions[handle]? with
  | none => exact refl _
  | some entry => cases entry with
    | none => exact refl _
    | some ready =>
        refine ⟨by simp only [List.length_set]; exact Nat.le_refl _, ?_⟩
        intro index below other after
        by_cases same : handle = index
        · subst index
          rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1] at after
          cases after
        · simpa only [List.getElem?_set_ne same] using after

end BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.refl
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.trans
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots.take
