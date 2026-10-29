-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentTranscript

/-! The public original transcript summary only appends configured owner bindings. Later commands and later creations never replace an earlier owner's configured pin. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix
open PqxdhDeploymentTranscript (Summary summarize step stepCommand)
open PqxdhDeploymentInterface (Entry)

private theorem one (before : Summary) (entry : Entry) :
    ∃ suffix, (step before entry).owners = before.owners ++ suffix := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · exact ⟨[], (List.append_nil _).symm⟩
  · cases command with
    | create pin keyId =>
        cases reply with
        | none => exact ⟨[], (List.append_nil _).symm⟩
        | some index =>
            cases parsed : PqxdhDeploymentInterface.parsePin pin with
            | none => exact ⟨[], by simp only [step, stepCommand, parsed, List.append_nil]⟩
            | some word => exact ⟨[(word, keyId)], by simp only [step, stepCommand, parsed]⟩
    | bundle owner =>
        cases reply <;> simp only [step, stepCommand]
        all_goals split <;> exact ⟨[], (List.append_nil _).symm⟩
    | finish owner raw =>
        cases reply <;> simp only [step, stepCommand]
        all_goals split <;> exact ⟨[], (List.append_nil _).symm⟩
    | _ => exact ⟨[], (List.append_nil _).symm⟩
  · exact ⟨[], (List.append_nil _).symm⟩

private theorem fold (before : Summary) (entries : List Entry) :
    ∃ suffix, (entries.foldl step before).owners = before.owners ++ suffix := by
  induction entries generalizing before with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons head tail ih =>
      obtain ⟨first, appended⟩ := one before head
      obtain ⟨rest, later⟩ := ih (step before head)
      exact ⟨first ++ rest, by simpa only [List.foldl_cons, appended, List.append_assoc] using later⟩

/-- Later original transcript entries preserve the configured binding at every already-created owner index. -/
theorem append (before later : List Entry) :
    ∃ suffix, (summarize (before ++ later)).owners = (summarize before).owners ++ suffix := by
  simpa only [summarize, List.foldl_append] using fold (summarize before) later

/-- A configured owner pin read at an earlier actual source cut is exactly the final original designation pin. -/
theorem lookup (before later : List Entry) (index : Nat)
    (first final : PqxdhBeaconPhase2Preparation.Word32 × U64)
    (found : (summarize before).owners[index]? = some first)
    (retained : (summarize (before ++ later)).owners[index]? = some final) : first = final := by
  obtain ⟨suffix, appended⟩ := append before later
  rw [appended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1, found] at retained
  exact Option.some.inj retained
end BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix.append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix.lookup
