-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/-! The ordinary joint monitor's history is reconstructed from the actual indexed query/reply transcript. Rejected services add no signature, while successful signing attempts enter before native attached-buffer packing. Uniform draws, key creation and reveals do not change signed messages. The index is the generated handle, independently of public-key aliases. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistory
open PqxdhJointIdentity
open PqxdhDynamicIdentityPool (DynamicSpec Observation)
open PqxdhJointIdentityFreshness (GlobalState)

def entry (identity : Nat) (observation : Observation) : Option Event :=
  match observation with
  | ⟨.inr (.service selected request), some reply⟩ =>
      if selected = identity then some (requestEvent request reply) else none
  | _ => none

def history (identity : Nat) (transcript : List Observation) : History :=
  transcript.filterMap (entry identity)

def replay (count : Nat) (transcript : List Observation) : GlobalState count :=
  transcript.foldl (fun prior observation =>
    PqxdhDynamicIdentityRouting.historyUpdate count observation.1 observation.2 prior)
    (PqxdhJointIdentityFreshness.initialState count)

/-- Every observed indexed step appends precisely its actual service event at that generated handle. -/
theorem step_history {count : Nat} (identity : Fin count) (query : DynamicSpec.Domain)
    (answer : DynamicSpec.Range query) (prior : GlobalState count) :
    (PqxdhDynamicIdentityRouting.historyUpdate count query answer prior).histories identity =
      prior.histories identity ++ (entry identity.1 ⟨query, answer⟩).toList := by
  cases query with
  | inl coin => simp [PqxdhDynamicIdentityRouting.historyUpdate, entry]
  | inr query => cases query with
    | create => simp [PqxdhDynamicIdentityRouting.historyUpdate, entry]
    | reveal selected =>
        simp only [PqxdhDynamicIdentityRouting.historyUpdate]
        split <;> cases answer <;> simp [PqxdhJointIdentityEvents.publicUpdate, entry]
    | service selected request =>
        by_cases valid : selected < count
        · by_cases same : selected = identity.1
          · subst selected
            cases answer <;> simp [PqxdhDynamicIdentityRouting.historyUpdate, valid, entry,
              PqxdhJointIdentityEvents.publicUpdate]
          · have different : (⟨selected, valid⟩ : Fin count) ≠ identity := by
              intro equal
              exact same (congrArg Fin.val equal)
            cases answer <;> simp [PqxdhDynamicIdentityRouting.historyUpdate, valid, entry,
              PqxdhJointIdentityEvents.publicUpdate, same, Ne.symm different]
        · have different : selected ≠ identity.1 := by
            intro equal
            exact valid (equal ▸ identity.isLt)
          cases answer <;> simp [PqxdhDynamicIdentityRouting.historyUpdate, valid, entry, different]

/-- The ordinary monitor retains the complete per-handle source history, including optional static-DH rejection. -/
theorem fold_history {count : Nat} (identity : Fin count) (transcript : List Observation)
    (prior : GlobalState count) :
    (transcript.foldl (fun state observation =>
      PqxdhDynamicIdentityRouting.historyUpdate count observation.1 observation.2 state) prior).histories identity =
      prior.histories identity ++ history identity.1 transcript := by
  induction transcript generalizing prior with
  | nil => simp [history]
  | cons observation rest ih =>
      rw [List.foldl_cons, ih, step_history]
      simp only [history, List.filterMap_cons, List.append_assoc]
      cases entry identity.1 observation <;> rfl

/-- Starting from the actual empty monitor gives the exact transcript-derived history, with no native success or publication premise. -/
theorem replay_history {count : Nat} (identity : Fin count) (transcript : List Observation) :
    (replay count transcript).histories identity = history identity.1 transcript := by
  rw [replay, fold_history]
  rfl

theorem append_history (identity : Nat) (earlier later : List Observation) :
    history identity (earlier ++ later) = history identity earlier ++ history identity later := by
  exact List.filterMap_append

theorem sign_history (identity : Nat) (transcript : List Observation) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    history identity (transcript ++ [⟨.inr (.service identity (.sign message)), some signature⟩]) =
      history identity transcript ++ [.signed message signature] := by
  simp [history, entry, requestEvent, List.filterMap_append]

theorem other_sign_history (identity selected : Nat) (different : selected ≠ identity)
    (transcript : List Observation) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    history identity (transcript ++ [⟨.inr (.service selected (.sign message)), some signature⟩]) =
      history identity transcript := by
  simp [history, entry, requestEvent, List.filterMap_append, different]

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.step_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.step_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.fold_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.fold_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.replay_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.replay_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.append_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.append_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.sign_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.sign_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.other_sign_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistory.other_sign_history
