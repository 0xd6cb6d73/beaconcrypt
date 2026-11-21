-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting

/-! Successful signing histories at source allocation indices and ordinary generated-key indices. The registry distinguishes imported known seeds from generated handles; equal public key bytes do not identify slots. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory
open PqxdhJointIdentity PqxdhDynamicIdentityPool
open PqxdhRegistrationJointIdentityRouting (Ref Registry State Valid route run)

def messageAt (index : Nat) (observation : Observation) : Option Pqxdh.Bytes :=
  match observation with
  | ⟨.inr (.service selected (.sign message)), some _⟩ =>
      if selected = index then some message else none
  | _ => none

def messagesAt (index : Nat) (transcript : List Observation) : List Pqxdh.Bytes :=
  transcript.filterMap (messageAt index)

/-- Only actual successful signing replies enter the chronological projection. -/
theorem append (index : Nat) (before after : List Observation) :
    messagesAt index (before ++ after) = messagesAt index before ++ messagesAt index after := by
  simp [messagesAt]

/-- Generated slots are unique by allocation index, independently of their key bytes. -/
def Unique (registry : Registry) : Prop :=
  ∀ (left right target : Nat), registry.refs[left]? = some (Ref.generated target) →
    registry.refs[right]? = some (Ref.generated target) → left = right

/-- Histories include rejected future-index requests but never count them as successful signatures. -/
structure Tracked (state : State) : Prop where
  valid : Valid state
  unique : Unique state.1
  sourceFuture : ∀ index, state.1.refs.length ≤ index → messagesAt index state.1.transcript = []
  targetFuture : ∀ index, state.2.seeds.length ≤ index → messagesAt index state.2.transcript = []
  generated : ∀ index target, state.1.refs[index]? = some (.generated target) →
    messagesAt index state.1.transcript = messagesAt target state.2.transcript

/-- The real empty registries discharge all history premises before any source request. -/
theorem initial : Tracked (⟨[], []⟩, initialState) := by
  constructor <;> simp [Valid, Unique, messagesAt, initialState]

/-- An appended handle is either an unchanged earlier slot or the one new final slot. -/
theorem lookup_append {A : Type} (entries : List A) (entry value : A) (index : Nat) :
    (entries ++ [entry])[index]? = some value ↔
      entries[index]? = some value ∨ (index = entries.length ∧ entry = value) := by
  by_cases earlier : index < entries.length
  · simp [List.getElem?_append_left earlier, Nat.ne_of_lt earlier]
  · simp [List.getElem?_append_right (Nat.le_of_not_lt earlier),
      List.getElem?_eq_none (Nat.le_of_not_lt earlier)]
    cases difference : index - entries.length <;> simp_all <;> omega

/-- Imports and fresh challenger indices preserve uniqueness of generated references. -/
theorem unique_append (registry : Registry) (entry : Ref) (unique : Unique registry)
    (fresh : ∀ (target index : Nat), entry = .generated target → registry.refs[index]? ≠ some (Ref.generated target)) :
    Unique { registry with refs := registry.refs ++ [entry] } := by
  simp only [Unique, lookup_append] at *
  aesop

/-- The next challenger slot has no earlier successful signatures, including after arbitrary rejected guesses of that index. -/
theorem created (joint : Primitives) (state : State) (seed : IdentitySeed) (tracked : Tracked state) :
    Tracked (PqxdhRegistrationJointIdentityRouting.record (.inr .create)
      (some (state.1.refs.length, joint.publicKeys seed))
      { state.1 with refs := state.1.refs ++ [.generated state.2.seeds.length] },
      (createdReply joint state.2 seed).2) := by
  refine ⟨PqxdhRegistrationJointIdentityRouting.created_valid joint state seed tracked.valid,
    ?_, ?_, ?_, ?_⟩
  case refine_4 =>
    intro index target found
    rcases (lookup_append state.1.refs (.generated state.2.seeds.length) (.generated target) index).mp found with
      previous | ⟨rfl, same⟩
    · simpa [PqxdhRegistrationJointIdentityRouting.record, createdReply, record, messagesAt, messageAt, List.filterMap_cons, List.filterMap_nil]
        using tracked.generated index target previous
    · have equal := Ref.generated.inj same
      subst target
      simpa [PqxdhRegistrationJointIdentityRouting.record, createdReply, record, messagesAt, messageAt, List.filterMap_cons, List.filterMap_nil]
        using (tracked.sourceFuture state.1.refs.length (Nat.le_refl _)).trans
          (tracked.targetFuture state.2.seeds.length (Nat.le_refl _)).symm
  case refine_1 =>
    exact unique_append state.1 (.generated state.2.seeds.length) tracked.unique
      (fun target index same previous =>
        (Nat.ne_of_lt (tracked.valid target (List.mem_of_getElem? previous)))
          (Ref.generated.inj same).symm)
  case refine_2 =>
    intro index future
    simpa [PqxdhRegistrationJointIdentityRouting.record, messagesAt, messageAt,
      List.filterMap_cons, List.filterMap_nil] using tracked.sourceFuture index (by
        simp only [PqxdhRegistrationJointIdentityRouting.record, List.length_append, List.length_singleton] at future
        omega)
  case refine_3 =>
    intro index future
    simpa [createdReply, record, messagesAt, messageAt, List.filterMap_cons, List.filterMap_nil]
      using tracked.targetFuture index (by
        simp only [createdReply, record, List.length_append, List.length_singleton] at future
        omega)

/-- Importing caller-known material creates no ordinary target and changes neither signing history. -/
theorem imported (joint : Primitives) (state : State) (seed : IdentitySeed) (tracked : Tracked state) :
    Tracked ((PqxdhRegistrationJointIdentityRouting.imported joint seed state.1).2, state.2) := by
  refine ⟨?_, ?_, ?_, tracked.targetFuture, ?_⟩
  case refine_1 => simpa [Valid, PqxdhRegistrationJointIdentityRouting.imported] using tracked.valid
  case refine_2 => exact unique_append state.1 (.known seed) tracked.unique (by simp)
  case refine_3 =>
    intro index future
    exact tracked.sourceFuture index (by
      simp only [PqxdhRegistrationJointIdentityRouting.imported, List.length_append, List.length_singleton] at future
      omega)
  case refine_4 =>
    intro index target found
    exact tracked.generated index target (by
      simpa [PqxdhRegistrationJointIdentityRouting.imported, lookup_append] using found)

/-- Exact chronological tail correspondence preserves the invariant without dropping either audit. -/
theorem audit (state : State) (tracked : Tracked state) (sourceTail targetTail : List Observation)
    (sourceFuture : ∀ index, state.1.refs.length ≤ index → messagesAt index sourceTail = [])
    (targetFuture : ∀ index, state.2.seeds.length ≤ index → messagesAt index targetTail = [])
    (generated : ∀ index target, state.1.refs[index]? = some (.generated target) →
      messagesAt index sourceTail = messagesAt target targetTail) :
    Tracked ({ state.1 with transcript := state.1.transcript ++ sourceTail },
      { state.2 with transcript := state.2.transcript ++ targetTail }) := by
  refine ⟨tracked.valid, tracked.unique, ?_, ?_, ?_⟩
  · exact fun index future => by simp only [append, tracked.sourceFuture index future, sourceFuture index future, List.append_nil]
  · exact fun index future => by simp only [append, tracked.targetFuture index future, targetFuture index future, List.append_nil]
  · exact fun index target found => by rw [append, append, tracked.generated index target found, generated index target found]

/-- A forwarded service records the same successful message at its distinct source and challenger indices. -/
theorem generated_service (state : State) (tracked : Tracked state) (index target : Nat)
    (found : state.1.refs[index]? = some (.generated target))
    (request : JointSpec.Domain) (answer : Option (JointSpec.Range request)) :
    Tracked (PqxdhRegistrationJointIdentityRouting.record (.inr (.service index request)) answer state.1,
      record (.inr (.service target request)) answer state.2) := by
  refine audit state tracked [⟨.inr (.service index request), answer⟩]
    [⟨.inr (.service target request), answer⟩] ?_ ?_ ?_
  case refine_3 =>
    intro other otherTarget otherFound
    have same : index = other ↔ target = otherTarget := by
      constructor
      · intro equal
        subst other
        simpa [found] using otherFound
      · intro equal
        subst otherTarget
        exact tracked.unique index other target found otherFound
    cases request <;> cases answer <;>
      simp [messagesAt, List.filterMap_cons, List.filterMap_nil, messageAt, same]
  case refine_1 =>
    intro other future
    have earlier : index < state.1.refs.length := (List.getElem?_eq_some_iff.mp found).1
    have different : index ≠ other := by omega
    cases request <;> cases answer <;>
      simp [messagesAt, List.filterMap_cons, List.filterMap_nil, messageAt, different]
  case refine_2 =>
    intro other future
    have earlier := tracked.valid target (List.mem_of_getElem? found)
    have different : target ≠ other := by omega
    cases request <;> cases answer <;>
      simp [messagesAt, List.filterMap_cons, List.filterMap_nil, messageAt, different]

/-- Coins, creation observations, DH, reveals and rejected services retain their audits without issuing a signing message. -/
theorem silent (state : State) (tracked : Tracked state) (sourceTail targetTail : List Observation)
    (sourceSilent : ∀ index, messagesAt index sourceTail = [])
    (targetSilent : ∀ index, messagesAt index targetTail = []) :
    Tracked ({ state.1 with transcript := state.1.transcript ++ sourceTail },
      { state.2 with transcript := state.2.transcript ++ targetTail }) :=
  audit state tracked sourceTail targetTail (fun index _ => sourceSilent index)
    (fun index _ => targetSilent index)
    (fun index target _ => (sourceSilent index).trans (targetSilent target).symm)

/-- Signing with a caller-known imported seed remains in the native audit and cannot extend any generated target's history. -/
theorem known_service (state : State) (tracked : Tracked state) (index : Nat) (seed : IdentitySeed)
    (found : state.1.refs[index]? = some (.known seed))
    (request : JointSpec.Domain) (answer : Option (JointSpec.Range request)) :
    Tracked (PqxdhRegistrationJointIdentityRouting.record (.inr (.service index request)) answer state.1, state.2) := by
  suffices extended : Tracked ({ state.1 with transcript := state.1.transcript ++ [⟨.inr (.service index request), answer⟩] },
      { state.2 with transcript := state.2.transcript ++ [] }) by
    simp only [List.append_nil] at extended
    cases state with
    | mk registry source => cases source; exact extended
  refine audit state tracked [⟨.inr (.service index request), answer⟩] [] ?_ (by simp [messagesAt]) ?_
  case refine_2 =>
    intro other target otherFound
    have different : index ≠ other := by
      intro equal
      subst other
      simp [found] at otherFound
    cases request <;> cases answer <;>
      simp [messagesAt, List.filterMap_cons, List.filterMap_nil, messageAt, different]
  case refine_1 =>
    intro other future
    have earlier : index < state.1.refs.length := (List.getElem?_eq_some_iff.mp found).1
    have different : index ≠ other := by omega
    cases request <;> cases answer <;>
      simp [messagesAt, List.filterMap_cons, List.filterMap_nil, messageAt, different]

/-- A retained native observation with no successful signature does not change the routed message relation. -/
theorem source_silent (state : State) (tracked : Tracked state)
    (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (quiet : ∀ index, messageAt index ⟨query, answer⟩ = none) :
    Tracked (PqxdhRegistrationJointIdentityRouting.record query answer state.1, state.2) := by
  have extended := silent state tracked [⟨query, answer⟩] []
    (by simp [messagesAt, List.filterMap_nil, quiet]) (by simp [messagesAt])
  rcases state with ⟨registry, ⟨seeds, transcript⟩⟩
  simpa only [List.append_nil, PqxdhRegistrationJointIdentityRouting.record, record] using extended

/-- Ambient random requests retain the ordinary transcript while leaving the native audit unchanged. -/
theorem target_silent (state : State) (tracked : Tracked state)
    (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (quiet : ∀ index, messageAt index ⟨query, answer⟩ = none) :
    Tracked (state.1, record query answer state.2) := by
  have extended := silent state tracked [] [⟨query, answer⟩]
    (by simp [messagesAt]) (by simp [messagesAt, List.filterMap_nil, quiet])
  rcases state with ⟨⟨refs, transcript⟩, source⟩
  simpa only [List.append_nil, PqxdhRegistrationJointIdentityRouting.record, record] using extended

end BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.initial

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.lookup_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.lookup_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.unique_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.unique_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.created

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.imported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.imported

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.audit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.audit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.generated_service' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.generated_service

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.silent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.silent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.known_service' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.known_service

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.source_silent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.source_silent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.target_silent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory.target_silent
