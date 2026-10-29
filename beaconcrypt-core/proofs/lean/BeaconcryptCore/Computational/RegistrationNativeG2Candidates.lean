-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-! Known-first candidates are extracted from the actual chronological supplied-input preparation requests. Their count is bounded by the original preparation-query bill, independent of other primitive loops or optional replies. This adapter supplies public candidates to the separate related-family checker; it does not privately test protection or assume any candidate is unrelated. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG2Candidates
open RegistrationNativeG2Trace (State Event handler)
open PqxdhJointIdentity (DhOutput)
variable {n : Nat} {KemSK Value : Type}

def first : Event → Option DhOutput
  | .prepare message => match message.third with
      | .supplied value _ => some value
      | _ => none
  | _ => none

def candidates (before : State) : List DhOutput := before.events.filterMap first

def preparations : List Event → Nat
  | [] => 0
  | .prepare _ :: rest => 1 + preparations rest
  | _ :: rest => preparations rest

def IsPrepare : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → Prop
  | .inl (.inl _) => True
  | _ => False
instance : DecidablePred (IsPrepare (n := n) (KemSK := KemSK)) := fun query => by
  rcases query with (_ | _) | _ <;> first | exact isTrue trivial | exact isFalse id

private theorem preparations_append (left right : List Event) :
    preparations (left ++ right) = preparations left + preparations right := by
  induction left with
  | nil => simp only [List.nil_append, preparations, Nat.zero_add]
  | cons event rest ih => cases event <;> simp only [List.cons_append, preparations, ih, Nat.add_assoc]

/-- Only actual supplied-input preparation requests contribute to the public known-first candidate list. -/
theorem candidates_length (before : State) : (candidates before).length ≤ preparations before.events := by
  unfold candidates
  induction before.events with
  | nil => simp only [List.filterMap_nil, List.length_nil, preparations, le_refl]
  | cons event rest ih =>
      cases event with
      | prepare message =>
          simp only [first] at ih
          cases found : message.third <;> simp only [List.filterMap_cons, first, found, preparations,
            List.length_cons] <;> omega
      | demand message => simpa only [List.filterMap_cons, first, preparations] using ih
      | encapsulate selected key ciphertext secret => simpa only [List.filterMap_cons, first, preparations] using ih
      | installAttempt role message => simpa only [List.filterMap_cons, first, preparations] using ih
      | install role message => simpa only [List.filterMap_cons, first, preparations] using ih

private theorem begin_count (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State) :
    preparations (RegistrationNativeG2Trace.begin query before).events =
      preparations before.events + if IsPrepare (KemSK := KemSK) query then 1 else 0 := by
  rcases query with (message | (message | query) | query) | query
  · simp [RegistrationNativeG2Trace.begin, preparations_append, preparations, IsPrepare]
  · simp [RegistrationNativeG2Trace.begin, preparations_append, preparations, IsPrepare]
  · cases query with
    | inl query => simp [RegistrationNativeG2Trace.begin, IsPrepare]
    | inr query => cases query with
      | inl coin => simp [RegistrationNativeG2Trace.begin, IsPrepare]
      | inr capability =>
          cases capability <;> simp only [RegistrationNativeG2Trace.begin, IsPrepare, ite_false, Nat.add_zero]
          all_goals cases found : before.current <;>
            simp [RegistrationNativeG2Trace.attempt, found, preparations_append, preparations]
  · simp [RegistrationNativeG2Trace.begin, IsPrepare]
  · simp [RegistrationNativeG2Trace.begin, IsPrepare]

private theorem finish_count (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (reply : (RegistrationNativePublicFrontend.Spec n KemSK).Range query) (before : State) :
    preparations (RegistrationNativeG2Trace.finish query reply before).events = preparations before.events := by
  rcases query with (message | (message | query) | query) | query
  · rfl
  · rfl
  · cases query with
    | inl query => rfl
    | inr query => cases query with
      | inl coin => rfl
      | inr capability =>
          cases capability <;> try rfl
          all_goals cases reply <;> cases found : before.current <;>
            simp [RegistrationNativeG2Trace.finish, RegistrationNativeG2Trace.installed, found, preparations_append, preparations]
  · rcases query with (query | key) | (query | key)
    · rfl
    · simp [RegistrationNativeG2Trace.finish, preparations_append, preparations]
    · rfl
    · simp [RegistrationNativeG2Trace.finish, preparations_append, preparations]
  · rfl

/-- The actual query trace increments its preparation count exactly at a reached preparation request. -/
theorem query_count (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (reply : (RegistrationNativePublicFrontend.Spec n KemSK).Range query) (before : State) :
    preparations (RegistrationNativeG2Trace.finish query reply (RegistrationNativeG2Trace.begin query before)).events =
      preparations before.events + if IsPrepare (KemSK := KemSK) query then 1 else 0 := by
  rw [finish_count, begin_count]

/-- Every supported adaptive trace obeys its original preparation-query bound. -/
theorem program_count (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (IsPrepare (KemSK := KemSK)) count)
    (before : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ handler work).run before)) :
    preparations result.2.events ≤ preparations before.events + count := by
  induction work using OracleComp.inductionOn generalizing count before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      change preparations before.events ≤ preparations before.events + count
      omega
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reached, stepped, continued⟩ := supported
      simp only [handler, StateT.run, support_map] at stepped
      obtain ⟨reply, _actualReply, equal⟩ := stepped
      cases equal
      have tail := ih reply _ (bounded.2 reply) _ continued
      have step := query_count query reply before
      by_cases counted : IsPrepare (KemSK := KemSK) query
      · have positive : 0 < count := bounded.1.resolve_left (not_not.mpr counted)
        simp only [ite_eq_left counted] at tail step
        omega
      · simp only [ite_eq_right counted] at tail step
        omega

/-- The literal observer's returned candidate list has the same actual preparation cap. -/
theorem candidate_bound (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (IsPrepare (KemSK := KemSK)) count)
    (result : Value × State) (supported : result ∈ support (RegistrationNativeG2Trace.program work)) :
    (candidates result.2).length ≤ count := by
  have boundedTrace := program_count work count bounded RegistrationNativeG2Trace.initial result supported
  exact (candidates_length result.2).trans (by simpa only [RegistrationNativeG2Trace.initial, preparations, Nat.zero_add] using boundedTrace)

end BeaconcryptCore.Computational.RegistrationNativeG2Candidates

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Candidates.candidates_length' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Candidates.candidates_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Candidates.query_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Candidates.query_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Candidates.program_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Candidates.program_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Candidates.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Candidates.candidate_bound
