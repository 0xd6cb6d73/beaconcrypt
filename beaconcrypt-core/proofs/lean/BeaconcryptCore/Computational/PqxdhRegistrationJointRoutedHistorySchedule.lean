-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistory

/-! Every supported actual generated/imported routing schedule preserves the exact signing-history correspondence, including rejected future handles, compromise and arbitrary adaptive continuations. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule
open PqxdhJointIdentity PqxdhDynamicIdentityPool
open PqxdhRegistrationJointIdentityRouting (Spec State route run)
open PqxdhRegistrationJointRoutedHistory

set_option backward.isDefEq.respectTransparency false in
/-- The real source router preserves the complete-index history relation on every possible actual reply. -/
theorem query (joint : Primitives) (request : Spec.Domain) (state : State) (tracked : Tracked state)
    (result : Spec.Range request × State)
    (supported : result ∈ support (run joint (route joint request) state)) : Tracked result.2 := by
  rcases request with (coin | request) | (coin | seed)
  case inl.inr =>
    cases request with
    | create =>
        rw [PqxdhRegistrationJointIdentityRouting.create_run] at supported
        obtain ⟨seed, _, rfl⟩ := (show ∃ seed ∈ support sampleSeed, _ from by
          simpa only [support_map, Set.mem_image] using supported)
        exact created joint state seed tracked
    | service index request =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
            subst result
            exact source_silent state tracked (.inr (.service index request)) none (by cases request <;> simp [messageAt])
        | some reference =>
            cases reference with
            | known seed =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
                subst result
                exact known_service state tracked index seed found request _
            | generated target =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
                simp only [lazyImpl, poolImpl, StateT.run, map_pure, mem_support_pure_iff] at supported
                subst result
                exact generated_service state tracked index target found request _
    | reveal index =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure,
              StateT.run_pure, map_pure, mem_support_pure_iff] at supported
            subst result
            exact source_silent state tracked (.inr (.reveal index)) none (by simp [messageAt])
        | some reference =>
            cases reference with
            | known seed =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure,
                  StateT.run_pure, map_pure, mem_support_pure_iff] at supported
                subst result
                exact source_silent state tracked (.inr (.reveal index)) (some seed) (by simp [messageAt])
            | generated target =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, bind_pure_comp,
                  simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
                simp only [lazyImpl, poolImpl, StateT.run, map_pure, mem_support_pure_iff] at supported
                subst result
                exact silent state tracked [⟨.inr (.reveal index), state.2.seeds[target]?⟩]
                  [⟨.inr (.reveal target), state.2.seeds[target]?⟩]
                  (by simp [messagesAt, messageAt]) (by simp [messagesAt, messageAt])
  case inl.inl =>
    simp only [PqxdhRegistrationJointIdentityRouting.run, route, simulateQ_map, simulateQ_spec_query,
      StateT.run_map] at supported
    simp only [lazyImpl, poolImpl, StateT.run, bind_pure_comp, Functor.map_map,
      support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact silent state tracked [⟨.inl coin, answer⟩] [⟨.inl coin, answer⟩]
      (by simp [messagesAt, messageAt]) (by simp [messagesAt, messageAt])
  case inr.inl =>
    simp only [PqxdhRegistrationJointIdentityRouting.run, route, simulateQ_map, simulateQ_spec_query,
      StateT.run_map] at supported
    simp only [lazyImpl, poolImpl, StateT.run, bind_pure_comp, Functor.map_map,
      support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact target_silent state tracked (.inl coin) answer (by simp [messageAt])
  case inr.inr =>
    simp only [PqxdhRegistrationJointIdentityRouting.run, route, simulateQ_pure, StateT.run_pure,
      map_pure, mem_support_pure_iff] at supported
    subst result
    exact imported joint state seed tracked

set_option backward.isDefEq.respectTransparency false in
/-- The invariant follows the complete coupled adaptive computation and both final states. No continuation or successful report is assumed in advance. -/
theorem program {Result : Type} (joint : Primitives) (work : OracleComp Spec Result)
    (state : State) (tracked : Tracked state) (result : Result × State)
    (supported : result ∈ support (run joint (simulateQ (route joint) work) state)) :
    Tracked result.2 := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      have equal : result = (value, state) := eq_of_mem_support_pure supported
      subst result
      exact tracked
  | query_bind request next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointIdentityRouting.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, step, tail⟩ := supported
      exact ih head.1 head.2 (query joint request state tracked head step) result tail

/-- Every actually reached mapped generated identity has exactly its native source-index signing log, even after known imports, failed future-index requests and later compromise. -/
theorem generated_history {Result : Type} (joint : Primitives) (work : OracleComp Spec Result)
    (result : Result × State)
    (supported : result ∈ support (run joint (simulateQ (route joint) work) (⟨[], []⟩, initialState)))
    (index target : Nat) (found : result.2.1.refs[index]? = some (.generated target)) :
    messagesAt index result.2.1.transcript = messagesAt target result.2.2.transcript :=
  (program joint work _ initial result supported).generated index target found

end BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule.query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule.program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule.generated_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule.generated_history
