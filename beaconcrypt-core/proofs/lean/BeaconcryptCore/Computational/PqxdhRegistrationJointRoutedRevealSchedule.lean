-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals

/-! Every supported actual generated/imported routing schedule preserves the exact successful-disclosure correspondence, including rejected future handles, compromise and arbitrary adaptive continuations. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedRevealSchedule
open PqxdhJointIdentity PqxdhDynamicIdentityPool
open PqxdhRegistrationJointIdentityRouting (Spec State route run)
open PqxdhRegistrationJointRoutedReveals
open PqxdhRegistrationJointRoutedHistory (Tracked)

set_option backward.isDefEq.respectTransparency false in
/-- The real source router preserves the complete-index disclosure relation on every possible actual reply. -/
theorem query (joint : Primitives) (request : Spec.Domain) (state : State) (tracked : Tracked state) (before : Recorded state)
    (result : Spec.Range request × State)
    (supported : result ∈ support (run joint (route joint request) state)) : Recorded result.2 := by
  rcases request with (coin | request) | (coin | seed)
  case inl.inr =>
    cases request with
    | create =>
        rw [PqxdhRegistrationJointIdentityRouting.create_run] at supported
        obtain ⟨seed, _, rfl⟩ := (show ∃ seed ∈ support sampleSeed, _ from by
          simpa only [support_map, Set.mem_image] using supported)
        exact created joint state seed before
    | service index request =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
            subst result
            exact source_silent state before (.inr (.service index request)) none (by cases request <;> simp [revealAt])
        | some reference =>
            cases reference with
            | known seed =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
                subst result
                exact source_silent state before (.inr (.service index request)) _ (by cases request <;> simp [revealAt])
            | generated target =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
                simp only [lazyImpl, poolImpl, StateT.run, map_pure, mem_support_pure_iff] at supported
                subst result
                exact silent state before [⟨.inr (.service index request), _⟩]
                  [⟨.inr (.service target request), _⟩]
                  (by intro index; cases request <;> simp [revealedAt, revealAt])
                  (by intro index; cases request <;> simp [revealedAt, revealAt])
    | reveal index =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure,
              StateT.run_pure, map_pure, mem_support_pure_iff] at supported
            subst result
            exact source_silent state before (.inr (.reveal index)) none (by simp [revealAt])
        | some reference =>
            cases reference with
            | known seed =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, pure_bind, simulateQ_pure,
                  StateT.run_pure, map_pure, mem_support_pure_iff] at supported
                subst result
                exact known_reveal state before index seed found (some seed)
            | generated target =>
                simp only [PqxdhRegistrationJointIdentityRouting.run, route, found, bind_pure_comp,
                  simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
                simp only [lazyImpl, poolImpl, StateT.run, map_pure, mem_support_pure_iff] at supported
                subst result
                exact generated_reveal state tracked before index target found _
  case inl.inl =>
    simp only [PqxdhRegistrationJointIdentityRouting.run, route, simulateQ_map, simulateQ_spec_query,
      StateT.run_map] at supported
    simp only [lazyImpl, poolImpl, StateT.run, bind_pure_comp, Functor.map_map,
      support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact silent state before [⟨.inl coin, answer⟩] [⟨.inl coin, answer⟩]
      (by simp [revealedAt, revealAt]) (by simp [revealedAt, revealAt])
  case inr.inl =>
    simp only [PqxdhRegistrationJointIdentityRouting.run, route, simulateQ_map, simulateQ_spec_query,
      StateT.run_map] at supported
    simp only [lazyImpl, poolImpl, StateT.run, bind_pure_comp, Functor.map_map,
      support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact target_silent state before (.inl coin) answer (by simp [revealAt])
  case inr.inr =>
    simp only [PqxdhRegistrationJointIdentityRouting.run, route, simulateQ_pure, StateT.run_pure,
      map_pure, mem_support_pure_iff] at supported
    subst result
    exact imported joint state seed before

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary adaptive source work preserves the successful reveal correspondence together with its independently derived handle invariant. -/
theorem program {Result : Type} (joint : Primitives) (work : OracleComp Spec Result)
    (state : State) (tracked : Tracked state) (before : Recorded state) (result : Result × State)
    (supported : result ∈ support (run joint (simulateQ (route joint) work) state)) :
    Recorded result.2 := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      have equal : result = (value, state) := eq_of_mem_support_pure supported
      subst result
      exact before
  | query_bind request next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointIdentityRouting.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, step, tail⟩ := supported
      exact ih head.1 head.2 (PqxdhRegistrationJointRoutedHistorySchedule.query joint request state tracked head step)
        (query joint request state tracked before head step) result tail

end BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedRevealSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedRevealSchedule.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedRevealSchedule.query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedRevealSchedule.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedRevealSchedule.program
