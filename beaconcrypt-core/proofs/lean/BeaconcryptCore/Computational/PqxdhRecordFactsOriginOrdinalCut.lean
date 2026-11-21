-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal

/-! Exact probabilistic source-prefix cut before an attempted sealing ordinal. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (Service ServiceSpec Sealing)
open PqxdhRecordFactsPrivateCacheSource (Reach)
open PqxdhRecordLiftWorldProvenance (sealingCoordinates)
variable {n : Nat} {X : Type}

/-- A source cut retains the exact attempted seal, full private prefix state, attempted-label history and literal remaining continuation. -/
structure Cut (n : Nat) (X : Type) where
  pending : Sealing n
  next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X
  state : CtxPrivate n
  past : List (Label n)

/-- Earlier source completion is retained as an actual result and full state, rather than being discarded. -/
abbrev Outcome (n : Nat) (X : Type) := (X × CtxPrivate n) ⊕ Cut n X

/-- Stop before the chosen sealing callback's reply; all prior callbacks execute under the literal supplied stateful service. -/
noncomputable def scan (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) : Nat → CtxPrivate n → List (Label n) → ProbComp (Outcome n X) :=
  OracleComp.recOn work
    (fun value _ state _ => pure (.inl (value, state)))
    (fun query next recurse index state past => match query with
      | .sealing pending => match index with
        | 0 => pure (.inr ⟨pending, next, state, past⟩)
        | index + 1 => do
          let reply ← (service (.sealing pending)).run state
          recurse reply.1 index reply.2 (past ++ [pending.material])
      | query => do
          let reply ← (service query).run state
          recurse reply.1 index reply.2 past)

/-- Resume the actual selected callback and its full literal adaptive continuation. -/
noncomputable def resume (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) :
    Outcome n X → ProbComp (X × CtxPrivate n)
  | .inl result => pure result
  | .inr cut => do
      let reply ← (service (.sealing cut.pending)).run cut.state
      (simulateQ service (cut.next reply.1)).run reply.2

/-- The zero ordinal stops before drawing any selected reply, including any writer result. -/
theorem scan_target (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (pending : Sealing n) (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) :
    scan service ((ServiceSpec n).query (.sealing pending) >>= next) 0 state past =
      pure (.inr ⟨pending, next, state, past⟩) := rfl

/-- Each earlier sealing callback advances the attempted ordinal and history regardless of its result. -/
theorem scan_prior (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (pending : Sealing n) (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (index : Nat) (state : CtxPrivate n) (past : List (Label n)) :
    scan service ((ServiceSpec n).query (.sealing pending) >>= next) (index + 1) state past =
      ((service (.sealing pending)).run state >>= fun reply =>
        scan service (next reply.1) index reply.2 (past ++ [pending.material])) := rfl

/-- Other source callbacks execute with their full reply and state and consume no sealing ordinal. -/
theorem scan_other (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (nonSeal : ∀ pending, query ≠ .sealing pending)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (index : Nat) (state : CtxPrivate n) (past : List (Label n)) :
    scan service ((ServiceSpec n).query query >>= next) index state past =
      ((service query).run state >>= fun reply => scan service (next reply.1) index reply.2 past) := by
  cases query
  case sealing pending => exact False.elim (nonSeal pending rfl)
  all_goals rfl

/-- Scanning and resuming reconstructs the entire original stateful probabilistic execution, including early completion. -/
theorem scan_resume (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (index : Nat) (state : CtxPrivate n) (past : List (Label n)) :
    (scan service work index state past >>= resume service) = (simulateQ service work).run state := by
  induction work using OracleComp.inductionOn generalizing index state past with
  | pure value => rfl
  | query_bind query next ih =>
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      cases index with
      | zero => rw [scan_target]; rfl
      | succ index =>
        rw [scan_prior]
        simp only [bind_assoc, ih, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    · rw [scan_other service query (fun pending same => sealed ⟨pending, same⟩)]
      simp only [bind_assoc, ih, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- A scan-supported cut is an actual full source prefix, at exactly the requested relative attempted-seal ordinal. -/
theorem scan_reachable (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (initial : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) (past0 : List (Label n))
    (work : OracleComp (ServiceSpec n) X) (index : Nat) (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach service initial start past0 work state past) (cut : Cut n X)
    (selected : Sum.inr cut ∈ support (scan service work index state past)) :
    Reach service initial start past0
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past ∧
      cut.past.length = past.length + index := by
  induction work using OracleComp.inductionOn generalizing index state past with
  | pure value =>
    change Sum.inr cut ∈ support (pure (Sum.inl (value, state)) : ProbComp (Outcome n X)) at selected
    simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at selected
  | query_bind query next ih =>
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      cases index with
      | zero =>
        rw [scan_target] at selected
        simp only [support_pure, Set.mem_singleton_iff, Sum.inr.injEq] at selected
        subst cut
        exact ⟨reached, (Nat.add_zero _).symm⟩
      | succ index =>
        rw [scan_prior] at selected
        simp only [mem_support_bind_iff] at selected
        obtain ⟨reply, supported, selected⟩ := selected
        have continued := Reach.step reached supported
        obtain ⟨found, counted⟩ := ih reply.1 index reply.2 (past ++ [pending.material]) continued selected
        refine ⟨found, ?_⟩
        simp only [List.length_append, List.length_singleton] at counted
        omega
    · rw [scan_other service query (fun pending same => sealed ⟨pending, same⟩)] at selected
      simp only [mem_support_bind_iff] at selected
      obtain ⟨reply, supported, selected⟩ := selected
      have empty : sealingCoordinates query = [] := by
        cases query
        case sealing pending => exact False.elim (sealed ⟨pending, rfl⟩)
        all_goals rfl
      have continued : Reach service initial start past0 (next reply.1) reply.2 past := by
        simpa only [empty, List.append_nil] using Reach.step reached supported
      exact ih reply.1 index reply.2 past continued selected

/-- Starting at the actual initial prefix yields its exact supported selected source callback and absolute history length. -/
theorem scan_prefix (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (index : Nat) (state : CtxPrivate n) (past : List (Label n))
    (cut : Cut n X) (selected : Sum.inr cut ∈ support (scan service work index state past)) :
    Reach service work state past
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past ∧
      cut.past.length = past.length + index :=
  scan_reachable service work state past work index state past Reach.initial cut selected

/-- Every supported selected ordinal is strictly below the existing complete syntactic sealing allowance. -/
theorem selected_index_lt (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (index : Nat) (state : CtxPrivate n) (past : List (Label n))
    (bound : Nat)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost work bound)
    (cut : Cut n X) (selected : Sum.inr cut ∈ support (scan service work index state past)) : index < bound := by
  obtain ⟨reached, counted⟩ := scan_prefix service work index state past cut selected
  have small := PqxdhRecordFactsOriginOrdinal.seal_index_lt service bound bounded cut.pending cut.next reached
  omega

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_target

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_prior

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_resume

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_reachable

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.scan_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.selected_index_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut.selected_index_lt
