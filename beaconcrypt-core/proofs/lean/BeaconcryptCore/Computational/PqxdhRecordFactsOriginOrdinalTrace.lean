-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalCut

/-! All attempted sealing cuts in one common original source probability space. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (Service ServiceSpec Sealing)
open PqxdhRecordFactsOriginOrdinalCut (Cut Outcome scan resume)
variable {n : Nat} {X : Type}

abbrev Result (n : Nat) (X : Type) := List (Cut n X) × (X × CtxPrivate n)

/-- Record every attempted sealing cut in source order while returning the complete original final result and state. -/
noncomputable def track (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) : CtxPrivate n → List (Label n) → ProbComp (Result n X) :=
  OracleComp.recOn work
    (fun value state _ => pure ([], (value, state)))
    (fun query next recurse state past => match query with
      | .sealing pending => do
          let reply ← (service (.sealing pending)).run state
          let result ← recurse reply.1 reply.2 (past ++ [pending.material])
          pure (⟨pending, next, state, past⟩ :: result.1, result.2)
      | query => do
          let reply ← (service query).run state
          recurse reply.1 reply.2 past)

/-- Sealing records its cut before the actual reply is drawn, then retains the complete suffix result. -/
theorem track_sealing (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (pending : Sealing n) (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) :
    track service ((ServiceSpec n).query (.sealing pending) >>= next) state past =
      (do let reply ← (service (.sealing pending)).run state
          let result ← track service (next reply.1) reply.2 (past ++ [pending.material])
          pure (⟨pending, next, state, past⟩ :: result.1, result.2)) := rfl

/-- Nonsealing source work executes unchanged and contributes no sealing cut. -/
theorem track_other (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (nonSeal : ∀ pending, query ≠ .sealing pending)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) :
    track service ((ServiceSpec n).query query >>= next) state past =
      ((service query).run state >>= fun reply => track service (next reply.1) reply.2 past) := by
  cases query
  case sealing pending => exact False.elim (nonSeal pending rfl)
  all_goals rfl

/-- Forgetting only the auxiliary cuts restores the full original source execution. -/
theorem track_drop (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n)) :
    Prod.snd <$> track service work state past = (simulateQ service work).run state := by
  induction work using OracleComp.inductionOn generalizing state past with
  | pure value => rfl
  | query_bind query next ih =>
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      rw [track_sealing]
      simp only [map_bind, bind_pure_comp, Functor.map_map, ih, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    · rw [track_other service query (fun pending same => sealed ⟨pending, same⟩)]
      simp only [map_bind, ih, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- Resume a chosen cut while retaining its complete metadata beside the actual final result. -/
noncomputable def markedResume (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) :
    Outcome n X → ProbComp (Option (Cut n X) × (X × CtxPrivate n))
  | .inl result => pure (none, result)
  | .inr cut => (fun result => (some cut, result)) <$> resume service (.inr cut)

/-- The requested cut and full final result are read from one complete source trace. -/
def selected (index : Nat) (result : Result n X) : Option (Cut n X) × (X × CtxPrivate n) :=
  (result.1[index]?, result.2)

/-- The nth cut in the common source trace has exactly the scanner-and-resume joint law. -/
theorem track_selected (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (index : Nat) (state : CtxPrivate n) (past : List (Label n)) :
    selected index <$> track service work state past =
      (scan service work index state past >>= markedResume service) := by
  induction work using OracleComp.inductionOn generalizing index state past with
  | pure value => rfl
  | query_bind query next ih =>
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      cases index with
      | zero =>
        rw [track_sealing, PqxdhRecordFactsOriginOrdinalCut.scan_target]
        simp only [map_bind, map_pure, pure_bind, selected, List.getElem?_cons_zero,
          markedResume, resume]
        apply bind_congr
        intro reply
        have same := congrArg (fun computation =>
          (fun result => (some (Cut.mk pending next state past), result)) <$> computation)
          (track_drop service (next reply.1) reply.2 (past ++ [pending.material]))
        simpa only [bind_pure_comp, Functor.map_map] using same
      | succ index =>
        rw [track_sealing, PqxdhRecordFactsOriginOrdinalCut.scan_prior]
        simp only [map_bind, map_pure, selected, List.getElem?_cons_succ, bind_assoc]
        apply bind_congr
        intro reply
        have same := ih reply.1 index reply.2 (past ++ [pending.material])
        unfold selected at same
        simpa only [bind_pure_comp] using same
    · rw [track_other service query (fun pending same => sealed ⟨pending, same⟩),
        PqxdhRecordFactsOriginOrdinalCut.scan_other service query (fun pending same => sealed ⟨pending, same⟩)]
      simp only [map_bind, ih, bind_assoc]

/-- Every supported complete trace contains at most the original attempted-seal budget, including unsuccessful writer callbacks. -/
theorem track_length (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (bound : Nat)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost work bound)
    (state : CtxPrivate n) (past : List (Label n)) (result : Result n X)
    (supported : result ∈ support (track service work state past)) : result.1.length ≤ bound := by
  induction work using OracleComp.inductionOn generalizing bound state past result with
  | pure value =>
    change result ∈ support (pure ([], (value, state)) : ProbComp (Result n X)) at supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Nat.zero_le _
  | query_bind query next ih =>
    rw [PqxdhRecordLiftCtxProgramBounds.Weighted, isQueryBound_query_bind_iff] at bounded
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      rw [track_sealing] at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨reply, answered, inner, finished, rfl⟩ := supported
      have remaining := ih reply.1 _ (bounded.2 reply.1) reply.2 (past ++ [pending.material]) inner finished
      have positive : 1 ≤ bound := bounded.1
      change inner.1.length ≤ bound - 1 at remaining
      simp only [List.length_cons]
      omega
    · rw [track_other service query (fun pending same => sealed ⟨pending, same⟩)] at supported
      simp only [mem_support_bind_iff] at supported
      obtain ⟨reply, answered, finished⟩ := supported
      have free : PqxdhRecordFactsHashSealBills.sealCost query = 0 := by
        cases query
        case sealing pending => exact False.elim (sealed ⟨pending, rfl⟩)
        all_goals rfl
      simpa only [free, Nat.sub_zero] using ih reply.1 _ (bounded.2 reply.1) reply.2 past result finished

/-- A cut read from a supported common trace has the exact supported prefix and full supported resumed result in the ordinal experiment. -/
theorem track_selected_support (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (index : Nat) (state : CtxPrivate n) (past : List (Label n))
    (result : Result n X) (supported : result ∈ support (track service work state past))
    (cut : Cut n X) (chosen : result.1[index]? = some cut) :
    Sum.inr cut ∈ support (scan service work index state past) ∧
      result.2 ∈ support (resume service (.inr cut)) := by
  have marked : selected index result ∈ support (selected index <$> track service work state past) := by
    simp only [support_map]
    exact ⟨result, supported, rfl⟩
  rw [track_selected] at marked
  simp only [mem_support_bind_iff] at marked
  obtain ⟨outcome, found, finished⟩ := marked
  cases outcome with
  | inl value =>
    simp only [markedResume, support_pure, Set.mem_singleton_iff] at finished
    have impossible := congrArg Prod.fst finished
    simp only [selected, chosen, reduceCtorEq] at impossible
  | inr actual =>
    simp only [markedResume, support_map] at finished
    obtain ⟨value, completed, same⟩ := finished
    have equalCut := congrArg Prod.fst same
    simp only [selected, chosen, Option.some.injEq] at equalCut
    subst actual
    have equalResult := congrArg Prod.snd same
    exact ⟨found, equalResult ▸ completed⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_drop

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_length

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_selected_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace.track_selected_support
