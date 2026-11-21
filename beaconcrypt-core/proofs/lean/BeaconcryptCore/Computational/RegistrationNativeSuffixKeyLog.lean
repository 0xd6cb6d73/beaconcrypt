-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound

/-! The ideal ordinary suffix-key experiment records its actual chronological prefix requests before the continuation, retaining failed or repeated guesses. Its finite list covers the complete reached random-oracle cache and has the actual syntactic query bound. Forgetting this private log recovers the literal ideal PRF experiment. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog
open RegistrationNativeSuffixKeyPrf (Prefix Oracle Spec idealImpl)
variable {Value : Type}
attribute [local irreducible] uniformSample

structure State where
  history : List Prefix
  cache : Oracle.QueryCache

def initial : State := ⟨[], ∅⟩
def Covers (before : State) : Prop := ∀ head, before.cache head ≠ none → head ∈ before.history

def IsQuery : Spec.Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred IsQuery
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

noncomputable def handler : QueryImpl Spec (StateT State ProbComp)
  | .inl coin => fun before => (fun reply => (reply, before)) <$> unifSpec.query coin
  | .inr head => fun before => (fun result => (result.1, ⟨before.history ++ [head], result.2⟩)) <$>
      (Oracle.randomOracle head).run before.cache

private theorem read_domain (head : Prefix) (before : Oracle.QueryCache) (result : Oracle.Range head × Oracle.QueryCache)
    (supported : result ∈ support ((Oracle.randomOracle head).run before))
    (key : Prefix) (cached : result.2 key ≠ none) : key = head ∨ before key ≠ none := by
  by_cases same : key = head
  · exact Or.inl same
  · right
    cases found : before head with
    | some answer =>
        rw [QueryImpl.withCaching_run_some _ found, mem_support_pure_iff] at supported
        cases supported
        exact cached
    | none =>
        rw [QueryImpl.withCaching_run_none _ found, support_map] at supported
        obtain ⟨answer, _sampled, equal⟩ := supported
        cases equal
        rwa [QueryCache.cacheQuery_of_ne _ _ same] at cached

/-- Empty cold ideal execution has complete cache coverage. -/
theorem initial_covers : Covers initial := by
  intro head cached
  exact (cached rfl).elim

/-- Every actual ideal callback preserves coverage by its own chronological query list. -/
theorem query_covers (query : Spec.Domain) (before : State) (result : Spec.Range query × State)
    (covered : Covers before) (supported : result ∈ support ((handler query).run before)) : Covers result.2 := by
  cases query with
  | inl coin =>
      simp only [handler, StateT.run, support_map] at supported
      obtain ⟨reply, _possible, equal⟩ := supported
      cases equal
      exact covered
  | inr head =>
      simp only [handler, StateT.run, support_map] at supported
      obtain ⟨reached, possible, equal⟩ := supported
      cases equal
      intro key cached
      rcases read_domain head before.cache reached possible key cached with same | previous
      · exact List.mem_append_right before.history (by simp [same])
      · exact List.mem_append_left _ (covered key previous)

/-- One ideal callback adds exactly one address only when it actually queries the PRF oracle. -/
theorem query_count (query : Spec.Domain) (before : State) (result : Spec.Range query × State)
    (supported : result ∈ support ((handler query).run before)) :
    result.2.history.length = before.history.length + if IsQuery query then 1 else 0 := by
  cases query <;> simp only [handler, StateT.run, support_map] at supported
  all_goals obtain ⟨reached, _possible, equal⟩ := supported; cases equal
  · rfl
  · simp only [List.length_append, List.length_singleton, IsQuery, ite_true]

/-- Every supported adaptive ideal execution has its entire reached cache covered by its own actual query list. -/
theorem program_covers (work : OracleComp Spec Value) (before : State) (result : Value × State)
    (covered : Covers before) (supported : result ∈ support ((simulateQ handler work).run before)) : Covers result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact covered
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact ih middle.1 middle.2 (query_covers query before middle covered reached) continued

/-- The reached chronological list inherits the ordinary adversary's actual PRF-query cap. -/
theorem program_count (work : OracleComp Spec Value) (count : Nat) (bounded : work.IsQueryBoundP IsQuery count)
    (before : State) (result : Value × State) (supported : result ∈ support ((simulateQ handler work).run before)) :
    result.2.history.length ≤ before.history.length + count := by
  apply bounded.cost_le_of_mem_support_run_simulateQ (fun state : State => state.history.length) _ _ before result supported
  · intro query counted current reached possible
    have step := query_count query current reached possible
    simp only [ite_eq_left counted] at step
    exact step.le
  · intro query free current reached possible
    have step := query_count query current reached possible
    simp only [ite_eq_right free, Nat.add_zero] at step
    exact step.le

/-- Forgetting the private log retains the literal ideal oracle's complete answer and cache poststate. -/
theorem query_source (query : Spec.Domain) (before : State) :
    Prod.map id State.cache <$> (handler query).run before = (idealImpl query).run before.cache := by
  cases query with
  | inl coin => simp only [handler, StateT.run, Functor.map_map, Prod.map_def, id_eq]; rfl
  | inr head =>
      simp only [handler, StateT.run, Functor.map_map, Prod.map_def, id_eq]
      have eta : (fun result : PqxdhServerAuthKeySchedule.Output × Oracle.QueryCache => (result.1, result.2)) = id := by
        funext result
        cases result
        rfl
      rw [eta, id_map]
      rfl

/-- The full adaptive ideal game is unchanged by chronological logging, including its complete random-oracle cache. -/
theorem program_source (work : OracleComp Spec Value) (before : State) :
    Prod.map id State.cache <$> (simulateQ handler work).run before = (simulateQ idealImpl work).run before.cache := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query_source query before, bind_map_left]
      exact bind_congr fun reached => ih reached.1 reached.2

end BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.initial_covers' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.initial_covers
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.query_covers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.query_covers
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.query_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.query_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.program_covers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.program_covers
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.program_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.program_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog.program_source
