-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordService
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace

/-! The concrete ordinary suffix-key adversary simulates the whole symbolic key table locally, logs every literal table suffix, and forwards only the additional suffix-key calls to its oracle. Its executable code has no candidate bytes. Closing that oracle with its real key reproduces the exact combined symbolic execution, including its complete table and chronological literal list. Query and list bills follow from the original combined AST, rather than an independence claim about real side information. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWord (Cache symbolic)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {Value : Type}
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value

abbrev State := Cache × List Secret

def IsKey : Combined.Domain → Prop
  | .inl query => RegistrationNativeSecretWord.IsKey query
  | .inr _ => False

def IsSuffix : Combined.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsKey
  | .inl query => inferInstanceAs (Decidable (RegistrationNativeSecretWord.IsKey query))
  | .inr _ => inferInstanceAs (Decidable False)

instance : DecidablePred IsSuffix
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

def literals : Combined.Domain → List Secret
  | .inl query => RegistrationNativeSecretWord.literals query
  | .inr _ => []

def coins : QueryImpl unifSpec (OracleComp RegistrationNativeSuffixKeyPrf.Spec) :=
  fun coin => RegistrationNativeSuffixKeyPrf.Spec.query (.inl coin)

noncomputable def compiler : QueryImpl Combined (StateT State (OracleComp RegistrationNativeSuffixKeyPrf.Spec))
  | .inl query => fun before =>
      (fun result => (result.1, (result.2, before.2 ++ RegistrationNativeSecretWord.literals query))) <$>
        simulateQ coins ((symbolic query).run before.1)
  | .inr head => fun before =>
      (fun reply => (reply, before)) <$> RegistrationNativeSuffixKeyPrf.Spec.query (.inr head)

noncomputable def run (work : OracleComp Combined Value) :
    OracleComp RegistrationNativeSuffixKeyPrf.Spec (Value × State) :=
  (simulateQ compiler work).run (∅, [])

noncomputable def guesses (work : OracleComp Combined Value) : OracleComp RegistrationNativeSuffixKeyPrf.Spec (List Secret) :=
  (fun result => result.2.2) <$> run work

noncomputable def closed (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    QueryImpl Combined (StateT Cache ProbComp)
  | .inl query => symbolic query
  | .inr head => fun before => pure (RegistrationNativeSuffixKeyPrf.value source candidate head, before)

private theorem coins_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) (work : ProbComp Value) :
    simulateQ (RegistrationNativeSuffixKeyPrf.realImpl source candidate) (simulateQ coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeSuffixKeyPrf.realImpl source candidate ∘ₛ coins = QueryImpl.ofLift unifSpec ProbComp := by
    funext query
    rfl
  rw [same, simulateQ_ofLift_eq_self]

/-- Closing one compiled callback with the actual primitive key retains its complete symbolic cache and literal trace. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (query : Combined.Domain) (before : State) :
    simulateQ (RegistrationNativeSuffixKeyPrf.realImpl source candidate) ((compiler query).run before) =
      (RawCtxSelectedQueryTrace.recorded (closed source candidate) literals query).run before := by
  cases query with
  | inl query =>
      simp only [compiler, StateT.run, simulateQ_map, coins_source, RawCtxSelectedQueryTrace.recorded,
        closed, literals, bind_pure_comp]
      rfl
  | inr head =>
      simp only [compiler, StateT.run, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeSuffixKeyPrf.realImpl, map_pure, RawCtxSelectedQueryTrace.recorded,
        closed, literals, pure_bind, List.append_nil]

/-- The ordinary reduction reproduces the entire actual combined execution under the real suffix-key oracle. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) (before : State) :
    simulateQ (RegistrationNativeSuffixKeyPrf.realImpl source candidate) ((simulateQ compiler work).run before) =
      (simulateQ (RawCtxSelectedQueryTrace.recorded (closed source candidate) literals) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [← query_source source candidate query before]
      exact bind_congr fun reached => ih reached.1 reached.2

private theorem coin_free (work : ProbComp Value) :
    (simulateQ coins work).IsQueryBoundP RegistrationNativeSuffixKeyLog.IsQuery 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, coins, isQueryBoundP_query_bind_iff,
        RegistrationNativeSuffixKeyLog.IsQuery, ite_false, not_false_eq_true, true_or, true_and]
      intro reply
      exact ih reply

/-- Local symbolic-table randomness contributes no query to the external suffix-key oracle. -/
theorem query_bound (query : Combined.Domain) (before : State) :
    ((compiler query).run before).IsQueryBoundP RegistrationNativeSuffixKeyLog.IsQuery
      (if IsSuffix query then 1 else 0) := by
  cases query with
  | inl query =>
      simpa only [compiler, StateT.run, IsSuffix, ite_false, isQueryBoundP_map_iff] using
        coin_free ((symbolic query).run before.1)
  | inr head => simp only [compiler, StateT.run, IsSuffix, ite_true, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff, RegistrationNativeSuffixKeyLog.IsQuery, Nat.zero_lt_one, implies_true]

/-- The complete ordinary recovery adversary pays exactly the original combined suffix-key query allowance. -/
theorem guesses_bound (work : OracleComp Combined Value) (cap : Nat) (bounded : work.IsQueryBoundP IsSuffix cap) :
    (guesses work).IsQueryBoundP RegistrationNativeSuffixKeyLog.IsQuery cap := by
  simp only [guesses, run, isQueryBoundP_map_iff]
  exact bounded.simulateQ_run_of_step
    (fun query selected before => by simpa only [ite_eq_left selected] using query_bound query before)
    (fun query unselected before => by simpa only [ite_eq_right unselected] using query_bound query before) (∅, [])

private theorem literal_length (query : Combined.Domain) :
    (literals query).length ≤ if IsKey query then 1 else 0 := by
  rcases query with (coin | ⟨head, word⟩) | head
  · simp only [literals, RegistrationNativeSecretWord.literals, IsKey, RegistrationNativeSecretWord.IsKey, ite_false, List.length_nil, le_refl]
  · cases word <;> simp [literals, RegistrationNativeSecretWord.literals, IsKey, RegistrationNativeSecretWord.IsKey]
  · simp [literals, IsKey]

private theorem query_length (query : Combined.Domain) (before : State)
    (result : Combined.Range query × State) (supported : result ∈ support ((compiler query).run before)) :
    result.2.2.length ≤ before.2.length + if IsKey query then 1 else 0 := by
  cases query with
  | inl query =>
      simp only [compiler, StateT.run, support_map] at supported
      obtain ⟨reached, _possible, equal⟩ := supported
      cases equal
      have bound := literal_length (.inl query)
      simp only [literals] at bound
      simpa only [List.length_append] using Nat.add_le_add_left bound before.2.length
  | inr head =>
      simp only [compiler, StateT.run, support_map] at supported
      obtain ⟨reply, _possible, equal⟩ := supported
      cases equal
      simp only [IsKey, ite_false, Nat.add_zero, le_refl]

/-- Every supported reduction AST returns only the original key-query allowance of literal guesses, including repeated and failed requests. -/
theorem program_length (work : OracleComp Combined Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap)
    (before : State) (result : Value × State) (supported : result ∈ support ((simulateQ compiler work).run before)) :
    result.2.2.length ≤ before.2.length + cap := by
  induction work using OracleComp.inductionOn generalizing before cap result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact Nat.le_add_right _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reached, step, tail⟩ := supported
      have leading := query_length query before reached step
      have rest := ih reached.1 _ (bounded.2 reached.1) reached.2 result tail
      have available := bounded.1
      by_cases selected : IsKey query
      · simp only [selected, ite_true, not_true_eq_false, false_or] at leading available rest
        omega
      · simp only [selected, ite_false] at leading available rest
        omega

/-- The terminal checker receives a list bounded on every bare oracle-program branch, so no sampled-oracle premise is needed. -/
theorem guesses_length (work : OracleComp Combined Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap)
    (list : List Secret) (supported : list ∈ support (guesses work)) : list.length ≤ cap := by
  simp only [guesses, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  cases equal
  have count := program_length work cap bounded (∅, []) result reached
  simpa only [List.length_nil, Nat.zero_add] using count

end BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.query_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.guesses_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.guesses_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.program_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.program_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.guesses_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler.guesses_length
