-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom

/-! Before adaptive selection the symbolic ROM uses only some addresses. This entire adaptive prefix is exactly the original physical ROM, even if a retrospectively chosen hidden template was already queried. The none entry is irrelevant to this source projection; the later recognition scan separately decides whether a fresh hidden token can be installed. No earlier forbidden-address or cache-miss premise is assumed here. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic
open RegistrationNativeIdentitySymbolicRom (cached counted)
variable {D R Value : Type} [DecidableEq D]

def project (before : (Option D →ₒ R).QueryCache) : (D →ₒ R).QueryCache :=
  ⟨fun input => before (some input)⟩

private theorem update (before : (Option D →ₒ R).QueryCache) (input : D) (answer : R) :
    project (before.cacheQuery (some input) answer) = (project before).cacheQuery input answer := by
  apply QueryCache.ext
  intro other
  by_cases same : other = input
  · subst other
    exact (QueryCache.cacheQuery_self before (some input) answer).trans
      (QueryCache.cacheQuery_self (project before) input answer).symm
  · change (before.cacheQuery (some input) answer) (some other) =
      ((project before).cacheQuery input answer) other
    rw [QueryCache.cacheQuery_of_ne _ _ (fun equal => same (Option.some.inj equal)),
      QueryCache.cacheQuery_of_ne _ _ same]
    rfl

/-- Every public address has exactly its original cache lookup, source sampler and physical cache update. -/
theorem query (sampler : ProbComp R) (before : (Option D →ₒ R).QueryCache) (input : D) :
    Prod.map id project <$> (cached sampler (some input)).run before =
      (cached sampler input).run (project before) := by
  have lookup : project before input = before (some input) := rfl
  unfold cached
  cases found : before (some input) with
  | none =>
    rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ (lookup.trans found)]
    simp only [Functor.map_map, Prod.map_def, id_eq]
    congr 1
    funext answer
    rw [update]
  | some answer =>
    rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ (lookup.trans found), map_pure]
    rfl

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- Public-prefix reindexing retains each literal source draw charge, including zero-cost repeated queries. -/
theorem cost (sampler : ProbComp R) (before : (Option D →ₒ R).QueryCache) (input : D) :
    Prod.map id project <$> (counted sampler (some input)).run before =
      (counted sampler input).run (project before) := by
  have interpreted := congrArg (fun work => (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0)
    (query sampler before input)
  have observed := congrArg (fun distribution => (fun result => ((result.1.1, result.2), result.1.2)) <$> distribution) interpreted
  simp only [counted, StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map_def, id_eq] at observed ⊢
  exact observed

/-- The full adaptive public-address prefix couples before the target message is known, without any hidden-address argument or prior-query restriction. -/
theorem program (sampler : ProbComp R) (work : OracleComp (D →ₒ (R × Nat)) Value)
    (before : (Option D →ₒ R).QueryCache) :
    Prod.map id project <$> (simulateQ (fun input => counted sampler (some input)) work).run before =
      (simulateQ (counted sampler) work).run (project before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
  exact fun input current => cost sampler current input

end BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic.query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic.cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic.cost
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic.program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicPublic.program
