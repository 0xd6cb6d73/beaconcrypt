-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CtxRomAuth
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-! A hidden random-oracle address is represented by one executable symbolic token, without storing that address in the client cache. Every repeated token query aliases the same cached answer. Only the private source projection receives the actual address; public queries must be stopped on recognition before that address is submitted. The lemmas here do not assume or establish the native recognition/coverage theorem. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom
variable {D R Value : Type} [DecidableEq D]

abbrev PhysicalSpec (D R : Type) := D →ₒ R
abbrev SymbolicSpec (D R : Type) := Option D →ₒ R

def address (hidden : D) : Option D → D
  | none => hidden
  | some input => input

def abstractAddress (hidden input : D) : Option D := if input = hidden then none else some input

/-- A private interpretation restores the symbolic token at its actual physical address. -/
def project (hidden : D) (cache : (SymbolicSpec D R).QueryCache) : (PhysicalSpec D R).QueryCache :=
  ⟨fun input => cache (abstractAddress hidden input)⟩

private theorem address_abstract (hidden input : D) : address hidden (abstractAddress hidden input) = input := by
  by_cases same : input = hidden
  · simp only [abstractAddress, same, ite_true, address]
  · simp only [abstractAddress, same, ite_false, address]

private theorem abstract_address (hidden : D) (query : Option D) (permitted : query ≠ some hidden) :
    abstractAddress hidden (address hidden query) = query := by
  cases query with
  | none => simp only [address, abstractAddress, ite_true]
  | some input =>
    have different : input ≠ hidden := fun same => permitted (congrArg some same)
    simp only [address, abstractAddress, different, ite_false]

private theorem abstract_eq (hidden input : D) (query : Option D) (permitted : query ≠ some hidden) :
    abstractAddress hidden input = query ↔ input = address hidden query := by
  constructor
  · intro same
    rw [← address_abstract hidden input, same]
  · intro same
    rw [same, abstract_address hidden query permitted]

/-- Symbolic and physical lookup agree at every token or unrecognized public address. -/
theorem lookup (hidden : D) (cache : (SymbolicSpec D R).QueryCache) (query : Option D)
    (permitted : query ≠ some hidden) : project hidden cache (address hidden query) = cache query := by
  change cache (abstractAddress hidden (address hidden query)) = cache query
  rw [abstract_address hidden query permitted]

/-- A physical cache update is the exact private realization of the same symbolic update, preserving all repeated-address aliases. -/
theorem update (hidden : D) (cache : (SymbolicSpec D R).QueryCache) (query : Option D) (answer : R)
    (permitted : query ≠ some hidden) :
    project hidden (cache.cacheQuery query answer) = (project hidden cache).cacheQuery (address hidden query) answer := by
  apply QueryCache.ext
  intro input
  change Function.update cache query (some answer) (abstractAddress hidden input) =
    Function.update (project hidden cache) (address hidden query) (some answer) input
  by_cases same : input = address hidden query
  · rw [same, abstract_address hidden query permitted, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ((abstract_eq hidden input query permitted).not.mpr same), Function.update_of_ne same]
    rfl

/-- Both physical and symbolic lazy tables use the identical actual sampler. The symbolic none input is an opaque address token. -/
def cached (sampler : ProbComp R) : QueryImpl (PhysicalSpec D R) (StateT (PhysicalSpec D R).QueryCache ProbComp) :=
  QueryImpl.withCaching (spec := PhysicalSpec D R) (fun _ => sampler)

/-- One complete actual token or unrecognized public query has exactly the same sampler/cached reply and privately realized source cache. -/
theorem query_source (sampler : ProbComp R) (hidden : D) (cache : (SymbolicSpec D R).QueryCache)
    (query : Option D) (permitted : query ≠ some hidden) :
    Prod.map id (project hidden) <$> (cached sampler query).run cache =
      (cached sampler (address hidden query)).run (project hidden cache) := by
  have physical := lookup hidden cache query permitted
  unfold cached
  cases found : cache query with
  | none =>
    rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ (physical.trans found)]
    simp only [Functor.map_map, Prod.map, id_eq]
    congr 1
    funext answer
    rw [update hidden cache query answer permitted]
  | some answer =>
    rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ (physical.trans found), map_pure]
    rfl

/-- A repeated suppressed attempt reuses the same symbolic answer and consumes no fresh uniform draw. -/
theorem token_alias (sampler : ProbComp R) (cache : (SymbolicSpec D R).QueryCache) (answer : R) :
    (cached sampler none).run (cache.cacheQuery none answer) = pure (answer, cache.cacheQuery none answer) :=
  QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self cache none answer)

/-- A full adaptive symbolic tree is realized by physical lazy queries at the same actual address, provided recognition stops forbidden public lookups. This is an OracleComp equality, not merely an event marginal. -/
theorem program_source (sampler : ProbComp R) (hidden : D) (work : OracleComp (SymbolicSpec D R) Value)
    (permitted : AllQueriesSatisfy work (fun query => query ≠ some hidden)) (cache : (SymbolicSpec D R).QueryCache) :
    Prod.map id (project hidden) <$> (simulateQ (cached sampler) work).run cache =
      (simulateQ (fun query => cached sampler (address hidden query)) work).run (project hidden cache) := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id_eq]
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp permitted
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query_source sampler hidden cache query first]
    rw [bind_map_left]
    exact bind_congr (fun result => ih result.1 (later result.1) result.2)


private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The capability returns each actual call's draw count; only digest answers are cached. -/
def counted (sampler : ProbComp R) : QueryImpl (D →ₒ (R × Nat))
    (StateT (PhysicalSpec D R).QueryCache ProbComp) := fun query cache =>
  (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ PqxdhRecordLiftWorld.countCoin ((cached sampler query).run cache)).run 0

/-- Private token realization preserves the exact per-call random-oracle draw count as well as digest and complete cache. -/
theorem counted_source (sampler : ProbComp R) (hidden : D) (cache : (SymbolicSpec D R).QueryCache)
    (query : Option D) (permitted : query ≠ some hidden) :
    Prod.map id (project hidden) <$> (counted sampler query).run cache =
      (counted sampler (address hidden query)).run (project hidden cache) := by
  have interpreted := congrArg (fun work => (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0)
    (query_source sampler hidden cache query permitted)
  have observed := congrArg (fun distribution => (fun result => ((result.1.1, result.2), result.1.2)) <$> distribution) interpreted
  simp only [counted, StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map, id_eq] at observed ⊢
  exact observed

/-- Repeating the same hidden-address token returns its cached digest with the literal zero source draw cost. -/
theorem counted_alias (sampler : ProbComp R) (cache : (SymbolicSpec D R).QueryCache) (answer : R) :
    (counted sampler none).run (cache.cacheQuery none answer) = pure ((answer, 0), cache.cacheQuery none answer) := by
  change (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ PqxdhRecordLiftWorld.countCoin ((cached sampler none).run (cache.cacheQuery none answer))).run 0 = _
  rw [token_alias]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]

end BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.lookup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.query_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.token_alias' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.token_alias
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.program_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.counted_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.counted_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.counted_alias' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom.counted_alias
