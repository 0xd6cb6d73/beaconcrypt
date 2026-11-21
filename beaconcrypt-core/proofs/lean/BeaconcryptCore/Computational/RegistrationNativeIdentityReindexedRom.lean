-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom

/-! A private realization may represent an entire family of hidden addresses by public symbolic keys. A right inverse on physical addresses and a left inverse at the actually admitted symbolic queries preserve the complete lazy cache, aliases and true draw counts. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom
open RegistrationNativeIdentitySymbolicRom (cached counted)
variable {Physical Symbolic R Value : Type} [DecidableEq Physical] [DecidableEq Symbolic]

/-- Only the private interpretation receives this physical-address abstraction. -/
def project (abstract : Physical → Symbolic) (cache : (Symbolic →ₒ R).QueryCache) : (Physical →ₒ R).QueryCache :=
  ⟨fun input => cache (abstract input)⟩

omit [DecidableEq Physical] [DecidableEq Symbolic] in
private theorem abstract_eq (realize : Symbolic → Physical) (abstract : Physical → Symbolic)
    (rightInverse : ∀ input, realize (abstract input) = input) (query : Symbolic)
    (allowed : abstract (realize query) = query) (input : Physical) :
    abstract input = query ↔ input = realize query := by
  constructor
  · intro same
    rw [← rightInverse input, same]
  · intro same
    rw [same, allowed]

private theorem update (realize : Symbolic → Physical) (abstract : Physical → Symbolic)
    (rightInverse : ∀ input, realize (abstract input) = input) (query : Symbolic)
    (allowed : abstract (realize query) = query) (cache : (Symbolic →ₒ R).QueryCache) (answer : R) :
    project abstract (cache.cacheQuery query answer) = (project abstract cache).cacheQuery (realize query) answer := by
  apply QueryCache.ext
  intro input
  change Function.update cache query (some answer) (abstract input) =
    Function.update (project abstract cache) (realize query) (some answer) input
  by_cases same : input = realize query
  · rw [same, allowed, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ((abstract_eq realize abstract rightInverse query allowed input).not.mpr same), Function.update_of_ne same]
    rfl

/-- One admitted symbolic query has the literal physical reply and full privately realized cache. -/
theorem query_source (sampler : ProbComp R) (realize : Symbolic → Physical) (abstract : Physical → Symbolic)
    (rightInverse : ∀ input, realize (abstract input) = input) (query : Symbolic)
    (allowed : abstract (realize query) = query) (cache : (Symbolic →ₒ R).QueryCache) :
    Prod.map id (project abstract) <$> (cached sampler query).run cache =
      (cached sampler (realize query)).run (project abstract cache) := by
  have physical : project abstract cache (realize query) = cache query := by
    change cache (abstract (realize query)) = cache query
    rw [allowed]
  unfold cached
  cases found : cache query with
  | none =>
    rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ (physical.trans found)]
    simp only [Functor.map_map, Prod.map_def, id_eq]
    congr 1
    funext answer
    rw [update realize abstract rightInverse query allowed cache answer]
  | some answer =>
    rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ (physical.trans found), map_pure]
    rfl

private theorem map_apply {State A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT State m A) (before : State) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The same reindexing preserves each actual ROM draw count as well as its digest and complete cache. -/
theorem counted_source (sampler : ProbComp R) (realize : Symbolic → Physical) (abstract : Physical → Symbolic)
    (rightInverse : ∀ input, realize (abstract input) = input) (query : Symbolic)
    (allowed : abstract (realize query) = query) (cache : (Symbolic →ₒ R).QueryCache) :
    Prod.map id (project abstract) <$> (counted sampler query).run cache =
      (counted sampler (realize query)).run (project abstract cache) := by
  have interpreted := congrArg (fun work => (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0)
    (query_source sampler realize abstract rightInverse query allowed cache)
  have observed := congrArg (fun distribution => (fun result => ((result.1.1, result.2), result.1.2)) <$> distribution) interpreted
  simp only [counted, StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map_def, id_eq] at observed ⊢
  exact observed

/-- Arbitrary adaptive admitted symbolic queries share one physical cache with all original aliases and exact per-call costs. -/
theorem program_source (sampler : ProbComp R) (realize : Symbolic → Physical) (abstract : Physical → Symbolic)
    (rightInverse : ∀ input, realize (abstract input) = input) (work : OracleComp (Symbolic →ₒ (R × Nat)) Value)
    (allowed : work.AllQueriesSatisfy (fun query => abstract (realize query) = query))
    (cache : (Symbolic →ₒ R).QueryCache) :
    Prod.map id (project abstract) <$> (simulateQ (counted sampler) work).run cache =
      (simulateQ (fun query => counted sampler (realize query)) work).run (project abstract cache) := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← counted_source sampler realize abstract rightInverse query first]
    rw [bind_map_left]
    exact bind_congr (fun result => ih result.1 (later result.1) result.2)

end BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom.query_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom.counted_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom.counted_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom.program_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedRom.program_source
