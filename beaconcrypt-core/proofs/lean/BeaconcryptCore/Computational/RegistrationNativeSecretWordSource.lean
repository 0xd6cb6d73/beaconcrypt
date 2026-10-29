-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWord

/-! The normalized symbolic service is the actual byte-indexed lazy table under the literal192-byte evaluation. The cache lens retains every queried byte and its actual answer; bytes outside the192-byte slice are absent from this client. No collision bound or final-event assumption is used by this operational identification. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordSource
open RegistrationNativeSecretWord (Key Spec Cache eval normalize decode symbolic actual)
open PqxdhKemIndCca (MlKemSharedSecret)
open PqxdhServerAuthKeySchedule (Output)
variable {Value : Type}

abbrev ByteCache := (Pqxdh.Bytes →ₒ Output).QueryCache

def byteCache (candidate : MlKemSharedSecret) (cache : Cache) : ByteCache :=
  QueryCache.ofFn fun bytes => (decode candidate bytes).bind fun key => cache key

noncomputable def byteSource (candidate : MlKemSharedSecret) : QueryImpl Spec (StateT ByteCache ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr key => (Pqxdh.Bytes →ₒ Output).randomOracle (eval candidate key)

/-- The byte cache reads the exact normalized symbolic cell for every native evaluated key. -/
theorem cache_eval (candidate : MlKemSharedSecret) (cache : Cache) (key : Key) :
    byteCache candidate cache (eval candidate key) = cache (normalize candidate key) := by
  simp only [byteCache, QueryCache.ofFn, RegistrationNativeSecretWord.decode_eval, Option.bind_some]

/-- Updating the actual normalized cell changes precisely the corresponding native192-byte cache entry. -/
theorem cache_update (candidate : MlKemSharedSecret) (cache : Cache) (key : Key) (answer : Output) :
    byteCache candidate (cache.cacheQuery (normalize candidate key) answer) =
      (byteCache candidate cache).cacheQuery (eval candidate key) answer := by
  apply QueryCache.ext
  intro bytes
  by_cases same : bytes = eval candidate key
  · subst bytes
    rw [cache_eval, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    change (decode candidate bytes).bind (fun point => cache.cacheQuery (normalize candidate key) answer point) =
      (decode candidate bytes).bind (fun point => cache point)
    cases parsed : decode candidate bytes with
    | none => rfl
    | some point =>
        have different : point ≠ normalize candidate key := by
          intro equal
          have bytesRun := RegistrationNativeSecretWord.decode_some candidate bytes point parsed
          rw [equal, RegistrationNativeSecretWord.eval_normalize] at bytesRun
          exact same bytesRun.symm
        exact QueryCache.cacheQuery_of_ne cache answer different

/-- Each normalized symbolic query retains the actual byte-oracle answer and full projected cache. -/
theorem query_source (candidate : MlKemSharedSecret) (query : Spec.Domain) (cache : Cache) :
    Prod.map id (byteCache candidate) <$> (actual candidate query).run cache =
      (byteSource candidate query).run (byteCache candidate cache) := by
  cases query with
  | inl coin =>
      simp only [actual, symbolic, RegistrationNativeG3CellEager.lazy, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, byteSource, StateT.run_lift,
        bind_pure_comp]
      rfl
  | inr key =>
      change Prod.map id (byteCache candidate) <$>
        ((Key →ₒ Output).randomOracle (normalize candidate key)).run cache =
          ((Pqxdh.Bytes →ₒ Output).randomOracle (eval candidate key)).run (byteCache candidate cache)
      cases found : cache (normalize candidate key) with
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ found,
            QueryImpl.withCaching_run_some _ ((cache_eval candidate cache key).trans found), map_pure]
          rfl
      | none =>
          rw [QueryImpl.withCaching_run_none _ found,
            QueryImpl.withCaching_run_none _ ((cache_eval candidate cache key).trans found), Functor.map_map]
          congr 1
          funext answer
          exact Prod.ext rfl (cache_update candidate cache key answer)

/-- Arbitrary adaptive coin/key programs retain their complete native byte-cache outcomes under the concrete source lens. -/
theorem program_source (candidate : MlKemSharedSecret) (work : OracleComp Spec Value) (cache : Cache) :
    Prod.map id (byteCache candidate) <$> (simulateQ (actual candidate) work).run cache =
      (simulateQ (byteSource candidate) work).run (byteCache candidate cache) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (byteCache candidate) (query_source candidate) work cache

/-- Empty actual native byte-table execution equals the normalized symbolic execution, without a goodness or no-alias premise. -/
theorem values_source (candidate : MlKemSharedSecret) (work : OracleComp Spec Value) :
    (simulateQ (actual candidate) work).run' ∅ = (simulateQ (byteSource candidate) work).run' ∅ := by
  have projected := congrArg (Functor.map Prod.fst) (program_source candidate work ∅)
  have empty : byteCache candidate ∅ = ∅ := by
    apply QueryCache.ext
    intro bytes
    change (decode candidate bytes).bind (fun _ => none) = none
    cases decode candidate bytes <;> rfl
  rw [empty] at projected
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map, id_eq] using projected

end BeaconcryptCore.Computational.RegistrationNativeSecretWordSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.cache_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.cache_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.cache_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.cache_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.values_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordSource.values_source
