import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility
import BeaconcryptCore.Computational.VCVioForwardOracleComp
import BeaconcryptCore.Computational.VCVioLegacyBridge

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.JointEagerTable

variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)] [MeasurableSpace R]
  [DiscreteMeasurableSpace R]

/-- Complete the final lazy cache with an independent uniform tail, retaining the total table jointly with the actual client result. This finite total table is analysis only. -/
def completedLazy {Result : Type} (client : OracleComp (D →ₒ R) Result)
    (cache : (D →ₒ R).QueryCache) : ProbComp ((D → R) × Result) := do
  let result ← (simulateQ randomOracle client).run cache
  let tail ← $ᵗ (D → R)
  pure (tableExtending result.2 tail, result.1)

/-- Deferred sampling preserves the entire sampled answer function jointly with the evaluated client result, from every preexisting cache. -/
theorem completedLazy_eq_eager {Result : Type} [MeasurableSpace Result]
    (client : OracleComp (D →ₒ R) Result)
    (cache : (D →ₒ R).QueryCache) :
    𝒟[completedLazy client cache] =
      𝒟[do
        let tail ← $ᵗ (D → R)
        let table := tableExtending cache tail
        pure (table, evalWithAnswerFn (QueryImpl.ofFn table) client)] := by
  induction client using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp [completedLazy, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]
  | query_bind query next ih =>
    classical
    let := Fintype.ofFinite R
    have : Nonempty (D → R) := ⟨fun _ => Classical.arbitrary R⟩
    have reduce : completedLazy (liftM ((D →ₒ R).query query) >>= next) cache =
        (randomOracle (spec := D →ₒ R) query).run cache >>= fun reply =>
          completedLazy (next reply.1) reply.2 := by
      simp only [completedLazy, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    have evaluate (tail : D → R) :
        evalWithAnswerFn (QueryImpl.ofFn (tableExtending cache tail))
          (liftM ((D →ₒ R).query query) >>= next) =
        evalWithAnswerFn (QueryImpl.ofFn (tableExtending cache tail))
          (next (tableExtending cache tail query)) := by
      rw [evalWithAnswerFn_bind]
      simp only [evalWithAnswerFn, simulateQ_spec_query, QueryImpl.ofFn_apply]
    rw [reduce]
    simp_rw [evaluate]
    cases cached : cache query with
    | none =>
      rw [QueryImpl.withCaching_run_none _ cached, map_eq_bind_pure_comp]
      simp only [Function.comp_def, bind_assoc, pure_bind]
      let observation : (D → R) → (D → R) × Result := fun tail =>
        (tableExtending cache tail,
          evalWithAnswerFn (QueryImpl.ofFn (tableExtending cache tail))
            (next (tableExtending cache tail query)))
      have updated (answer : R) :
          (fun tail : D → R =>
            (tableExtending (cache.cacheQuery query answer) tail,
              evalWithAnswerFn (QueryImpl.ofFn (tableExtending (cache.cacheQuery query answer) tail))
                (next answer))) =
          fun tail => observation (Function.update tail query answer) := by
        funext tail
        simp only [observation]
        rw [tableExtending_cacheQuery, ← tableExtending_update_of_none cache tail cached answer]
        simp only [Function.update_self]
      trans 𝒟[do
        let answer ← $ᵗ R
        let tail ← $ᵗ (D → R)
        pure (observation (Function.update tail query answer))]
      · rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
        apply MeasureTheory.Measure.bind_congr_right
        filter_upwards [] with answer
        rw [ih answer (cache.cacheQuery query answer), bind_pure_comp, bind_pure_comp, updated answer]
      · exact evalDist_uniformSample_bind_update_map SampleableType.evalDist_uniformSample
          SampleableType.evalDist_uniformSample query observation
    | some answer =>
      rw [QueryImpl.withCaching_run_some _ cached, pure_bind, ih answer cache]
      have hit (tail : D → R) : tableExtending cache tail query = answer := by
        simp [tableExtending, cached]
      simp_rw [hit]

/-- From an empty dictionary the retained completed lazy table has exactly the joint law of an upfront uniform table and the client's deterministic evaluation against that same table. -/
theorem completedLazy_empty_eq_uniform {Result : Type} [MeasurableSpace Result]
    (client : OracleComp (D →ₒ R) Result) :
    𝒟[completedLazy client ∅] =
      𝒟[do
        let table ← $ᵗ (D → R)
        pure (table, evalWithAnswerFn (QueryImpl.ofFn table) client)] := by
  rw [completedLazy_eq_eager]
  simp only [tableExtending_empty]

/-- Absorbing a fresh cell into the uniform full table preserves every complete probabilistic continuation. -/
theorem uniform_update_bind {Result : Type} [MeasurableSpace Result]
    (query : D) (next : (D → R) → ProbComp Result) :
    𝒟[do
      let answer ← $ᵗ R
      let table ← $ᵗ (D → R)
      next (Function.update table query answer)] =
      𝒟[($ᵗ (D → R)) >>= next] := by
  exact evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample query next

/-- Only independent explicit samplers are reordered, with their complete following computation retained. -/
theorem independent_comm_spmf {A B Result : Type}
    (left : ProbComp A) (right : ProbComp B)
    (next : A → B → ProbComp Result) :
    EvalDistEq (left >>= fun a => right >>= next a)
      (right >>= fun b => left >>= fun a => next a b) :=
  OracleComp.EvalDistEq.bind_bind_swap left right next

/-- The measure-level form of independent explicit sampler reordering. -/
theorem independent_comm {A B Result : Type} [MeasurableSpace Result]
    (left : ProbComp A) (right : ProbComp B)
    (next : A → B → ProbComp Result) :
    𝒟[left >>= fun a => right >>= next a] =
      𝒟[right >>= fun b => left >>= fun a => next a b] := by
  exact (independent_comm_spmf left right next).evalDist_eq

abbrev MixedSpec (D R : Type) := unifSpec + (D →ₒ R)

/-- The actual mixed interpreter forwards each explicit source coin query and lazily caches only private dictionary requests. -/
def mixedLazyImpl : QueryImpl (MixedSpec D R) (StateT (D →ₒ R).QueryCache ProbComp) :=
  fun query cache => match query with
  | .inl coin => do
    let answer ← unifSpec.query coin
    pure (answer, cache)
  | .inr point => (randomOracle (spec := D →ₒ R) point).run cache

/-- The reserved private table does not replace explicit source coins: each left query is still evaluated by the real uniform oracle. -/
def mixedEagerImpl (table : D → R) : QueryImpl (MixedSpec D R) ProbComp := fun query =>
  match query with
  | .inl coin => unifSpec.query coin
  | .inr point => pure (table point)

/-- After the actual mixed run, independently complete only uncached private cells and retain that full table jointly with the result. -/
def mixedCompletedLazy {Result : Type} (client : OracleComp (MixedSpec D R) Result)
    (cache : (D →ₒ R).QueryCache) : ProbComp ((D → R) × Result) := do
  let result ← (simulateQ mixedLazyImpl client).run cache
  let tail ← $ᵗ (D → R)
  pure (tableExtending result.2 tail, result.1)

/-- The mixed lazy/eager correspondence retains the full private table and complete source result while every explicit uniform query remains real. -/
theorem mixedCompletedLazy_eq_eager {Result : Type} [MeasurableSpace Result]
    (client : OracleComp (MixedSpec D R) Result)
    (cache : (D →ₒ R).QueryCache) :
    𝒟[mixedCompletedLazy client cache] =
      𝒟[do
        let tail ← $ᵗ (D → R)
        let table := tableExtending cache tail
        let result ← simulateQ (mixedEagerImpl table) client
        pure (table, result)] := by
  induction client using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp [mixedCompletedLazy, simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    classical
    have reduce : mixedCompletedLazy (liftM ((MixedSpec D R).query query) >>= next) cache =
        (mixedLazyImpl query).run cache >>= fun reply =>
          mixedCompletedLazy (next reply.1) reply.2 := by
      simp only [mixedCompletedLazy, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rw [reduce]
    cases query with
    | inl coin =>
      change 𝒟[(unifSpec.query coin : ProbComp _) >>= fun answer =>
        mixedCompletedLazy (next answer) cache] =
        𝒟[($ᵗ (D → R)) >>= fun tail =>
          (unifSpec.query coin : ProbComp _) >>= fun answer =>
            simulateQ (mixedEagerImpl (tableExtending cache tail)) (next answer) >>= fun result =>
              pure (tableExtending cache tail, result)]
      rw [independent_comm ($ᵗ (D → R)) (unifSpec.query coin : ProbComp _)]
      apply evalDist_bind_congr
      intro answer
      exact ih answer cache
    | inr point =>
      change R → OracleComp (MixedSpec D R) Result at next
      change 𝒟[(randomOracle (spec := D →ₒ R) point).run cache >>= fun reply =>
        mixedCompletedLazy (next reply.1) reply.2] =
        𝒟[($ᵗ (D → R)) >>= fun tail =>
          simulateQ (mixedEagerImpl (tableExtending cache tail)) (next (tableExtending cache tail point)) >>=
            fun result => pure (tableExtending cache tail, result)]
      cases cached : cache point with
      | none =>
        rw [QueryImpl.withCaching_run_none _ cached, map_eq_bind_pure_comp]
        simp only [Function.comp_def, bind_assoc, pure_bind]
        let observation : (D → R) → ProbComp ((D → R) × Result) := fun tail => do
          let result ← simulateQ (mixedEagerImpl (tableExtending cache tail))
            (next (tableExtending cache tail point))
          pure (tableExtending cache tail, result)
        have updated (answer : R) :
            (fun tail : D → R => do
              let result ← simulateQ (mixedEagerImpl (tableExtending (cache.cacheQuery point answer) tail))
                (next answer)
              pure (tableExtending (cache.cacheQuery point answer) tail, result)) =
            fun tail => observation (Function.update tail point answer) := by
          funext tail
          simp only [observation]
          rw [tableExtending_cacheQuery, ← tableExtending_update_of_none cache tail cached answer]
          simp only [Function.update_self]
        trans 𝒟[do
          let answer ← $ᵗ R
          let tail ← $ᵗ (D → R)
          observation (Function.update tail point answer)]
        · apply evalDist_bind_congr
          intro answer
          rw [ih answer (cache.cacheQuery point answer), updated answer]
        · exact uniform_update_bind point observation
      | some answer =>
        rw [QueryImpl.withCaching_run_some _ cached, pure_bind, ih answer cache]
        have hit (tail : D → R) : tableExtending cache tail point = answer := by
          simp [tableExtending, cached]
        simp_rw [hit]

/-- Empty-cache specialization for the mixed interface; all explicit source randomness remains inside the continued eager interpreter. -/
theorem mixedCompletedLazy_empty_eq_uniform {Result : Type}
    [MeasurableSpace Result] (client : OracleComp (MixedSpec D R) Result) :
    𝒟[mixedCompletedLazy client ∅] =
      𝒟[do
        let table ← $ᵗ (D → R)
        let result ← simulateQ (mixedEagerImpl table) client
        pure (table, result)] := by
  rw [mixedCompletedLazy_eq_eager]
  simp only [tableExtending_empty]

end BeaconcryptCore.Computational.JointEagerTable



/--
info: 'BeaconcryptCore.Computational.JointEagerTable.completedLazy_eq_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointEagerTable.completedLazy_eq_eager

/--
info: 'BeaconcryptCore.Computational.JointEagerTable.completedLazy_empty_eq_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointEagerTable.completedLazy_empty_eq_uniform

/--
info: 'BeaconcryptCore.Computational.JointEagerTable.uniform_update_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointEagerTable.uniform_update_bind

/--
info: 'BeaconcryptCore.Computational.JointEagerTable.mixedCompletedLazy_eq_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointEagerTable.mixedCompletedLazy_eq_eager

/--
info: 'BeaconcryptCore.Computational.JointEagerTable.mixedCompletedLazy_empty_eq_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointEagerTable.mixedCompletedLazy_empty_eq_uniform
