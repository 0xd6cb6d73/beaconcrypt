import BeaconcryptCore.Computational.RawCtxSelectedParentTable

/-!
A fixed-source memo handler retains every earlier cache binding, including outputs inserted by earlier hybrid steps. The complete adaptive continuation sees exactly the initial cache lookup with the actual fixed source as fallback. Only the final private table is erased after that continuation has finished. No consistency, freshness, output-uniformity or key-injectivity premise is used. The table is private proof context and supplies no new reveal capability.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxRetainedTable
open RawCtxKdfRequestTable RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf

/-- Recording the value already selected by the complete cache view changes no later lookup. -/
theorem view_stable (fallback : Prior) (cache : Table) (address : JointKdfAddress) :
    view fallback (cache.cacheQuery address (view fallback cache address)) = view fallback cache := by
  funext request
  by_cases same : request = address
  · subst request
    simp [view]
  · simp [view, QueryCache.cacheQuery_of_ne cache _ same]

/-- An actual fixed-source query returns the retained binding when present and the original source output otherwise. -/
theorem memo_view (source : FixedHkdfSha512NoSaltSource) (cache : Table) (address : JointKdfAddress) :
    (memoImpl source address).run cache =
      pure (view (productionStream source.crypto) cache address,
        cache.cacheQuery address (view (productionStream source.crypto) cache address)) := by
  cases found : cache address with
  | none => simp [memoImpl, view, found]
  | some output =>
    have retained : cache.cacheQuery address output = cache := by
      refine QueryCache.ext (fun previous => ?_)
      by_cases same : previous = address
      · subst previous
        simpa using found.symm
      · exact QueryCache.cacheQuery_of_ne cache _ same
    simp [memoImpl, view, found, retained]

/-- Other effects retain their original handler; all KDF replies use the same complete retained lookup. -/
noncomputable def viewImpl {ι State : Type} {spec : OracleSpec ι}
    (prior : Prior) (other : QueryImpl spec (StateT State ProbComp)) :
    QueryImpl (spec + JointKdfRO) (StateT State ProbComp)
  | .inl query => other query
  | .inr request => pure (prior request)

/-- Every adaptive continuation retains the original result and auxiliary state for an arbitrary initial cache, including prior hybrid entries. -/
theorem complete {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (cache : Table) :
    (simulateQ (viewImpl (view (productionStream source.crypto) cache) other) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (tableImpl source other) client).run (state, cache) := by
  induction client using OracleComp.inductionOn generalizing state cache with
  | pure value => rfl
  | query_bind query next ih =>
    cases query with
    | inl query =>
      change ((other query).run state >>= fun result =>
        (simulateQ (viewImpl (view (productionStream source.crypto) cache) other) (next result.1)).run result.2) =
        (fun result => (result.1, result.2.1)) <$>
          (((other query).run state >>= fun result => pure (result.1, (result.2, cache))) >>=
            fun result => (simulateQ (tableImpl source other) (next result.1)).run result.2)
      simp only [bind_assoc, pure_bind, map_bind]
      exact congrArg (fun continuation => (other query).run state >>= continuation)
        (funext fun result => ih result.1 result.2 cache)
    | inr request =>
      change (simulateQ (viewImpl (view (productionStream source.crypto) cache) other)
        (next (view (productionStream source.crypto) cache request))).run state =
        (fun result => (result.1, result.2.1)) <$>
          (((memoImpl source request).run cache >>= fun result => pure (result.1, (state, result.2))) >>=
            fun result => (simulateQ (tableImpl source other) (next result.1)).run result.2)
      simpa only [memo_view, pure_bind, view_stable] using
        ih (view (productionStream source.crypto) cache request) state
          (cache.cacheQuery request (view (productionStream source.crypto) cache request))

/-- After recording one complete predecessor response, the whole continued memo execution realizes that retained entry and every original prior binding. -/
theorem recorded_complete {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (cache : Table)
    (address : JointKdfAddress) (output : FullOutput) :
    (simulateQ (viewImpl (lookup (view (productionStream source.crypto) cache)
      (RawCtxSelectedParentEntry.fromOutput address output) (PqxdhOrderedChainHybrids.nextChain output)) other)
      client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (tableImpl source other) client).run (state, cache.cacheQuery address output) := by
  simpa only [show view (productionStream source.crypto) (cache.cacheQuery address output) =
    lookup (view (productionStream source.crypto) cache)
      (RawCtxSelectedParentEntry.fromOutput address output) (PqxdhOrderedChainHybrids.nextChain output) from
        funext fun request => view_recorded _ _ _ request _] using
    complete source other client state (cache.cacheQuery address output)

end BeaconcryptCore.Computational.RawCtxRetainedTable

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedTable.view_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedTable.view_stable

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedTable.memo_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedTable.memo_view

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedTable.complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedTable.complete

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedTable.recorded_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedTable.recorded_complete
