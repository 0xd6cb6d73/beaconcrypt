import BeaconcryptCore.Computational.RawCtxSelectiveSharedRom

/-!
The original carried scanner can execute its prefix through a shared ROM. Selection is made from the actual private state before executing the selected request. The proof preserves the exact saved descriptor and the complete reached cache; it does not recover a descriptor from an unrelated marginal or populate an arbitrary challenger cache.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedPrefixScan
open CtxRomAuth AdaptiveCtxSharedHash RawCtxForwardAnnotation RawCtxForwardCoverage RawCtxForwardScan
variable {ι Local Native Tag Result : Type} {base : OracleSpec ι}

noncomputable def scan
    (privateQuery : base.Domain → Bool) (selected : base.Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp HashSpec)))
    (client : OracleComp (Spec Tag base) Result) :
    Covered privateQuery client → Local → OracleComp HashSpec (Cut Tag Result Local) :=
  OracleComp.recOn client
    (fun result _covered state => pure (.complete result state))
    (fun query _next recurse covered state =>
      if chosen : selected query.2 state = true then
        pure (.pending (query.1.get (covered.1.trans (selection query.2 state chosen))) state)
      else do
        let (reply, updated) ← (impl query.2).run state
        recurse reply (covered.2 reply) updated)

def restore (attach : Local → CtxRO.QueryCache → Native)
    (result : Cut Tag Result Local × CtxRO.QueryCache) : Cut Tag Result Native :=
  match result.1 with
  | .complete value state => .complete value (attach state result.2)
  | .pending tag state => .pending tag (attach state result.2)

/-- Executing the exact callback compiler gives the original carried-prefix sampler with its full reached cache and saved continuation descriptor. -/
theorem source
    (privateQuery : base.Domain → Bool) (selected : base.Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp HashSpec)))
    (nativeSelected : base.Domain → Native → Bool)
    (nativeSelection : ∀ query state, nativeSelected query state = true → privateQuery query = true)
    (nativeImpl : QueryImpl base (StateT Native ProbComp))
    (attach : Local → CtxRO.QueryCache → Native)
    (sameSelection : ∀ query state cache, nativeSelected query (attach state cache) = selected query state)
    (sameStep : ∀ query state cache,
      (fun result => (result.1.1, attach result.1.2 result.2)) <$>
        (simulateQ hashImpl ((impl query).run state)).run cache =
          (nativeImpl query).run (attach state cache))
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (state : Local) (cache : CtxRO.QueryCache) :
    restore attach <$> (simulateQ hashImpl (scan privateQuery selected selection impl client covered state)).run cache =
      RawCtxForwardScan.scan privateQuery nativeSelected nativeSelection nativeImpl client covered (attach state cache) := by
  induction client using OracleComp.inductionOn generalizing state cache with
  | pure value => rfl
  | query_bind query next ih =>
    cases chosen : selected query.2 state with
    | true =>
      have nativeChosen : nativeSelected query.2 (attach state cache) = true := (sameSelection query.2 state cache).trans chosen
      rw [RawCtxForwardScan.scan_cut privateQuery nativeSelected nativeSelection nativeImpl query next covered _ nativeChosen]
      change restore attach <$> (simulateQ hashImpl (if chosen : selected query.2 state = true then _ else _)).run cache = _
      rw [dif_pos chosen]
      rfl
    | false =>
      have nativeChosen : nativeSelected query.2 (attach state cache) = false := (sameSelection query.2 state cache).trans chosen
      rw [RawCtxForwardScan.scan_other privateQuery nativeSelected nativeSelection nativeImpl query next covered _ nativeChosen]
      change restore attach <$> (simulateQ hashImpl (if chosen : selected query.2 state = true then _ else _)).run cache = _
      rw [dif_neg (by rw [chosen]; decide)]
      simp only [simulateQ_bind, StateT.run_bind, map_bind]
      rw [← sameStep query.2 state cache, bind_map_left]
      exact bind_congr fun result => ih result.1.1 (covered.2 result.1.1) result.1.2 result.2

end BeaconcryptCore.Computational.RawCtxSharedPrefixScan


/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPrefixScan.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrefixScan.source
