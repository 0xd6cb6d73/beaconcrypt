-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.LazyOracleDiscard
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-! Completing a finite lazy cell table preserves the contextual law of arbitrary adaptive clients that also use literal probability coins. The initial cache is overlaid on the independently sampled table; no root context, table freshness or seed-state reset is required. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3CellEager
open LazyOracleDiscard (LawEq)
variable {D R Value : Type} [DecidableEq D] [Finite D]
  [SampleableType R] [SampleableType (D → R)]

abbrev Spec (D R : Type) := unifSpec + (D →ₒ R)

noncomputable def lazy : QueryImpl (Spec D R) (StateT (D →ₒ R).QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (D →ₒ R).QueryCache ProbComp) + (D →ₒ R).randomOracle

noncomputable def fixed (table : D → R) : QueryImpl (Spec D R) ProbComp
  | .inl coin => unifSpec.query coin
  | .inr point => pure (table point)

noncomputable def lazyRun (work : OracleComp (Spec D R) Value) (cache : (D →ₒ R).QueryCache) : ProbComp Value :=
  (simulateQ lazy work).run' cache

noncomputable def fixedRun (table : D → R) (work : OracleComp (Spec D R) Value) : ProbComp Value :=
  simulateQ (fixed table) work

omit [Finite D] [SampleableType (D → R)] in
private theorem lazy_bind (query : (Spec D R).Domain)
    (next : (Spec D R).Range query → OracleComp (Spec D R) Value) (cache : (D →ₒ R).QueryCache) :
    lazyRun (((Spec D R).query query : OracleComp (Spec D R) _) >>= next) cache =
      ((lazy query).run cache >>= fun result => lazyRun (next result.1) result.2) := by
  simp only [lazyRun, simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]

omit [DecidableEq D] [Finite D] [SampleableType R] [SampleableType (D → R)] in
private theorem fixed_bind (table : D → R) (query : (Spec D R).Domain)
    (next : (Spec D R).Range query → OracleComp (Spec D R) Value) :
    fixedRun table (((Spec D R).query query : OracleComp (Spec D R) _) >>= next) =
      (fixed table query >>= fun reply => fixedRun table (next reply)) := by
  simp only [fixedRun, simulateQ_bind, simulateQ_spec_query]

private theorem update_uniform (point : D) (next : (D → R) → ProbComp Value) :
    LawEq (do let answer ← $ᵗ R; let table ← $ᵗ (D → R); next (Function.update table point answer))
      (do let table ← $ᵗ (D → R); next table) := by
  intro Result _ continuation
  let : MeasurableSpace R := ⊤
  let : DiscreteMeasurableSpace R := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  simp only [bind_assoc]
  exact evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample point
    (fun table => next table >>= continuation)

private theorem read_eager (point : D) (next : R → OracleComp (Spec D R) Value)
    (cache : (D →ₒ R).QueryCache)
    (later : ∀ answer current, LawEq (lazyRun (next answer) current)
      (do let table ← $ᵗ (D → R); fixedRun (OracleComp.completeTable current table) (next answer))) :
    LawEq (((D →ₒ R).randomOracle point).run cache >>= fun result => lazyRun (next result.1) result.2)
      (do let table ← $ᵗ (D → R);
          fixedRun (OracleComp.completeTable cache table) (next (OracleComp.completeTable cache table point))) := by
  cases found : cache point with
  | some answer =>
      rw [QueryImpl.withCaching_run_some _ found, pure_bind]
      simpa only [OracleComp.completeTable, found, Option.getD_some] using later answer cache
  | none =>
      rw [QueryImpl.withCaching_run_none _ found]
      simp only [bind_map_left]
      have first := LawEq.bind (LawEq.refl ($ᵗ R)) (fun answer => later answer (cache.cacheQuery point answer))
      refine first.trans ?_
      have redrawn := update_uniform point (fun table => fixedRun (OracleComp.completeTable cache table)
        (next (OracleComp.completeTable cache table point)))
      simpa only [bind_assoc, OracleComp.completeTable_cacheQuery,
        OracleComp.completeTable_update_of_none cache _ found,
        OracleComp.completeTable, found, Function.update_self, Option.getD_none] using redrawn

/-- Finite lazy cells and literal coins have the contextual law of one completed table, with every initial cached cell retained. -/
theorem cached_eager (work : OracleComp (Spec D R) Value) (cache : (D →ₒ R).QueryCache) :
    LawEq (lazyRun work cache)
      (do let table ← $ᵗ (D → R); fixedRun (OracleComp.completeTable cache table) work) := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [lazyRun, fixedRun, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (LazyOracleDiscard.lawEq_drop ($ᵗ (D → R)) (pure value)).symm
  | query_bind query next ih =>
      rw [lazy_bind]
      cases query with
      | inl coin =>
          change LawEq (((StateT.lift (unifSpec.query coin : ProbComp _)).run cache) >>= _) _
          simp only [StateT.run_lift, bind_pure_comp]
          have first := LawEq.bind (LawEq.refl (unifSpec.query coin : ProbComp _)) (fun reply => ih reply cache)
          refine first.trans ?_
          have moved := LazyOracleDiscard.lawEq_swap (unifSpec.query coin : ProbComp _) ($ᵗ (D → R))
            (fun reply table => fixedRun (OracleComp.completeTable cache table) (next reply))
          convert moved using 1; simp only [fixed_bind, fixed]; rfl
      | inr point =>
          change LawEq (((D →ₒ R).randomOracle point).run cache >>= _) _
          simp only [fixed_bind, fixed, pure_bind]
          convert read_eager (D := D) (R := R) point next cache (fun reply current => ih reply current) using 1
          rfl

/-- With the actual empty cache, the complete table is an independent uniform function with no overlay. -/
theorem empty_eager (work : OracleComp (Spec D R) Value) :
    LawEq (lazyRun work ∅) (do let table ← $ᵗ (D → R); fixedRun table work) := by
  simpa only [OracleComp.completeTable_empty] using cached_eager work ∅

end BeaconcryptCore.Computational.RegistrationNativeG3CellEager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3CellEager.cached_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3CellEager.cached_eager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3CellEager.empty_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3CellEager.empty_eager
