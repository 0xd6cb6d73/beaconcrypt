import BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix
import BeaconcryptCore.Computational.RawCtxRetainedTable

/-!
A remaining selected private derivation can be factored through its complete fixed retained view. Public and other callbacks remain unchanged. The private table and cursor are projected only after the whole continuation, and early comparison sampling has its own sampling cost rather than inheriting one through a distribution equation.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectiveChainGame
open RawCtxKdfRequestTable RawCtxSelectedParentTable RawCtxRetainedTable

/-- The entire saturated continuation retains every earlier private binding and all original common state under the fixed retained view. -/
theorem saturated_view {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (cache : Table) (cursor : Cursor)
    (past : stage ≤ cursor.depth) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler source stage other) client).run (state, (cache, cursor)) =
      (simulateQ (viewImpl (view (productionStream source.crypto) cache) other) client).run state := by
  rw [RawCtxSelectiveChainPrefix.saturated_run source stage other client (state, (cache, cursor)) past]
  have zero := congrArg (fun computation : ProbComp (Result × (State × Table)) =>
    (fun result => (result.1, result.2.1)) <$> computation)
    (zero_complete source other client state cache cursor)
  simpa only [Functor.map_map, project] using zero.trans (complete source other client state cache).symm

private theorem unmatched_view (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (cache : Table) (cursor : Cursor) (unchosen : matched cursor request = false) :
    privateStep source stage request (cache, cursor) =
      pure (view (productionStream source.crypto) cache request,
        (cache.cacheQuery request (view (productionStream source.crypto) cache request), cursor)) := by
  cases found : cache request with
  | none =>
    rw [private_real source stage request (cache, cursor) found (Or.inl unchosen)]
    simp [view, found, advance, unchosen]
  | some output =>
    rw [private_hit source stage request (cache, cursor) output found]
    simp [view, found, advance, unchosen]

/-- With one selected derivation remaining and its actual address absent from the retained private cache, an early complete response gives the same final result/common-state distribution. -/
theorem single_uniform {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (cache : Table) (cursor : Cursor)
    (missing : cache (cursorAddress cursor) = none) :
    EvalDistEq ((fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler source (cursor.depth + 1) other) client).run (state, (cache, cursor)))
      (($ᵗ FullOutput) >>= fun output =>
        (simulateQ (viewImpl (view (productionStream source.crypto) (cache.cacheQuery (cursorAddress cursor) output)) other) client).run state) := by
  induction client using OracleComp.inductionOn generalizing state cache cursor with
  | pure value =>
    change EvalDistEq (pure (value, state) : ProbComp (Result × State))
      (($ᵗ FullOutput) >>= fun _ => pure (value, state))
    exact (OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (pure (value, state))).symm
  | query_bind query next ih =>
    cases query with
    | inl query =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [handler, viewImpl, StateT.run, bind_assoc, pure_bind, map_bind]
      refine (EvalDistEq.bind_right ((other query).run state)
        (fun result => ih result.1 result.2 cache cursor missing)).trans ?_
      exact (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ FullOutput) ((other query).run state)
        (fun output result => (simulateQ (viewImpl
          (view (productionStream source.crypto) (cache.cacheQuery (cursorAddress cursor) output)) other)
          (next result.1)).run result.2)).symm
    | inr request =>
      by_cases same : request = cursorAddress cursor
      · subst request
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        have chosen : matched cursor (cursorAddress cursor) = true := by simp [matched]
        simp only [handler, viewImpl, StateT.run,
          private_selected source (cursor.depth + 1) (cursorAddress cursor) (cache, cursor) missing chosen (Nat.lt_succ_self _),
          bind_map_left, pure_bind, map_bind, bind_assoc]
        simp only [view, QueryCache.cacheQuery_self, Option.getD_some]
        refine EvalDistEq.bind_right ($ᵗ FullOutput) (fun output => ?_)
        change EvalDistEq ((fun result => (result.1, result.2.1)) <$>
          (simulateQ (handler source (cursor.depth + 1) other) (next output)).run
            (state, (cache.cacheQuery (cursorAddress cursor) output, advance cursor (cursorAddress cursor) output)))
          ((simulateQ (viewImpl (view (productionStream source.crypto) (cache.cacheQuery (cursorAddress cursor) output)) other)
            (next output)).run state)
        exact Eq.subst (motive := fun later => EvalDistEq _ later) (saturated_view source (cursor.depth + 1) other
          (next output) state (cache.cacheQuery (cursorAddress cursor) output) (advance cursor (cursorAddress cursor) output)
          (by simp [advance_depth, chosen])) (EvalDistEq.refl _)
      · have unchosen : matched cursor request = false := by simp [matched, same]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp only [handler, viewImpl, StateT.run,
          unmatched_view source (cursor.depth + 1) request cache cursor unchosen, pure_bind]
        have response (output : FullOutput) :
            view (productionStream source.crypto) (cache.cacheQuery (cursorAddress cursor) output) request =
              view (productionStream source.crypto) cache request := by
          simp only [view, QueryCache.cacheQuery_of_ne (spec := JointKdfRO) cache output same]
        simp only [response]
        change EvalDistEq ((fun result => (result.1, result.2.1)) <$>
          (simulateQ (handler source (cursor.depth + 1) other)
            (next (view (productionStream source.crypto) cache request))).run
            (state, (cache.cacheQuery request (view (productionStream source.crypto) cache request), cursor)))
          (($ᵗ FullOutput) >>= fun output =>
            (simulateQ (viewImpl (view (productionStream source.crypto) (cache.cacheQuery (cursorAddress cursor) output)) other)
              (next (view (productionStream source.crypto) cache request))).run state)
        have stillMissing : (cache.cacheQuery request (view (productionStream source.crypto) cache request)) (cursorAddress cursor) = none := by
          rw [QueryCache.cacheQuery_of_ne (spec := JointKdfRO) cache _ (Ne.symm same), missing]
        have future (output : FullOutput) :
            view (productionStream source.crypto)
              ((cache.cacheQuery request (view (productionStream source.crypto) cache request)).cacheQuery (cursorAddress cursor) output) =
            view (productionStream source.crypto) (cache.cacheQuery (cursorAddress cursor) output) := by
          funext address
          simp only [view_recorded, view_stable]
        simpa only [future] using ih (view (productionStream source.crypto) cache request) state
          (cache.cacheQuery request (view (productionStream source.crypto) cache request)) cursor stillMissing

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.single_uniform_vcvioLegacy :
    ∀ {ι State Result : Type} {spec : OracleSpec ι} (source : BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp)) (client : OracleComp (spec + BeaconcryptCore.Computational.PqxdhJointKdf.JointKdfRO) Result) (state : State) (cache : BeaconcryptCore.Computational.RawCtxKdfRequestTable.Table) (cursor : BeaconcryptCore.Computational.RawCtxSelectiveChainGame.Cursor) (missing : cache (BeaconcryptCore.Computational.RawCtxSelectiveChainGame.cursorAddress cursor) = Option.none),
      𝒮[(fun (result : Result × State × BeaconcryptCore.Computational.RawCtxSelectiveChainGame.Store) => (result.1, result.2.1)) <$> (simulateQ (BeaconcryptCore.Computational.RawCtxSelectiveChainGame.handler source (cursor.depth + 1) other) client).run (state, cache, cursor)] =
        𝒮[do
          let output ← $ᵗ BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.FullOutput
          (simulateQ (BeaconcryptCore.Computational.RawCtxRetainedTable.viewImpl (BeaconcryptCore.Computational.RawCtxSelectedParentTable.view (BeaconcryptCore.Computational.PqxdhJointKdf.productionStream source.crypto) (OracleSpec.QueryCache.cacheQuery cache (BeaconcryptCore.Computational.RawCtxSelectiveChainGame.cursorAddress cursor) output)) other) client).run state] :=
  by simpa only [BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] using @BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.single_uniform

noncomputable def early {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (cache : Table) (target : JointKdfAddress) :
    ProbComp (Result × State) := do
  let output ← $ᵗ FullOutput
  (simulateQ (viewImpl (view (productionStream source.crypto) (cache.cacheQuery target output)) other) client).run state

set_option maxRecDepth 2048 in
/-- The early-draw comparison pays its own full76 reservation and every all-reply continuation coin, including an unused child draw on early completion. -/
theorem early_uniform {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (cache : Table) (target : JointKdfAddress)
    (budget : Nat) (bounded : ∀ output : FullOutput,
      ((simulateQ (viewImpl (view (productionStream source.crypto) (cache.cacheQuery target output)) other) client).run state).IsTotalQueryBound budget) :
    (early source other client state cache target).IsTotalQueryBound (76 + budget) := by
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) bounded

end BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.saturated_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.saturated_view

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.single_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.single_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.early_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw.early_uniform
