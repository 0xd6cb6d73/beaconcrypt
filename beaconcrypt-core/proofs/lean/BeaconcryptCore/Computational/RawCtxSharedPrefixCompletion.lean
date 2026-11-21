import BeaconcryptCore.Computational.RawCtxSharedPrefixBounds

/-!
The shared-ROM scanner resumes its exact saved callback and complete continuation. This is equality of the original oracle programs, so it can transfer query bounds, including cached hash requests, without inferring costs from probability distributions.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedPrefixCompletion
open CtxRomAuth AdaptiveCtxSharedHash RawCtxForwardAnnotation RawCtxForwardCoverage RawCtxForwardScan
variable {ι Local Tag Result : Type} {base : OracleSpec ι}

noncomputable def finish (impl : QueryImpl base (StateT Local (OracleComp HashSpec)))
    (frame : Tag → Frame base Result) : Cut Tag Result Local → OracleComp HashSpec (Result × Local)
  | .complete result state => pure (result, state)
  | .pending tag state => do
      let reply ← (impl (frame tag).1).run state
      (simulateQ impl ((frame tag).2 reply.1)).run reply.2

/-- Resumption executes the same selected request and every later callback with the full local state and shared hash interface. -/
theorem scan_finish
    (privateQuery : base.Domain → Bool) (selected : base.Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp HashSpec))) (frame : Tag → Frame base Result)
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (sound : Sound frame client) (state : Local) :
    (RawCtxSharedPrefixScan.scan privateQuery selected selection impl client covered state >>= finish impl frame) =
      (simulateQ impl (simulateQ erase client)).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, erase, StateT.run_bind]
    change ((if chosen : selected query.2 state = true then _ else _) >>= finish impl frame) = _
    split
    next chosen =>
      have same := sound.1 (query.1.get (covered.1.trans (selection query.2 state chosen)))
        (Option.some_get (covered.1.trans (selection query.2 state chosen))).symm
      exact congrArg (fun saved : Frame base Result => do
        let reply ← (impl saved.1).run state
        (simulateQ impl (saved.2 reply.1)).run reply.2) same.symm
    next unchosen =>
      rw [bind_assoc]
      exact bind_congr fun reply => ih reply.1 (covered.2 reply.1) (sound.2 reply.1) reply.2

/-- Dropping a suffix cannot increase any counted class of oracle requests, including requests answered from a cache. -/
theorem prefix_bound {Value : Type} (client : OracleComp base Result) (next : Result → OracleComp base Value)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (q : Nat)
    (bounded : (client >>= next).IsQueryBoundP predicate q) : client.IsQueryBoundP predicate q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => trivial
  | query_bind query continuation ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at bounded
    exact (isQueryBoundP_query_bind_iff predicate _ _ _).mpr ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

end BeaconcryptCore.Computational.RawCtxSharedPrefixCompletion

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPrefixCompletion.scan_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrefixCompletion.scan_finish

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPrefixCompletion.prefix_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrefixCompletion.prefix_bound
