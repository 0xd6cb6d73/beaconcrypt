import BeaconcryptCore.Computational.RawCtxForwardCoverage
import BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix

/-!
The source scanner returns the descriptor already carried by the selected query. Static coverage proves that this option is present whenever the state-dependent cut selects that query, so no fallback frame, existential search or inverse on continuations is executed. Exact descriptor soundness then proves that packing the returned concrete tag is the original full stateful source prefix.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardScan
open RawCtxForwardAnnotation RawCtxForwardCoverage
variable {Tag ι Result State : Type} {base : OracleSpec ι}

inductive Cut (Tag Result State : Type) where
  | complete (result : Result) (state : State)
  | pending (tag : Tag) (state : State)

noncomputable def pack (frame : Tag → Frame base Result) : Cut Tag Result State → RawCtxPendingMixedPrefix.Prefix base Result State
  | .complete result state => (.complete result, state)
  | .pending tag state => (.pending (frame tag).1 (frame tag).2, state)

noncomputable def scan
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp))
    (client : OracleComp (Spec Tag base) Result) :
    Covered privateQuery client → State → ProbComp (Cut Tag Result State) :=
  OracleComp.recOn client
    (fun result _covered state => pure (.complete result state))
    (fun query _next recurse covered state =>
      if chosen : selected query.2 state = true then
        pure (.pending (query.1.get (covered.1.trans (selection query.2 state chosen))) state)
      else do
        let (reply, updated) ← (impl query.2).run state
        recurse reply (covered.2 reply) updated)

/-- Completion retains the exact actual result and whole reached interpreter state. -/
theorem scan_pure
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (result : Result)
    (covered : Covered privateQuery (pure result : OracleComp (Spec Tag base) Result)) (state : State) :
    scan privateQuery selected selection impl (pure result) covered state = pure (.complete result state) := rfl

/-- A selected query returns its literal carried descriptor before making the primitive call or receiving any reply. -/
theorem scan_cut
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (query : (Spec Tag base).Domain)
    (next : (Spec Tag base).Range query → OracleComp (Spec Tag base) Result)
    (covered : Covered privateQuery (((Spec Tag base).query query : OracleComp (Spec Tag base) _) >>= next)) (state : State)
    (chosen : selected query.2 state = true) :
    scan privateQuery selected selection impl (((Spec Tag base).query query : OracleComp (Spec Tag base) _) >>= next) covered state =
      pure (.pending (query.1.get (covered.1.trans (selection query.2 state chosen))) state) := by
  change (if chosen : selected query.2 state = true then _ else _ : ProbComp _) = _
  rw [dif_pos chosen]
  rfl

/-- An unselected callback executes its original full stateful interface and scans the unchanged reply continuation. -/
theorem scan_other
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (query : (Spec Tag base).Domain)
    (next : (Spec Tag base).Range query → OracleComp (Spec Tag base) Result)
    (covered : Covered privateQuery (((Spec Tag base).query query : OracleComp (Spec Tag base) _) >>= next)) (state : State)
    (chosen : selected query.2 state = false) :
    scan privateQuery selected selection impl (((Spec Tag base).query query : OracleComp (Spec Tag base) _) >>= next) covered state =
      (do let (reply, updated) ← (impl query.2).run state
          scan privateQuery selected selection impl (next reply) (covered.2 reply) updated) := by
  change (if chosen : selected query.2 state = true then _ else _ : ProbComp _) = _
  rw [dif_neg (by rw [chosen]; decide)]
  rfl

/-- Packing the carried descriptor gives exactly the original complete stateful prefix, retaining the selected dependent callback and every pre-cut effect. -/
theorem scan_pack
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (frame : Tag → Frame base Result)
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (sound : Sound frame client) (state : State) :
    pack frame <$> scan privateQuery selected selection impl client covered state =
      RawCtxStatefulPendingPrefix.scan selected impl (simulateQ erase client) state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, erase]
    cases chosen : selected query.2 state with
    | true =>
      rw [scan_cut privateQuery selected selection impl query next covered state chosen,
        RawCtxStatefulPendingPrefix.scan_cut selected impl query.2 _ state chosen, map_pure]
      have present := covered.1.trans (selection query.2 state chosen)
      have same := sound.1 (query.1.get present) (Option.some_get present).symm
      exact congrArg pure (congrArg (fun saved : Frame base Result =>
        (RawCtxPendingMixedPrefix.Stopped.pending saved.1 saved.2, state)) same.symm)
    | false =>
      rw [scan_other privateQuery selected selection impl query next covered state chosen,
        RawCtxStatefulPendingPrefix.scan_other selected impl query.2 _ state chosen, map_bind]
      exact bind_congr fun reply => ih reply.1 (covered.2 reply.1) (sound.2 reply.1) reply.2

/-- The executable carried-prefix sampler followed by its exact descriptor continuation is the same original complete execution. -/
theorem scan_finish
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (frame : Tag → Frame base Result)
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (sound : Sound frame client) (state : State) :
    (scan privateQuery selected selection impl client covered state >>=
      fun cut => RawCtxPendingMixedPrefix.finish impl (pack frame cut)) =
      (simulateQ impl (simulateQ erase client)).run state := by
  have complete := RawCtxStatefulPendingPrefix.scan_finish selected impl (simulateQ erase client) state
  rw [← scan_pack privateQuery selected selection impl frame client covered sound state] at complete
  simpa only [bind_map_left] using complete

/-- A supported carried descriptor is the actual selected query of the same erased source syntax and retains its full original continuation. -/
theorem pending_origin
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (frame : Tag → Frame base Result)
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (sound : Sound frame client) (state reached : State) (tag : Tag)
    (supported : Cut.pending tag reached ∈ support (scan privateQuery selected selection impl client covered state)) :
    selected (frame tag).1 reached = true ∧
      RawCtxQueryOccurrence.Occurs (frame tag).1 (frame tag).2 (simulateQ erase client) := by
  have mapped : (RawCtxPendingMixedPrefix.Stopped.pending (frame tag).1 (frame tag).2, reached) ∈
      support (pack frame <$> scan privateQuery selected selection impl client covered state) := by
    rw [support_map]
    exact ⟨.pending tag reached, supported, rfl⟩
  rw [scan_pack privateQuery selected selection impl frame client covered sound state] at mapped
  exact RawCtxStatefulPendingPrefix.pending_origin selected impl (simulateQ erase client) state reached
    (frame tag).1 (frame tag).2 mapped

/-- The carried sampler's actual uniform-query bill is bounded by the complete original source bill through literal scan-and-finish equality. -/
theorem scan_uniform
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (frame : Tag → Frame base Result)
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (sound : Sound frame client) (state : State) (budget : Nat)
    (bounded : ((simulateQ impl (simulateQ erase client)).run state).IsTotalQueryBound budget) :
    (scan privateQuery selected selection impl client covered state).IsTotalQueryBound budget := by
  apply IsTotalQueryBound.of_bind_left (ob := fun cut => RawCtxPendingMixedPrefix.finish impl (pack frame cut))
  rw [scan_finish privateQuery selected selection impl frame client covered sound state]
  exact bounded

end BeaconcryptCore.Computational.RawCtxForwardScan

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardScan.scan_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardScan.scan_pure
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardScan.scan_cut' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardScan.scan_cut
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardScan.scan_other' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardScan.scan_other
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardScan.scan_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardScan.scan_pack
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardScan.scan_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardScan.scan_finish
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardScan.pending_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardScan.pending_origin
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardScan.scan_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardScan.scan_uniform
