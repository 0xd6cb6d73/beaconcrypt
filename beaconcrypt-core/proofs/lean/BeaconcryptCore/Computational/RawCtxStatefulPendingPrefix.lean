import BeaconcryptCore.Computational.RawCtxQueryOccurrence

/-!
This scanner stops before a query selected by its complete current interpreter state. It retains the original dependent pending payload, exact outside continuation and full reached state. This allows a source KDF pending request to remain available while the private cache/cursor determines whether the callback is the next selected miss. Every unselected callback executes normally, including repeated table hits and optional failures. The generic operational laws do not assert that a cut occurs or that an input is fresh or uniform.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix
open RawCtxPendingMixedPrefix

noncomputable def scan {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) : State → ProbComp (Prefix spec Result State) :=
  OracleComp.recOn client
    (fun result state => pure (.complete result, state))
    (fun query next recurse state => if selected query state then pure (.pending query next, state)
      else do
        let (reply, updated) ← (impl query).run state
        recurse reply updated)

/-- Early completion retains the actual result and complete reached state. -/
theorem scan_pure {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (result : Result) (state : State) :
    scan selected impl (pure result) state = pure (.complete result, state) := rfl

/-- The actual state-dependent selected callback is saved before its reply or effect. -/
theorem scan_cut {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (query : ι) (next : spec.Range query → OracleComp spec Result) (state : State)
    (chosen : selected query state = true) :
    scan selected impl (spec.query query >>= next) state = pure (.pending query next, state) := by
  change (if selected query state then _ else _ : ProbComp _) = _
  rw [chosen]
  rfl

/-- Every unselected callback preserves its original reply and complete state effects before scanning its original continuation. -/
theorem scan_other {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (query : ι) (next : spec.Range query → OracleComp spec Result) (state : State)
    (chosen : selected query state = false) :
    scan selected impl (spec.query query >>= next) state =
      (do let (reply, updated) ← (impl query).run state
          scan selected impl (next reply) updated) := by
  change (if selected query state then _ else _ : ProbComp _) = _
  rw [chosen]
  rfl

/-- Resuming the same saved frame gives the exact original complete stateful execution, including executions that finish before any cut. -/
theorem scan_finish {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) (state : State) :
    (scan selected impl client state >>= finish impl) = (simulateQ impl client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    cases chosen : selected query state with
    | true => rw [scan_cut selected impl query next state chosen]; rfl
    | false =>
      simp only [scan_other selected impl query next state chosen, bind_assoc, ih,
        simulateQ_query_bind, StateT.run_bind]
      rfl

/-- Literal agreement on unselected callback executions gives one common complete prefix, without comparing evaluated costs or conditioning on a cut. -/
theorem scan_same {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (left right : QueryImpl spec (StateT State ProbComp))
    (agree : ∀ query state, selected query state = false → (left query).run state = (right query).run state)
    (client : OracleComp spec Result) (state : State) :
    scan selected left client state = scan selected right client state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    cases chosen : selected query state with
    | true => rw [scan_cut selected left query next state chosen, scan_cut selected right query next state chosen]
    | false =>
      rw [scan_other selected left query next state chosen, scan_other selected right query next state chosen,
        agree query state chosen]
      exact bind_congr fun reply => ih reply.1 reply.2

/-- A supported pending result derives the actual selection condition and original syntactic query occurrence with the same complete continuation and reached state. -/
theorem pending_origin {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) (state reached : State) (target : ι)
    (continuation : spec.Range target → OracleComp spec Result)
    (supported : (Stopped.pending target continuation, reached) ∈ support (scan selected impl client state)) :
    selected target reached = true ∧ RawCtxQueryOccurrence.Occurs target continuation client := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [scan_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.1
  | query_bind query next ih =>
    cases chosen : selected query state with
    | true =>
      simp only [scan_cut selected impl query next state chosen,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      cases supported.1
      rw [supported.2]
      exact ⟨chosen, RawCtxQueryOccurrence.here _ _⟩
    | false =>
      simp only [scan_other selected impl query next state chosen, support_bind, Set.mem_iUnion] at supported
      rcases supported with ⟨reply, _, supported⟩
      have tail := ih reply.1 reply.2 supported
      exact ⟨tail.1, RawCtxQueryOccurrence.later target query continuation next reply.1 tail.2⟩

end BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix

/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_pure
/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_cut' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_cut
/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_other' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_other
/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_finish
/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.scan_same
/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.pending_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix.pending_origin
