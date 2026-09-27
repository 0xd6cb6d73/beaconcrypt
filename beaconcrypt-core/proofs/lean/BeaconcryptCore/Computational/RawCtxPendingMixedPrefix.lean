import BeaconcryptCore.Computational.RawCtxPendingLiveQueries

/-!
The original adaptive computation is stopped immediately before its selected query, with the complete dependent query, reply continuation and interpreter state retained. The index counts every selected original callback, including repeated inputs; all other callbacks execute normally and preserve their effects. The owner and live specializations select both send and receive KDF calls. These are exact operational cuts, not a fresh-input or cache-miss premise. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingMixedPrefix

inductive Stopped {ι : Type} (spec : OracleSpec ι) (Result : Type) where
  | complete (result : Result)
  | pending (query : ι) (next : spec.Range query → OracleComp spec Result)

abbrev Prefix {ι : Type} (spec : OracleSpec ι) (Result State : Type) := Stopped spec Result × State

noncomputable def scan {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) : Nat → State → ProbComp (Prefix spec Result State) :=
  OracleComp.recOn client
    (fun result _ state => pure (.complete result, state))
    (fun query next recurse index state =>
      if selected query then match index with
        | 0 => pure (.pending query next, state)
        | index + 1 => do
            let (reply, updated) ← (impl query).run state
            recurse reply index updated
      else do
        let (reply, updated) ← (impl query).run state
        recurse reply index updated)

noncomputable def finish {ι Result State : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT State ProbComp)) (frame : Prefix spec Result State) : ProbComp (Result × State) :=
  match frame.1 with
  | .complete result => pure (result, frame.2)
  | .pending query next => do
      let (reply, updated) ← (impl query).run frame.2
      (simulateQ impl (next reply)).run updated

def ownerSelected {Chain : Type} : (RawCtxPendingOwnerQueries.Spec Chain).Domain → Bool
  | .inl (.inl _) => true
  | .inr (.inl (.inl _)) => true
  | _ => false

def liveSelected : RawCtxPendingLiveQueries.Spec.Domain → Bool
  | .inl query => ownerSelected query
  | .inr _ => false

/-- Completion retains the exact result and full reached interpreter state. -/
theorem scan_pure {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (result : Result) (index : Nat) (state : State) :
    scan selected impl (pure result) index state = pure (.complete result, state) := rfl

/-- The selected original callback is stopped before any reply or callback effect. -/
theorem scan_selected_zero {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (query : ι) (next : spec.Range query → OracleComp spec Result) (chosen : selected query = true)
    (state : State) :
    scan selected impl (spec.query query >>= next) 0 state = pure (.pending query next, state) := by
  change (if selected query then (pure (Stopped.pending query next, state) : ProbComp (Prefix spec Result State)) else _) = _
  rw [chosen]
  rfl

/-- Passing a prior selected slot executes its actual callback and counts it once even when the input repeats. -/
theorem scan_selected_succ {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (query : ι) (next : spec.Range query → OracleComp spec Result) (chosen : selected query = true)
    (index : Nat) (state : State) :
    scan selected impl (spec.query query >>= next) (index + 1) state =
      (do let (reply, updated) ← (impl query).run state
          scan selected impl (next reply) index updated) := by
  change (if selected query then _ else _ : ProbComp (Prefix spec Result State)) = _
  rw [chosen]
  rfl

/-- Every unselected callback executes normally without consuming the private-KDF selection index. -/
theorem scan_other {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (query : ι) (next : spec.Range query → OracleComp spec Result) (unchosen : selected query = false)
    (index : Nat) (state : State) :
    scan selected impl (spec.query query >>= next) index state =
      (do let (reply, updated) ← (impl query).run state
          scan selected impl (next reply) index updated) := by
  change (if selected query then _ else _ : ProbComp (Prefix spec Result State)) = _
  rw [unchosen]
  rfl

/-- Resuming the actual selected query restores the same complete execution, including early completion and all earlier effects. -/
theorem scan_finish {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) (index : Nat) (state : State) :
    (scan selected impl client index state >>= finish impl) = (simulateQ impl client).run state := by
  induction client using OracleComp.inductionOn generalizing index state with
  | pure result => rfl
  | query_bind query next ih =>
      cases chosen : selected query with
      | false =>
          simp only [scan_other selected impl query next chosen, bind_assoc, ih,
            simulateQ_query_bind, StateT.run_bind]
          rfl
      | true =>
          cases index with
          | zero =>
              rw [scan_selected_zero selected impl query next chosen]
              rfl
          | succ index =>
              simp only [scan_selected_succ selected impl query next chosen, bind_assoc,
                simulateQ_query_bind, StateT.run_bind]
              simp_rw [ih]
              rfl

/-- Every supported pending cut is an actual selected callback of the original program. -/
theorem pending_selected {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) (index : Nat) (state reached : State)
    (target : ι) (continuation : spec.Range target → OracleComp spec Result)
    (supported : (Stopped.pending target continuation, reached) ∈
      support (scan selected impl client index state)) : selected target = true := by
  induction client using OracleComp.inductionOn generalizing index state with
  | pure value =>
      simp only [scan_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      cases supported.1
  | query_bind query next ih =>
      cases chosen : selected query with
      | false =>
          simp only [scan_other selected impl query next chosen, support_bind, Set.mem_iUnion] at supported
          rcases supported with ⟨reply, _, supported⟩
          exact ih reply.1 index reply.2 supported
      | true =>
          cases index with
          | zero =>
              simp only [scan_selected_zero selected impl query next chosen, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at supported
              cases supported.1
              exact chosen
          | succ index =>
              simp only [scan_selected_succ selected impl query next chosen, support_bind, Set.mem_iUnion] at supported
              rcases supported with ⟨reply, _, supported⟩
              exact ih reply.1 index reply.2 supported

/-- Completed cuts preserve each underlying query budget by literal program equality, without distribution-based cost transport. -/
theorem completed_query_bound {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) (index : Nat) (state : State)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (scan selected impl client index state >>= finish impl).IsQueryBoundP predicate budget ↔
      ((simulateQ impl client).run state).IsQueryBoundP predicate budget := by
  rw [scan_finish]

open PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedLiveRead

/-- The selected mixed cut resumes to the same original live source result and complete retained state. -/
theorem source_cut {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp RawCtxSelectedLiveTrace.SourceSpec Result)
    (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) (index : Nat) :
    let impl := RawCtxSelectedLiveCompiler.recorded source writer output reader ∘ₛ RawCtxPendingLiveQueries.erase
    RawCtxSelectedLiveCompiler.regroup <$>
      (scan liveSelected impl
        ((simulateQ (RawCtxPendingLiveQueries.compiler sender decode owner) client).run
          (RawCtxSelectedLiveCompiler.splitState state).1)
        index (RawCtxSelectedLiveCompiler.splitState state).2 >>= finish impl) =
      (simulateQ (RawCtxSelectedLiveTrace.observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner reader) client).run state := by
  dsimp only
  rw [scan_finish]
  exact RawCtxPendingLiveQueries.source_project source writer output reader sender decode owner client state

end BeaconcryptCore.Computational.RawCtxPendingMixedPrefix

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_pure

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_selected_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_selected_zero

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_selected_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_selected_succ

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_other' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_other

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.scan_finish

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.pending_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.pending_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.completed_query_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.completed_query_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.source_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.source_cut
