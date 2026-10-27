import BeaconcryptCore.Computational.RawCtxPendingReceiveQueries

/-!
The original receive program is scanned at a chronological KDF callback index. Before that callback, all original effects and the complete private state execute unchanged; the saved stop retains the actual full pending request and its arbitrary outer continuation. Resuming the same stop gives the exact full original result and poststate, including completion before the selected index. A stop supported by the recursive receive program has its original normalResume continuation, derived from source syntax.

A callback index is not a distinct table-miss index. These operational statements do not claim a new entry, uniform native HKDF output, secrecy or absence of live exposure. The pending payload and stored continuation are private interpreter context, not a new public or reveal capability. Snapshots, persistence and restoration remain excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingReceivePrefix
open RawCtxChainReceive RawCtxPendingReceiveQueries RawCtxInterpretedOpening

inductive Stopped (Send Receive Material Context Plaintext Result : Type) where
  | complete (result : Result)
  | pending (request : Kdf Send Receive Material Context)
      (next : Receive × Material → OracleComp (Spec Send Receive Material Context Plaintext) Result)

abbrev Prefix (Send Receive Material Context Plaintext Result State : Type) :=
  Stopped Send Receive Material Context Plaintext Result × State

noncomputable def scan {Send Receive Material Context Plaintext Result State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (client : OracleComp (Spec Send Receive Material Context Plaintext) Result) :
    Nat → State → ProbComp (Prefix Send Receive Material Context Plaintext Result State) :=
  OracleComp.recOn client
    (fun result _ state => pure (.complete result, state))
    (fun query next recurse index state => match query with
      | .inl pending => match index with
        | 0 => pure (.pending pending next, state)
        | index + 1 => do
            let (reply, updated) ← (impl (.inl pending)).run state
            recurse reply index updated
      | .inr pending => do
          let (reply, updated) ← (impl (.inr pending)).run state
          recurse reply index updated)

noncomputable def finish {Send Receive Material Context Plaintext Result State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (frame : Prefix Send Receive Material Context Plaintext Result State) : ProbComp (Result × State) :=
  match frame.1 with
  | .complete result => pure (result, frame.2)
  | .pending request next => do
      let (reply, updated) ← (impl (.inl request)).run frame.2
      (simulateQ impl (next reply)).run updated

/-- Passing an earlier original KDF slot executes its original stateful callback before continuing the scan. -/
theorem scan_pending_succ {Send Receive Material Context Plaintext Result State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (pending : Kdf Send Receive Material Context)
    (next : Receive × Material → OracleComp (Spec Send Receive Material Context Plaintext) Result)
    (index : Nat) (state : State) :
    scan impl ((Spec Send Receive Material Context Plaintext).query (.inl pending) >>= next) (index + 1) state =
      (do let (reply, updated) ← (impl (.inl pending)).run state
          scan impl (next reply) index updated) := rfl

/-- Completion before the selected index retains the exact final result and current state. -/
theorem scan_pure {Send Receive Material Context Plaintext Result State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (result : Result) (index : Nat) (state : State) :
    scan impl (pure result) index state = pure (.complete result, state) := rfl

/-- Selecting the next KDF call stops before its original callback, with the entire unchanged state and continuation. -/
theorem scan_pending_zero {Send Receive Material Context Plaintext Result State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (pending : Kdf Send Receive Material Context)
    (next : Receive × Material → OracleComp (Spec Send Receive Material Context Plaintext) Result)
    (state : State) :
    scan impl ((Spec Send Receive Material Context Plaintext).query (.inl pending) >>= next) 0 state =
      pure (.pending pending next, state) := rfl

/-- An opening executes its original optional callback without consuming a KDF selection index. -/
theorem scan_open {Send Receive Material Context Plaintext Result State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (pending : Opening Send Receive Material Context)
    (next : core.option.Option Plaintext → OracleComp (Spec Send Receive Material Context Plaintext) Result)
    (index : Nat) (state : State) :
    scan impl ((Spec Send Receive Material Context Plaintext).query (.inr pending) >>= next) index state =
      (do let (reply, updated) ← (impl (.inr pending)).run state
          scan impl (next reply) index updated) := rfl

/-- Resuming the selected original request retains every preceding effect and the full adaptive continuation, including completion before that request. -/
theorem scan_finish {Send Receive Material Context Plaintext Result State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (client : OracleComp (Spec Send Receive Material Context Plaintext) Result)
    (index : Nat) (state : State) :
    (scan impl client index state >>= finish impl) = (simulateQ impl client).run state := by
  induction client using OracleComp.inductionOn generalizing index state with
  | pure result => rfl
  | query_bind query next ih =>
    cases query with
    | inl pending =>
      cases index with
      | zero => rfl
      | succ index =>
        simp only [scan_pending_succ, bind_assoc, simulateQ_query_bind, StateT.run_bind]
        simp_rw [ih]
        rfl
    | inr pending =>
      simp only [scan_open, bind_assoc, ih, simulateQ_query_bind, StateT.run_bind]
      rfl

/-- A stop reached by the actual recursive receive program carries its original full pending payload and exact remaining receive continuation. -/
theorem program_pending {Send Receive Material Context Plaintext State : Type}
    (impl : QueryImpl (Spec Send Receive Material Context Plaintext) (StateT State ProbComp))
    (effect : Effect Send Receive Material Context) (index : Nat) (state : State)
    (pending : Kdf Send Receive Material Context)
    (next : Receive × Material → OracleComp (Spec Send Receive Material Context Plaintext)
      (RefinedRatchet Send Receive Material × core.option.Option Plaintext))
    (updated : State)
    (supported : (.pending pending next, updated) ∈
      support (scan impl (RawCtxPendingReceiveQueries.program effect) index state)) :
    next = fun reply => RawCtxPendingReceiveQueries.program (normalResume pending reply) := by
  generalize depth : effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect index state with
  | h rank ih =>
    cases effect with
    | rejected entry context =>
      simp only [RawCtxPendingReceiveQueries.program, scan_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at supported
      cases supported.1
    | openRequested opening =>
      simp only [RawCtxPendingReceiveQueries.program, scan_open, scan_pure, support_bind,
        Set.mem_iUnion, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      rcases supported with ⟨reply, _, contradiction, _⟩
      cases contradiction
    | kdfRequested before =>
      cases index with
      | zero =>
        simp only [RawCtxPendingReceiveQueries.program, scan_pending_zero, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at supported
        cases supported.1
        rfl
      | succ index =>
        simp only [RawCtxPendingReceiveQueries.program, scan_pending_succ, support_bind, Set.mem_iUnion] at supported
        rcases supported with ⟨reply, _, supported⟩
        exact ih _ (depth ▸ normalResume_rank before reply.1) _ index reply.2 supported rfl

end BeaconcryptCore.Computational.RawCtxPendingReceivePrefix

/--
info: 'BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_pending_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_pending_succ
/--
info: 'BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_pure
/--
info: 'BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_pending_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_pending_zero
/--
info: 'BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_open
/--
info: 'BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.scan_finish
/--
info: 'BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.program_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceivePrefix.program_pending
