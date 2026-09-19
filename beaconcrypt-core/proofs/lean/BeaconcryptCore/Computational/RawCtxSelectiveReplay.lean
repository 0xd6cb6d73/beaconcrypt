import BeaconcryptCore.Computational.RawCtxCursorLineage
import BeaconcryptCore.Computational.RawCtxPendingRetainedExecution

/-!
A supported execution of the actual selective private table can be replayed with the fixed lookup supplied by its own final table. Every private response was really recorded, and every earlier binding persists. This is only support inclusion for proving source invariants: it asserts neither probability equality nor query-cost transport, and it does not make a reached cache uniformly distributed.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveReplay
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxSelectedParentTable RawCtxCursorLineage
variable {ι State Result : Type} {spec : OracleSpec ι}

/-- The same full result and ambient state occur under the retained view of this execution's own final table; all initial full responses remain present. -/
theorem complete (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State × Store)
    (result : Result × (State × Store))
    (supported : result ∈ support ((simulateQ (handler source stage other) client).run state)) :
    Extends state.2.1 result.2.2.1 ∧
      (result.1, result.2.1) ∈ support ((simulateQ
        (RawCtxRetainedTable.viewImpl (view (productionStream source.crypto) result.2.2.1) other) client).run state.1) := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨fun _ _ known => known, by simp⟩
  | query_bind query next ih =>
    cases query with
    | inl query =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      rw [StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, actual, tail⟩ := supported
      have later := ih reply.1 (reply.2, state.2) result tail
      refine ⟨later.1, ?_⟩
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        RawCtxRetainedTable.viewImpl, mem_support_bind_iff]
      exact ⟨reply, actual, later.2⟩
    | inr request =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      rw [StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, actual, tail⟩ := supported
      have later := ih reply.1 (state.1, reply.2) result tail
      have extension := private_extends source stage request state.2 reply actual
      have recorded : reply.2.1 request = some reply.1 := by
        rw [private_state source stage request state.2 reply actual]
        simp
      have retained := later.1 request reply.1 recorded
      refine ⟨fun address output known => later.1 address output (extension address output known), ?_⟩
      simpa only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        RawCtxRetainedTable.viewImpl, StateT.run_pure, pure_bind, view, retained, Option.getD_some] using later.2

/-- The exact enriched source program retains the same replay property, including all native openings, sealing, public services and optional live reads. -/
theorem pending {A : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (state : RawCtxPendingSelectiveFamily.State A)
    (result : Result × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run state)) :
    Extends state.2.1 result.2.2.1 ∧
      (result.1, result.2.1) ∈ support ((simulateQ
        (RawCtxPendingRetainedExecution.retained source writer (view (productionStream source.crypto) result.2.2.1)) client).run state.1) := by
  simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingSelectiveFamily.backend,
    RawCtxPendingBackendInterpretation.program_compose] at supported
  have replay := complete source stage (RawCtxProtocolBackend.backend source writer)
    (simulateQ RawCtxPendingRetainedExecution.compiler client) state result supported
  simpa only [RawCtxPendingRetainedExecution.retained, RawCtxPendingBackendInterpretation.program_compose,
    RawCtxPendingRetainedExecution.compiler] using replay

/-- Chronological input logging does not change the same original supported result and shared state in this final-table replay. -/
theorem logged {A : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (result : Result × RawCtxSelectiveFamilyLog.LoggedState A)
    (supported : result ∈ support ((simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage) client).run state)) :
    Extends state.1.2.1 result.2.1.2.1 ∧
      (result.1, result.2.1.1) ∈ support ((simulateQ
        (RawCtxPendingRetainedExecution.retained source writer (view (productionStream source.crypto) result.2.1.2.1)) client).run state.1.1) := by
  have original : (result.1, result.2.1) ∈ support
      ((simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run state.1) := by
    rw [← RawCtxSelectiveFamilyLog.program_projection source writer stage client state.1 state.2, support_map]
    exact ⟨result, supported, rfl⟩
  exact pending source writer stage client state.1 (result.1, result.2.1) original

end BeaconcryptCore.Computational.RawCtxSelectiveReplay

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveReplay.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveReplay.complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveReplay.pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveReplay.pending

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveReplay.logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveReplay.logged
