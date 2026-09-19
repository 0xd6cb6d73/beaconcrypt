import BeaconcryptCore.Computational.RawCtxPendingBackendInterpretation
import BeaconcryptCore.Computational.RawCtxLoggedParentResponse
import BeaconcryptCore.Computational.RawCtxRetainedTable

/-!
Once the selected cursor is past a substitution stage, the complete remaining original pending family program uses the actual fixed source with its full retained private cache. The mutable table and cursor are projected only after the entire continuation. All original family/history/ratchet state and shared primitive effects remain present. Public services retain the real source. No cache consistency, key separation or successful callback premise is added.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingRetainedExecution
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectiveChainGame
open RawCtxPendingSelectiveFamily RawCtxSelectedParentTable RawCtxKdfRequestTable
variable {A Result : Type} {S B : Nat}

noncomputable def compiler := RawCtxPendingFamilyNative.handler (serverCount := S) (beaconCount := B) RawCtxSelectiveKdfFamily.compiler

/-- Past the chosen stage, the exact complete pending source execution is saturated and keeps all original effects under stage zero. -/
theorem saturated (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (Spec S B) Result) (state : State A) (past : stage ≤ state.2.2.depth) :
    (simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run state =
      (simulateQ (RawCtxPendingSelectiveFamily.handler source writer 0) client).run state := by
  simp only [RawCtxPendingSelectiveFamily.handler, backend, RawCtxPendingBackendInterpretation.program_compose]
  exact RawCtxSelectiveChainPrefix.saturated_run source stage (RawCtxProtocolBackend.backend source writer)
    (simulateQ compiler client) state past

noncomputable def retained (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :=
  RawCtxPendingFamilyNative.handler (serverCount := S) (beaconCount := B)
    (RawCtxRetainedTable.viewImpl prior (RawCtxProtocolBackend.backend (Auxiliary := A) source writer) ∘ₛ RawCtxSelectiveKdfFamily.compiler)

/-- Projecting only the completed private table/cursor yields the same retained prior lookup and complete original result/shared state, even for earlier hybrid cache entries. -/
theorem retained_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (Spec S B) Result) (state : State A) (past : stage ≤ state.2.2.depth) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run state =
      (simulateQ (retained source writer (view (productionStream source.crypto) state.2.1)) client).run state.1 := by
  rw [saturated source writer stage client state past]
  simp only [RawCtxPendingSelectiveFamily.handler, backend, retained, RawCtxPendingBackendInterpretation.program_compose]
  have zero := RawCtxSelectiveChainGame.zero_complete source (RawCtxProtocolBackend.backend source writer)
    (simulateQ compiler client) state.1 state.2.1 state.2.2
  have projected := congrArg (fun computation : ProbComp (Result × (RawCtxSharedPrimitive.SharedState A × Table)) =>
    (fun result => (result.1, result.2.1)) <$> computation) zero
  simpa only [Functor.map_map, RawCtxSelectiveChainGame.project, compiler, Prod.eta] using projected.trans
    (RawCtxRetainedTable.complete source (RawCtxProtocolBackend.backend source writer)
      (simulateQ compiler client) state.1 state.2.1).symm

/-- Erasing only the private log/table/cursor after the complete saturated execution preserves the same native result, original history and shared primitive state under the retained view. -/
theorem logged_retained (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (Spec S B) Result) (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (past : stage ≤ state.1.2.2.depth) :
    (fun result => (result.1, result.2.1.1)) <$>
      (simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage) client).run state =
      (simulateQ (retained source writer (view (productionStream source.crypto) state.1.2.1)) client).run state.1.1 := by
  have erased := congrArg (fun computation : ProbComp (Result × State A) =>
    (fun result => (result.1, result.2.1)) <$> computation)
    (RawCtxSelectiveFamilyLog.program_projection source writer stage client state.1 state.2)
  simpa only [Functor.map_map, Prod.eta] using erased.trans (retained_run source writer stage client state.1 past)

/-- After the actual matched predecessor response, the real child stage resumes the original full family frame under the retained prior plus this exact parent entry. -/
theorem parent_resume {M P I D K : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (depth : Nat) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (output : FullOutput)
    (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (selected : matched state.1.2.2 (RawCtxSelectedFamilyContext.address context) = true)
    (sameDepth : state.1.2.2.depth = depth) :
    (fun result => (result.1, result.2.1.1)) <$>
      RawCtxLoggedParentResponse.resume source writer (depth + 1) sender route decode context output state =
      (simulateQ (retained source writer (lookup (view (productionStream source.crypto) state.1.2.1)
        (RawCtxSelectedParentEntry.fromOutput (RawCtxSelectedFamilyContext.address context) output)
        (PqxdhOrderedChainHybrids.nextChain output)))
        ((RawCtxSelectedFamilyContext.frame sender route decode context).2
          (RawCtxSelectedFamilyNativeContext.reply sender route decode context output))).run state.1.1 := by
  have past : depth + 1 ≤ (RawCtxLoggedParentResponse.updated context output state).1.2.2.depth := by
    simp only [RawCtxLoggedParentResponse.updated, advance_depth, selected, if_true, sameDepth]
    exact Nat.le_refl _
  have actual := logged_retained source writer (depth + 1)
    ((RawCtxSelectedFamilyContext.frame sender route decode context).2
      (RawCtxSelectedFamilyNativeContext.reply sender route decode context output))
    (RawCtxLoggedParentResponse.updated context output state) past
  have cache : view (productionStream source.crypto) (state.1.2.1.cacheQuery (RawCtxSelectedFamilyContext.address context) output) =
      lookup (view (productionStream source.crypto) state.1.2.1)
        (RawCtxSelectedParentEntry.fromOutput (RawCtxSelectedFamilyContext.address context) output)
        (PqxdhOrderedChainHybrids.nextChain output) := by
    funext request
    exact view_recorded _ _ _ request _
  simpa only [RawCtxLoggedParentResponse.resume, RawCtxLoggedParentResponse.updated, cache] using actual

end BeaconcryptCore.Computational.RawCtxPendingRetainedExecution

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.saturated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.saturated

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.retained_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.retained_run

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.logged_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.logged_retained

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.parent_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingRetainedExecution.parent_resume
