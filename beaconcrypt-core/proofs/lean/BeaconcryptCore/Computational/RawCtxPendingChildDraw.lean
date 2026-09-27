import BeaconcryptCore.Computational.RawCtxSelectiveSingleDraw
import BeaconcryptCore.Computational.RawCtxPendingRetainedExecution

/-!
The original complete pending family execution consumes the single remaining private child draw. Its actual source Result, family/history and shared primitive state are retained, while only completed private table/cursor/log instrumentation is projected. The early comparison draw is an evaluated-distribution splice and has its own sampling bill. The actual cache-miss condition remains explicit until the source input log/candidate consumer discharges it; no source branch or public HKDF computation is removed.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingChildDraw
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectiveChainGame
open RawCtxPendingSelectiveFamily RawCtxSelectedParentTable RawCtxKdfRequestTable RawCtxPendingRetainedExecution
variable {A Result : Type} {S B : Nat}

/-- The complete original pending source program uses the exact one-remaining-child splice, with every original backend effect and result preserved. -/
theorem pending_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (client : OracleComp (Spec S B) Result) (state : State A)
    (missing : state.2.1 (cursorAddress state.2.2) = none) :
    𝒮[(fun result => (result.1, result.2.1)) <$>
      (simulateQ (RawCtxPendingSelectiveFamily.handler source writer (state.2.2.depth + 1)) client).run state] =
      𝒮[(($ᵗ FullOutput) >>= fun output =>
        (simulateQ (retained source writer (view (productionStream source.crypto)
          (state.2.1.cacheQuery (cursorAddress state.2.2) output))) client).run state.1)] := by
  simp only [RawCtxPendingSelectiveFamily.handler, backend, retained, RawCtxPendingBackendInterpretation.program_compose]
  simpa only [compiler, Prod.eta] using RawCtxSelectiveSingleDraw.single_uniform source
    (RawCtxProtocolBackend.backend source writer) (simulateQ compiler client) state.1 state.2.1 state.2.2 missing

/-- The same one-child splice removes only completed private log/table/cursor instrumentation and retains the full original native result/history/shared state. -/
theorem logged_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (client : OracleComp (Spec S B) Result) (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (missing : state.1.2.1 (cursorAddress state.1.2.2) = none) :
    𝒮[(fun result => (result.1, result.2.1.1)) <$>
      (simulateQ (RawCtxSelectiveFamilyLog.handler source writer (state.1.2.2.depth + 1)) client).run state] =
      𝒮[(($ᵗ FullOutput) >>= fun output =>
        (simulateQ (retained source writer (view (productionStream source.crypto)
          (state.1.2.1.cacheQuery (cursorAddress state.1.2.2) output))) client).run state.1.1)] := by
  have erased := congrArg (fun computation : ProbComp (Result × State A) =>
    (fun result => (result.1, result.2.1)) <$> computation)
    (RawCtxSelectiveFamilyLog.program_projection source writer (state.1.2.2.depth + 1) client state.1 state.2)
  have complete : (fun result => (result.1, result.2.1.1)) <$>
      (simulateQ (RawCtxSelectiveFamilyLog.handler source writer (state.1.2.2.depth + 1)) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (RawCtxPendingSelectiveFamily.handler source writer (state.1.2.2.depth + 1)) client).run state.1 := by
    simpa only [Functor.map_map, Prod.eta] using erased
  exact (congrArg evalSPMF complete).trans (pending_uniform source writer client state.1 missing)

/-- After the actual matched parent response, the next source stage draws its remaining child early and keeps the entire original native family continuation under the retained private cache. -/
theorem parent_random {M P I D K : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (depth : Nat) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (parent : FullOutput)
    (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (selected : matched state.1.2.2 (RawCtxSelectedFamilyContext.address context) = true)
    (sameDepth : state.1.2.2.depth = depth)
    (missing : (RawCtxLoggedParentResponse.updated context parent state).1.2.1
      (cursorAddress (RawCtxLoggedParentResponse.updated context parent state).1.2.2) = none) :
    let reached := RawCtxLoggedParentResponse.updated context parent state
    𝒮[(fun result => (result.1, result.2.1.1)) <$>
      RawCtxLoggedParentResponse.resume source writer (depth + 2) sender route decode context parent state] =
      𝒮[(($ᵗ FullOutput) >>= fun child =>
        (simulateQ (retained source writer (view (productionStream source.crypto)
          (reached.1.2.1.cacheQuery (cursorAddress reached.1.2.2) child)))
          ((RawCtxSelectedFamilyContext.frame sender route decode context).2
            (RawCtxSelectedFamilyNativeContext.reply sender route decode context parent))).run state.1.1)] := by
  have actual := logged_uniform source writer
    ((RawCtxSelectedFamilyContext.frame sender route decode context).2
      (RawCtxSelectedFamilyNativeContext.reply sender route decode context parent))
    (RawCtxLoggedParentResponse.updated context parent state) missing
  have stage : (RawCtxLoggedParentResponse.updated context parent state).1.2.2.depth + 1 = depth + 2 := by
    simp [RawCtxLoggedParentResponse.updated, advance_depth, selected, sameDepth]
  simp only [RawCtxLoggedParentResponse.updated] at stage
  simpa only [RawCtxLoggedParentResponse.resume, RawCtxLoggedParentResponse.updated, stage] using actual

/-- Recording the actual parent input preserves complete private-cache address provenance for every full parent response, including a retained cache hit. -/
theorem updated_covered {M P I D K : Type}
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (parent : FullOutput)
    (state : RawCtxSelectiveFamilyLog.LoggedState A) (covered : RawCtxSelectiveFamilyLog.Covered state) :
    RawCtxSelectiveFamilyLog.Covered (RawCtxLoggedParentResponse.updated context parent state) := by
  intro address output found
  by_cases same : address = RawCtxSelectedFamilyContext.address context
  · subst address
    simp [RawCtxLoggedParentResponse.updated]
  · have previous : state.1.2.1 address = some output := by
      simpa only [RawCtxLoggedParentResponse.updated,
        QueryCache.cacheQuery_of_ne (spec := JointKdfRO) state.1.2.1 parent same] using found
    simp only [RawCtxLoggedParentResponse.updated, List.mem_append]
    exact Or.inl (covered address output previous)

/-- A child input absent from the actual chronological prior inputs and the just-executed parent input cannot already occur in the reached private cache. -/
theorem child_missing {M P I D K : Type}
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (parent : FullOutput)
    (state : RawCtxSelectiveFamilyLog.LoggedState A) (covered : RawCtxSelectiveFamilyLog.Covered state)
    (child : JointKdfAddress)
    (unlisted : child ∉ state.2 ++ [RawCtxSelectedFamilyContext.address context]) :
    (RawCtxLoggedParentResponse.updated context parent state).1.2.1 child = none := by
  cases present : (RawCtxLoggedParentResponse.updated context parent state).1.2.1 child with
  | none => rfl
  | some output =>
      exact False.elim (unlisted ((updated_covered context parent state covered) child output present))

/-- The random-child source equation applies on the complement of the actual prior/parent input event, with cache-miss provenance derived from that source log. -/
theorem parent_random_of_unlisted {M P I D K : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (depth : Nat) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (parent : FullOutput)
    (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (selected : matched state.1.2.2 (RawCtxSelectedFamilyContext.address context) = true)
    (sameDepth : state.1.2.2.depth = depth)
    (covered : RawCtxSelectiveFamilyLog.Covered state)
    (unlisted : cursorAddress (RawCtxLoggedParentResponse.updated context parent state).1.2.2 ∉
      state.2 ++ [RawCtxSelectedFamilyContext.address context]) :
    let reached := RawCtxLoggedParentResponse.updated context parent state
    𝒮[(fun result => (result.1, result.2.1.1)) <$>
      RawCtxLoggedParentResponse.resume source writer (depth + 2) sender route decode context parent state] =
      𝒮[(($ᵗ FullOutput) >>= fun child =>
        (simulateQ (retained source writer (view (productionStream source.crypto)
          (reached.1.2.1.cacheQuery (cursorAddress reached.1.2.2) child)))
          ((RawCtxSelectedFamilyContext.frame sender route decode context).2
            (RawCtxSelectedFamilyNativeContext.reply sender route decode context parent))).run state.1.1)] := by
  exact parent_random source writer depth sender route decode context parent state selected sameDepth
    (child_missing context parent state covered _ unlisted)

end BeaconcryptCore.Computational.RawCtxPendingChildDraw

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildDraw.pending_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildDraw.pending_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildDraw.logged_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildDraw.logged_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildDraw.parent_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildDraw.parent_random

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildDraw.updated_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildDraw.updated_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildDraw.child_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildDraw.child_missing

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildDraw.parent_random_of_unlisted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildDraw.parent_random_of_unlisted
