import BeaconcryptCore.Computational.RawCtxPendingChildDraw
import BeaconcryptCore.Computational.RawCtxRetainedParentBackend
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch

/-!
Both actual source stages after a matched parent callback run the same complete saved family continuation. The real stage uses the retained original child value; the random stage uses one full child draw and a private-only address patch. All original native result, family, history and shared state are retained through the concrete material-only context relation. Prior/parent input collisions remain explicit source branches. Public HKDF and original optional reads remain real. These equations allow one common final source event; they do not assert that a state-dependent event is itself an executable target-free observer.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingChildRealization
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open RawCtxSelectiveChainGame RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedParentPrivatePatch
open RawCtxSelectedFamilyContext RawCtxSelectedParentFamilyMap RawCtxSelectedParentCalls
variable {M P I D K A Result : Type} {S B : Nat}

/-- The actual matched parent callback advances to exactly its returned next-chain input. -/
theorem child_address (context : Context M P I D K Result S B) (parent : FullOutput)
    (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (selected : matched state.1.2.2 (address context) = true) :
    cursorAddress (RawCtxLoggedParentResponse.updated context parent state).1.2.2 =
      targetAddress (nextChain parent) := by
  simp only [RawCtxLoggedParentResponse.updated, advance, selected, if_true]
  change FixedHkdfDomain.ratchet.address (nextChain parent).toList = _
  simp [targetAddress, RawCtxSelectedPendingCut.requestAddress, RawCtxChainSend.nativeRequest,
    RawCtxKdfRequestTable.address, RawCtxFreshChainCut.concreteChain,
    PqxdhRefinement.absBytes,
    Function.comp_def, Refinement.ProtocolComposition.absByte_concreteByte]
  have info : List.map PqxdhRefinement.absByte ratchet.SYM_RATCHET_INFO.val = Pqxdh.INFO_R := by
    simpa only [PqxdhRefinement.absBytes, pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO
  rw [info]
  rfl

/-- After separate parent and child inputs, the actual twice-updated private cache is exactly the retained parent lookup with only the child address patched. -/
theorem child_table (fallback : Prior) (cache : RawCtxKdfRequestTable.Table)
    (parentAddress : JointKdfAddress) (parent child : FullOutput)
    (separate : targetAddress (nextChain parent) ≠ parentAddress) :
    view fallback ((cache.cacheQuery parentAddress parent).cacheQuery (targetAddress (nextChain parent)) child) =
      lookup (privatePatch (view fallback cache) (nextChain parent) child)
        (fromOutput parentAddress parent) (nextChain parent) := by
  funext request
  simp only [lookup, realize_fromOutput]
  by_cases sameChild : request = targetAddress (nextChain parent)
  · subst request
    simp [view, privatePatch, fromOutput, separate]
  · by_cases sameParent : request = parentAddress
    · subst request
      simp [view, fromOutput, sameChild]
    · simp [view, privatePatch, fromOutput, sameChild, sameParent, QueryCache.cacheQuery_of_ne]

/-- The actual real-child stage is the same material-only stopped family interpreter, preserving the entire original native result and shared state. -/
theorem real (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context M P I D K Result S B)
    (parent : FullOutput) (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (selected : matched state.1.2.2 (address context) = true) (sameDepth : state.1.2.2.depth = depth) :
    (fun result => (result.1, result.2.1.1)) <$>
      RawCtxLoggedParentResponse.resume source writer (depth + 1) sender route decode context parent state =
      Prod.map (Prod.map id (RawCtxGenericFamilyLive.mapState (nativeKernel (nextChain parent)))) id <$>
        (simulateQ (labelLive source writer (view (productionStream source.crypto) state.1.2.1)
          (fromOutput (address context) parent) (nextChain parent))
          (stopped sender route decode context (material parent))).run state.1.1 := by
  rw [RawCtxPendingRetainedExecution.parent_resume source writer depth sender route decode context parent state selected sameDepth,
    RawCtxRetainedParentBackend.retained_live]
  exact RawCtxSelectedFamilyNativeContext.frame_run source writer (view (productionStream source.crypto) state.1.2.1)
    sender route decode context parent state.1.1

/-- Away from the recorded prior/parent input event, the actual random-child stage is the complete same stopped family interpreter with one private child patch. -/
theorem random (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context M P I D K Result S B)
    (parent : FullOutput) (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (selected : matched state.1.2.2 (address context) = true) (sameDepth : state.1.2.2.depth = depth)
    (covered : RawCtxSelectiveFamilyLog.Covered state)
    (unlisted : targetAddress (nextChain parent) ∉ state.2 ++ [address context]) :
    𝒮[(fun result => (result.1, result.2.1.1)) <$>
      RawCtxLoggedParentResponse.resume source writer (depth + 2) sender route decode context parent state] =
      𝒮[(($ᵗ FullOutput) >>= fun child =>
        Prod.map (Prod.map id (RawCtxGenericFamilyLive.mapState (nativeKernel (nextChain parent)))) id <$>
          (simulateQ (labelLive source writer
            (privatePatch (view (productionStream source.crypto) state.1.2.1) (nextChain parent) child)
            (fromOutput (address context) parent) (nextChain parent))
            (stopped sender route decode context (material parent))).run state.1.1)] := by
  have separate : targetAddress (nextChain parent) ≠ address context := by
    intro same
    exact unlisted (by simp [same])
  have actual := RawCtxPendingChildDraw.parent_random_of_unlisted source writer depth sender route decode context parent state
    selected sameDepth covered (by simpa only [child_address context parent state selected] using unlisted)
  refine actual.trans ?_
  apply evalSPMF_bind_congr' ($ᵗ FullOutput)
  intro child
  have table : view (productionStream source.crypto)
      ((RawCtxLoggedParentResponse.updated context parent state).1.2.1.cacheQuery
        (cursorAddress (RawCtxLoggedParentResponse.updated context parent state).1.2.2) child) =
      lookup (privatePatch (view (productionStream source.crypto) state.1.2.1) (nextChain parent) child)
        (fromOutput (address context) parent) (nextChain parent) := by
    rw [child_address context parent state selected]
    exact child_table (productionStream source.crypto) state.1.2.1 (address context) parent child separate
  rw [table, RawCtxRetainedParentBackend.retained_live]
  exact congrArg evalSPMF (RawCtxSelectedFamilyNativeContext.frame_run source writer
    (privatePatch (view (productionStream source.crypto) state.1.2.1) (nextChain parent) child)
    sender route decode context parent state.1.1)

/-- Outside the actual prior-input event, patching the child's original fixed-source value leaves the complete retained prior lookup unchanged. -/
theorem real_patch (source : FixedHkdfSha512NoSaltSource) (context : Context M P I D K Result S B)
    (parent : FullOutput) (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (covered : RawCtxSelectiveFamilyLog.Covered state)
    (unlisted : targetAddress (nextChain parent) ∉ state.2 ++ [address context]) :
    privatePatch (view (productionStream source.crypto) state.1.2.1) (nextChain parent)
      (productionStream source.crypto (targetAddress (nextChain parent))) =
      view (productionStream source.crypto) state.1.2.1 := by
  have missing : state.1.2.1 (targetAddress (nextChain parent)) = none := by
    cases present : state.1.2.1 (targetAddress (nextChain parent)) with
    | none => rfl
    | some output =>
        exact False.elim (unlisted (List.mem_append.mpr (Or.inl (covered _ output present))))
  funext query
  by_cases same : query = targetAddress (nextChain parent)
  · subst query
    simp [privatePatch, view, missing]
  · simp [privatePatch, same]

/-- The real source stage uses the same privately patched stopped-program interface as the random stage, with its actual fixed-source child response and one common complete final output. -/
theorem real_patched (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context M P I D K Result S B)
    (parent : FullOutput) (state : RawCtxSelectiveFamilyLog.LoggedState A)
    (selected : matched state.1.2.2 (address context) = true) (sameDepth : state.1.2.2.depth = depth)
    (covered : RawCtxSelectiveFamilyLog.Covered state)
    (unlisted : targetAddress (nextChain parent) ∉ state.2 ++ [address context]) :
    (fun result => (result.1, result.2.1.1)) <$>
      RawCtxLoggedParentResponse.resume source writer (depth + 1) sender route decode context parent state =
      Prod.map (Prod.map id (RawCtxGenericFamilyLive.mapState (nativeKernel (nextChain parent)))) id <$>
        (simulateQ (labelLive source writer
          (privatePatch (view (productionStream source.crypto) state.1.2.1) (nextChain parent)
            (productionStream source.crypto (targetAddress (nextChain parent))))
          (fromOutput (address context) parent) (nextChain parent))
          (stopped sender route decode context (material parent))).run state.1.1 := by
  rw [real_patch source context parent state covered unlisted]
  exact real source writer depth sender route decode context parent state selected sameDepth

end BeaconcryptCore.Computational.RawCtxPendingChildRealization

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildRealization.child_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildRealization.child_address

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildRealization.child_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildRealization.child_table

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildRealization.real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildRealization.real

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildRealization.random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildRealization.random

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildRealization.real_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildRealization.real_patch

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingChildRealization.real_patched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingChildRealization.real_patched
