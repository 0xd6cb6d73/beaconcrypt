import BeaconcryptCore.Computational.PqxdhPreparedOccurrencePaths
import BeaconcryptCore.Computational.PqxdhLaterInputAlias

/-! The concrete retained parent/child patch preserves the actual earlier cache and supplies the original saved query reply before its complete continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterRetainedPatch
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialNativeRetained RawCtxSelectedParentTable RawCtxCursorLineage
open RawCtxSelectedParentPrivatePatch PqxdhOrderedChainHybrids
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The actual parent insertion followed by the separately sampled child preserves every earlier binding on the explicit cache-miss and input-separation branch. -/
theorem parent_child_extends (state : PqxdhInitialNativeLog.State A N C)
    (address : JointKdfAddress) (parent output : FullOutput)
    (missing : state.1.1.2.1 address = none)
    (childMissing : state.1.1.2.1 (targetAddress (nextChain parent)) = none)
    (separate : targetAddress (nextChain parent) ≠ address) :
    Extends state.1.1.2.1
      ((PqxdhInitialNativeResponse.updated address parent state).1.1.2.1.cacheQuery
        (targetAddress (nextChain parent)) output) := by
  have childAbsent : (PqxdhInitialNativeResponse.updated address parent state).1.1.2.1
      (targetAddress (nextChain parent)) = none := by
    simpa only [PqxdhInitialNativeResponse.updated,
      QueryCache.cacheQuery_of_ne (spec := JointKdfRO) _ parent separate] using childMissing
  exact fun request response found =>
    PqxdhInitialNativeParentRandom.child_extends _ _ output childAbsent request response
      (PqxdhInitialNativeParentEvent.parent_extends state address parent missing request response found)

/-- The retained saved KDF request returns the exact cached parent with unchanged complete operational state. No selected-child or source freshness assumption enters this callback equation. -/
theorem frame_response (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (table : RawCtxKdfRequestTable.Table) (state : RetainedState A N C) (parent : FullOutput)
    (found : table (PqxdhInitialBuilderContext.address context) = some parent) :
    (retained source writer (view (productionStream source.crypto) table) external
      (PqxdhInitialBuilderContext.frame sender route decode context).1).run state =
        pure (PqxdhInitialParentBuilderContext.reply sender route decode context parent, state) := by
  let full : PqxdhInitialNativeLog.State A N C :=
    (((state.1, (table, ⟨List.Vector.replicate 32 0, 0⟩)), []), state.2)
  have actual := step_retained source writer external
    (PqxdhInitialBuilderContext.frame sender route decode context).1 full
  rw [PqxdhInitialNativeResponse.frame_hit source writer 0 external sender route decode context full parent found] at actual
  simpa only [map_pure, project, PqxdhInitialNativeResponse.updated, full] using actual.symm

/-- The complete saved frame, including its first retained parent request, is exactly the literal original resumption with that same full parent response. -/
theorem frame_completion (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (table : RawCtxKdfRequestTable.Table) (state : RetainedState A N C) (parent : FullOutput)
    (found : table (PqxdhInitialBuilderContext.address context.original) = some parent) :
    RawCtxPendingMixedPrefix.finish (retained source writer (view (productionStream source.crypto) table) external)
      (.pending (PqxdhInitialOriginContext.frame mark sender route decode context).1
        (PqxdhInitialOriginContext.frame mark sender route decode context).2, state) =
    (simulateQ (retained source writer (view (productionStream source.crypto) table) external)
      (PqxdhInitialOriginContext.resume mark sender route decode context
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run state := by
  simp only [RawCtxPendingMixedPrefix.finish, PqxdhInitialOriginContext.frame,
    frame_response source writer external sender route decode context.original table state parent found, pure_bind]

local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (N := N) (S := S) (B := B)

/-- On the complement of the already bounded actual earlier-input/parent alias event, the literal sampler supplies every condition needed for retaining its prefix under the parent/child patch. -/
theorem sample_one_extends (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original]) :
    Extends pending.2.1.1.1.2.1
      ((PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address pending.1.original)
        parent pending.2.1).1.1.2.1.cacheQuery (targetAddress (nextChain parent)) output) := by
  have actual := (PqxdhInitialPreparedParent.supported_pending source writer _ _ _ _ _ _ sender route decode _ _
    depth _ pending.2 pending.1).mp supported
  simp only [List.mem_append, List.mem_singleton, not_or] at safe
  apply parent_child_extends pending.2.1 _ parent output actual.2 ?_ safe.2
  cases found : pending.2.1.1.1.2.1 (targetAddress (nextChain parent)) with
  | none => rfl
  | some value => exact False.elim (safe.1
      (PqxdhLaterInputAlias.sample_one_covered source writer sender route decode depth start pending supported
        _ value found))

end BeaconcryptCore.Computational.PqxdhLaterRetainedPatch

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.parent_child_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.parent_child_extends
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.frame_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.frame_response
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.frame_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.frame_completion
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.sample_one_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterRetainedPatch.sample_one_extends
