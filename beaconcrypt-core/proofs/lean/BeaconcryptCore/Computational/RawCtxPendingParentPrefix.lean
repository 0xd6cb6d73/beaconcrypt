import BeaconcryptCore.Computational.RawCtxPendingParentCallbacks
import BeaconcryptCore.Computational.RawCtxStatefulPrefixInvariant
import BeaconcryptCore.Computational.RawCtxPendingNonKdfStore

/-!
This source prefix stops at the original matched predecessor callback, including a private-cache hit. The full native family, original dependent pending continuation, shared primitive state, private table and selected cursor are retained. Cache hits remain an explicit branch because they may advance to a later fresh child. These operational equations do not treat an absent predecessor miss as common completion and do not assume address separation or a selected input distribution.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingParentPrefix
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxPendingSelectiveFamily RawCtxPendingParentCallbacks

noncomputable def scan {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : State Auxiliary) :=
  RawCtxStatefulPendingPrefix.scan (parentCut cutStage) (handler source writer runStage)
    (program sender route decode client state) primitive

/-- Completing the matched-predecessor scan recovers the exact original complete selective source family, including cache-hit and early-completion branches. -/
theorem scan_complete {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :
    Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (scan source writer cutStage runStage sender route decode client state (primitive, store) >>=
        RawCtxPendingMixedPrefix.finish (handler source writer runStage)) =
      RawCtxSelectiveChainGame.family source writer runStage serverCount beaconCount sender route decode client state primitive store := by
  rw [scan, RawCtxStatefulPendingPrefix.scan_finish]
  exact (source_program source writer runStage sender route decode client state primitive store).symm


private theorem cut_selected {Auxiliary : Type} {serverCount beaconCount : Nat}
    (stage : Nat) (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary)
    (chosen : parentCut stage query state = true) : RawCtxPendingFamilyLiveTails.selected query = true := by
  rcases query with ((request | opening) | ((request | sealing) | request)) | request
  all_goals first | rfl | simp [parentCut, RawCtxSelectedFamilyContext.queryAddress,
    RawCtxSelectedFamilyContext.primitiveAddress] at chosen

/-- Every supported matched predecessor cut derives the original full source context and actual match/depth facts; no cache-miss premise removes the hit branch. -/
theorem reached_context {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive reached : State Auxiliary) (query : (Spec serverCount beaconCount).Domain)
    (next : (Spec serverCount beaconCount).Range query → OracleComp (Spec serverCount beaconCount)
      (Result × RawCtxSelectedFamilyContext.NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (scan source writer cutStage runStage sender route decode client state primitive)) :
    ∃ context : RawCtxSelectedFamilyContext.Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount,
      (⟨query, next⟩ : RawCtxSelectedFamilyContext.Frame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) =
        RawCtxSelectedFamilyContext.frame sender route decode context ∧
      RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) ∧
      matched reached.2.2 (RawCtxSelectedFamilyContext.address context) = true ∧ reached.2.2.depth = cutStage := by
  have origin := RawCtxStatefulPendingPrefix.pending_origin (parentCut cutStage) (handler source writer runStage)
    (program sender route decode client state) primitive reached query next supported
  have tail := RawCtxPendingFamilyLiveTails.program_tail sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined state.1, state.2)
    query next origin.2 (cut_selected cutStage query reached origin.1)
  obtain ⟨context, same⟩ := RawCtxSelectedFamilyContext.tail_context sender route decode query next tail
  have sameQuery := congrArg Sigma.fst same
  change query = (RawCtxSelectedFamilyContext.frame sender route decode context).1 at sameQuery
  have sameAddress : RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) := by
    rw [sameQuery]
    exact RawCtxSelectedFamilyContext.frame_address sender route decode context
  have chosen := origin.1
  rw [parentCut, sameAddress] at chosen
  exact ⟨context, same, sameAddress, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using chosen⟩

/-- Every actual unselected callback preserves the predecessor-depth invariant, including original opening, sealing, public work and optional reads. -/
theorem step_preserve {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage depth : Nat)
    (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary)
    (valid : state.2.2.depth ≤ depth) (unchosen : parentCut depth query state = false)
    (result : (Spec serverCount beaconCount).Range query × State Auxiliary)
    (supported : result ∈ support (((handler source writer stage) query).run state)) :
    result.2.2.2.depth ≤ depth := by
  cases found : RawCtxSelectedFamilyContext.queryAddress query with
  | none =>
    rw [RawCtxPendingNonKdfStore.callback_store source writer stage query found state result supported]
    exact valid
  | some address => exact kdf_preserve source writer stage depth query address found state valid unchosen result supported

/-- Both adjacent child stages share the same actual complete prefix before the matched predecessor callback, including the cached predecessor branch. -/
theorem scan_same {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : State Auxiliary) (initial : primitive.2.2.depth ≤ depth) :
    scan source writer depth (depth + 1) sender route decode client state primitive =
      scan source writer depth (depth + 2) sender route decode client state primitive := by
  apply RawCtxStatefulPrefixInvariant.scan_same (parentCut depth) _ _ (fun reached => reached.2.2.depth ≤ depth)
    _ _ (program sender route decode client state) primitive initial
  · intro query reached valid _
    exact RawCtxPendingSelectiveFamily.handler_same source writer (depth + 1) query reached
      (before_child depth query reached valid)
  · intro query reached valid unchosen result supported
    exact step_preserve source writer (depth + 1) depth query reached valid unchosen result supported

/-- Adjacent child stages resume one source-derived predecessor prefix, keeping actual cached and fresh predecessor responses and genuine completion before the predecessor. -/
theorem adjacent_complete {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) (initial : store.2.depth ≤ depth) :
    let common := scan source writer depth (depth + 1) sender route decode client state (primitive, store)
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (handler source writer (depth + 1))) =
      RawCtxSelectiveChainGame.family source writer (depth + 1) serverCount beaconCount sender route decode client state primitive store) ∧
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (handler source writer (depth + 2))) =
      RawCtxSelectiveChainGame.family source writer (depth + 2) serverCount beaconCount sender route decode client state primitive store) := by
  refine ⟨scan_complete source writer depth (depth + 1) sender route decode client state primitive store, ?_⟩
  rw [scan_same source writer depth sender route decode client state (primitive, store) initial]
  exact scan_complete source writer depth (depth + 2) sender route decode client state primitive store

/-- The actual completed or pending predecessor prefix remains at or before the chosen depth in the same complete reached state. -/
theorem scan_valid {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : State Auxiliary) (initial : primitive.2.2.depth ≤ depth)
    (result : RawCtxPendingMixedPrefix.Prefix (Spec serverCount beaconCount)
      (Result × RawCtxSelectedFamilyContext.NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
      (State Auxiliary))
    (supported : result ∈ support (scan source writer depth runStage sender route decode client state primitive)) :
    result.2.2.2.depth ≤ depth :=
  RawCtxStatefulPrefixInvariant.scan_valid (parentCut depth) (handler source writer runStage)
    (fun reached => reached.2.2.depth ≤ depth) (step_preserve source writer runStage depth)
    (program sender route decode client state) primitive initial result supported

end BeaconcryptCore.Computational.RawCtxPendingParentPrefix

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentPrefix.scan_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentPrefix.scan_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentPrefix.reached_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentPrefix.reached_context

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentPrefix.step_preserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentPrefix.step_preserve

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentPrefix.scan_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentPrefix.scan_same

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentPrefix.adjacent_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentPrefix.adjacent_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentPrefix.scan_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentPrefix.scan_valid
