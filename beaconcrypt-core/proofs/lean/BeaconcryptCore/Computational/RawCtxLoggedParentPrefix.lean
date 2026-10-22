import BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog

/-!
The actual common predecessor prefix retains its chronological private inputs together with the full native pending frame, family, history, shared primitive state, table and cursor. The matched predecessor selector includes cache hits. The same source prefix is used by both adjacent child stages; the retained log supplies cache-address provenance rather than an assumed enumeration of an arbitrary table.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxLoggedParentPrefix
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxPendingSelectiveFamily RawCtxPendingParentCallbacks
open RawCtxSelectiveFamilyLog (LoggedState)

noncomputable def scan {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (initial : LoggedState Auxiliary) :=
  RawCtxStatefulPendingPrefix.scan (fun query reached => parentCut depth query reached.1)
    (RawCtxSelectiveFamilyLog.handler source writer runStage) (program sender route decode client state) initial

private theorem step_same {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (query : (Spec serverCount beaconCount).Domain) (state : LoggedState Auxiliary)
    (valid : state.1.2.2.depth ≤ depth) :
    ((RawCtxSelectiveFamilyLog.handler source writer (depth + 1) query).run state) =
      ((RawCtxSelectiveFamilyLog.handler source writer (depth + 2) query).run state) := by
  have same := RawCtxPendingSelectiveFamily.handler_same source writer (depth + 1) query state.1
    (before_child depth query state.1 valid)
  simpa only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp] using
    congrArg (fun computation => (fun result => (result.1, (result.2, RawCtxSelectiveFamilyLog.inputs query state.2))) <$> computation) same

private theorem step_preserve {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage depth : Nat)
    (query : (Spec serverCount beaconCount).Domain) (state : LoggedState Auxiliary)
    (valid : state.1.2.2.depth ≤ depth) (unchosen : parentCut depth query state.1 = false)
    (result : (Spec serverCount beaconCount).Range query × LoggedState Auxiliary)
    (supported : result ∈ support (((RawCtxSelectiveFamilyLog.handler source writer stage) query).run state)) :
    result.2.1.2.2.depth ≤ depth := by
  simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨reply, actual, rfl⟩ := supported
  exact RawCtxPendingParentPrefix.step_preserve source writer stage depth query state.1 valid unchosen reply actual

/-- Both adjacent child stages share the same complete predecessor prefix and chronological input log, including cached predecessor callbacks. -/
theorem scan_same {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (initial : LoggedState Auxiliary) (valid : initial.1.2.2.depth ≤ depth) :
    scan source writer depth (depth + 1) sender route decode client state initial =
      scan source writer depth (depth + 2) sender route decode client state initial := by
  apply RawCtxStatefulPrefixInvariant.scan_same (fun query reached => parentCut depth query reached.1)
    _ _ (fun reached => reached.1.2.2.depth ≤ depth) _ _ (program sender route decode client state) initial valid
  · intro query reached invariant _
    exact step_same source writer depth query reached invariant
  · intro query reached invariant unchosen result supported
    exact step_preserve source writer (depth + 1) depth query reached invariant unchosen result supported

/-- Resuming the saved logged prefix recovers the same complete native source family with its full chronological log retained. -/
theorem scan_complete {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (initial : LoggedState Auxiliary) :
    Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (scan source writer depth runStage sender route decode client state initial >>=
        RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer runStage)) =
      RawCtxSelectiveFamilyLog.family source writer runStage sender route decode client state initial.1.1 initial.1.2 initial.2 := by
  rw [scan, RawCtxStatefulPendingPrefix.scan_finish]
  rfl

/-- Removing only the private input log gives the exact original matched-predecessor prefix and complete saved frame. -/
theorem scan_projection {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (initial : LoggedState Auxiliary) :
    (fun result => (result.1, result.2.1)) <$> scan source writer depth runStage sender route decode client state initial =
      RawCtxPendingParentPrefix.scan source writer depth runStage sender route decode client state initial.1 :=
  RawCtxSelectiveFamilyLog.scan_projection source writer runStage (parentCut depth)
    (program sender route decode client state) initial.1 initial.2

/-- Every supported matched predecessor cut derives the original full source context and actual match/depth facts; no cache-miss premise removes the hit branch. -/
theorem reached_context {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (initial reached : LoggedState Auxiliary) (query : (Spec serverCount beaconCount).Domain)
    (next : (Spec serverCount beaconCount).Range query → OracleComp (Spec serverCount beaconCount)
      (Result × RawCtxSelectedFamilyContext.NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (scan source writer cutStage runStage sender route decode client state initial)) :
    ∃ context : RawCtxSelectedFamilyContext.Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount,
      (⟨query, next⟩ : RawCtxSelectedFamilyContext.Frame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) =
        RawCtxSelectedFamilyContext.frame sender route decode context ∧
      RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) ∧
      matched reached.1.2.2 (RawCtxSelectedFamilyContext.address context) = true ∧ reached.1.2.2.depth = cutStage := by
  have projected : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached.1) ∈ support
      (RawCtxPendingParentPrefix.scan source writer cutStage runStage sender route decode client state initial.1) := by
    rw [← scan_projection source writer cutStage runStage sender route decode client state initial]
    simp only [support_map, Set.mem_image]
    exact ⟨(RawCtxPendingMixedPrefix.Stopped.pending query next, reached), supported, rfl⟩
  exact RawCtxPendingParentPrefix.reached_context source writer cutStage runStage sender route decode client state
    initial.1 reached.1 query next projected

/-- Both original adjacent native source games resume one actual logged predecessor prefix, retaining early completion and every cached predecessor response. -/
theorem adjacent_complete {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (initial : LoggedState Auxiliary) (valid : initial.1.2.2.depth ≤ depth) :
    let common := scan source writer depth (depth + 1) sender route decode client state initial
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer (depth + 1))) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2) ∧
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer (depth + 2))) =
      RawCtxSelectiveFamilyLog.family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2) := by
  refine ⟨scan_complete source writer depth (depth + 1) sender route decode client state initial, ?_⟩
  rw [scan_same source writer depth sender route decode client state initial valid]
  exact scan_complete source writer depth (depth + 2) sender route decode client state initial

/-- An actual source prefix from its empty private cache derives both the original matched context and provenance of every reached cache address from the same chronological log. -/
theorem reached_empty {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (cursor : Cursor) (past : List JointKdfAddress)
    (reached : LoggedState Auxiliary) (query : (Spec serverCount beaconCount).Domain)
    (next : (Spec serverCount beaconCount).Range query → OracleComp (Spec serverCount beaconCount)
      (Result × RawCtxSelectedFamilyContext.NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (scan source writer cutStage runStage sender route decode client state ((primitive, (∅, cursor)), past))) :
    RawCtxSelectiveFamilyLog.Covered reached ∧
    ∃ context : RawCtxSelectedFamilyContext.Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount,
      (⟨query, next⟩ : RawCtxSelectedFamilyContext.Frame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) =
        RawCtxSelectedFamilyContext.frame sender route decode context ∧
      RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) ∧
      matched reached.1.2.2 (RawCtxSelectedFamilyContext.address context) = true ∧ reached.1.2.2.depth = cutStage := by
  exact ⟨RawCtxSelectiveFamilyLog.scan_covered source writer runStage
    (fun query logged => parentCut cutStage query logged.1) (program sender route decode client state)
    ((primitive, (∅, cursor)), past) (RawCtxSelectiveFamilyLog.empty_covered primitive cursor past)
    (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) supported,
    reached_context source writer cutStage runStage sender route decode client state
      ((primitive, (∅, cursor)), past) reached query next supported⟩

end BeaconcryptCore.Computational.RawCtxLoggedParentPrefix

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.scan_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.scan_same

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.scan_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.scan_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.scan_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.scan_projection

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.reached_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.reached_context

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.adjacent_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.adjacent_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.reached_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentPrefix.reached_empty
