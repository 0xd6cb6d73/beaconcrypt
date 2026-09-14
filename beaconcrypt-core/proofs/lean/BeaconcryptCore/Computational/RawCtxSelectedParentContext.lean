import BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut

/-!
Concrete retained-parent contexts are extracted from the same supported original live source stop. Each context stores the original owner request and typed outside client, original owner and its typed outside client, complete pending receive/send request, and live history/ghost. Its stopped observer uses only the retained material coordinate. This is an actual source grammar witness, not an arbitrary supplied cut or native continuation compatibility assumption.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentContext
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

abbrev OwnerSpec := RawCtxSelectedPublicTrace.SourceSpec
abbrev SourceSpec := RawCtxSelectedLiveTrace.SourceSpec

inductive Context (Metadata Result : Type) (serverCount beaconCount : Nat) : Type where
  | receive (request : OwnerSpec.Domain)
      (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
      (outside : OwnerSpec.Range request → OracleComp SourceSpec Result)
      (before : Owner RatchetChain Metadata)
      (ownerOutside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp OwnerSpec (OwnerSpec.Range request))
      (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
  | send (request : OwnerSpec.Domain)
      (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
      (outside : OwnerSpec.Range request → OracleComp SourceSpec Result)
      (before : Owner RatchetChain Metadata)
      (ownerOutside : Option RawCtxSourceSend.Encrypted → OracleComp OwnerSpec (OwnerSpec.Range request))
      (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)

abbrev Frame (Metadata Result : Type) (serverCount beaconCount : Nat) :=
  Σ query, (RawCtxGenericLiveRead.Spec RatchetChain).Range query → OracleComp (RawCtxGenericLiveRead.Spec RatchetChain)
    (Result × RawCtxGenericLiveRead.OuterState RatchetChain Metadata serverCount beaconCount)

noncomputable def frame {Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    Context Metadata Result serverCount beaconCount → Frame Metadata Result serverCount beaconCount
  | .receive _ history bad outside before ownerOutside pending =>
      ⟨.inl (.inl (.inl pending)), fun reply => RawCtxPendingLiveTails.liftOwner exposure sender decode owner history bad outside
        (RawCtxPendingOwnerTails.receiveTail sender decode before ownerOutside pending reply)⟩
  | .send _ history bad outside before ownerOutside pending =>
      ⟨.inl (.inr (.inl (.inl pending))), fun reply => RawCtxPendingLiveTails.liftOwner exposure sender decode owner history bad outside
        (RawCtxPendingOwnerTails.sendTail sender decode before ownerOutside pending reply)⟩

def address {Metadata Result : Type} {serverCount beaconCount : Nat} :
    Context Metadata Result serverCount beaconCount → JointKdfAddress
  | .receive _ _ _ _ _ _ pending => RawCtxSelectedPendingCut.requestAddress pending.request
  | .send _ _ _ _ _ _ pending => RawCtxSelectedPendingCut.requestAddress pending.request

noncomputable def stopped {Metadata Result : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : Context Metadata Result serverCount beaconCount) (value : Material) :
    OracleComp (RawCtxGenericLiveRead.Spec Slot)
      (Result × RawCtxSelectedParentLiveSource.LabelState Metadata serverCount beaconCount) :=
  match context with
  | .receive _ history bad outside before ownerOutside pending =>
      RawCtxSelectedParentLiveCut.receiveStop sender decode owner history bad outside before ownerOutside pending value
  | .send _ history bad outside before ownerOutside pending =>
      RawCtxSelectedParentLiveCut.sendStop sender decode owner history bad outside before ownerOutside pending value

noncomputable def native {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : Context Metadata Result serverCount beaconCount) (output : FullOutput) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp
      (Result × RawCtxSelectedParentLiveSource.NativeState Metadata serverCount beaconCount) :=
  match context with
  | .receive _ history _ outside before ownerOutside pending =>
      RawCtxSelectedParentLiveCut.nativeReceiveTail source writer prior sender decode owner history outside before ownerOutside pending output
  | .send _ history _ outside before ownerOutside pending =>
      RawCtxSelectedParentLiveCut.nativeSendTail source writer prior sender decode owner history outside before ownerOutside pending output

/-- Every source-derived live tail has one concrete original receive/send context, including both exact outside clients and the complete history. -/
theorem tail_context {Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (query : (RawCtxGenericLiveRead.Spec RatchetChain).Domain)
    (next : (RawCtxGenericLiveRead.Spec RatchetChain).Range query → OracleComp (RawCtxGenericLiveRead.Spec RatchetChain)
      (Result × RawCtxGenericLiveRead.OuterState RatchetChain Metadata serverCount beaconCount))
    (tail : RawCtxPendingLiveTails.Tail exposure sender decode owner query next) :
    ∃ context : Context Metadata Result serverCount beaconCount,
      (⟨query, next⟩ : Frame Metadata Result serverCount beaconCount) = frame exposure sender decode owner context := by
  cases tail with
  | original request history bad outside query next originalTail =>
    cases originalTail with
    | receive before ownerOutside pending => exact ⟨.receive request history bad outside before ownerOutside pending, rfl⟩
    | send before ownerOutside pending => exact ⟨.send request history bad outside before ownerOutside pending, rfl⟩

def queryAddress : (RawCtxGenericLiveRead.Spec RatchetChain).Domain → Option JointKdfAddress
  | .inl (.inl (.inl pending)) => some (RawCtxSelectedPendingCut.requestAddress pending.request)
  | .inl (.inr (.inl (.inl pending))) => some (RawCtxSelectedPendingCut.requestAddress pending.request)
  | _ => none

/-- The retained address is the same concrete request in the original stopped source frame, with no index or parent supplied independently. -/
theorem frame_address {Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (context : Context Metadata Result serverCount beaconCount) :
    queryAddress (frame exposure sender decode owner context).1 = some (address context) := by
  cases context <;> rfl

/-- The same concrete receive/send context gives the complete native continuation from its predecessor output and the material-only stopped observer. -/
theorem native_cut {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : Context Metadata Result serverCount beaconCount) (output : FullOutput) :
    native (Auxiliary := Auxiliary) source writer prior sender decode owner context output =
      Prod.map id (RawCtxSelectedParentLiveSource.project (nextChain output)) <$>
        simulateQ (RawCtxSelectedParentCompiler.live source writer prior (fromOutput (address context) output)
          (childResponse prior (fromOutput (address context) output) (nextChain output))
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain output))))
          (stopped sender decode owner context (material output)) := by
  cases context with
  | receive request history bad outside before ownerOutside pending =>
    exact RawCtxSelectedParentLiveCut.receive_cut source writer prior sender decode owner history bad outside before ownerOutside pending output
  | send request history bad outside before ownerOutside pending =>
    exact RawCtxSelectedParentLiveCut.send_cut source writer prior sender decode owner history bad outside before ownerOutside pending output

/-- A supported scan of the original complete live client derives its exact context and original pending address before the selected response, retaining the full reached primitive state. -/
theorem reached_context {Metadata Base Result : Type} {serverCount beaconCount : Nat}
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (impl : QueryImpl (RawCtxGenericLiveRead.Spec RatchetChain) (StateT Base ProbComp))
    (client : OracleComp SourceSpec Result)
    (state : RawCtxGenericLiveRead.OuterState RatchetChain Metadata serverCount beaconCount)
    (index : Nat) (initial reached : Base) (query : (RawCtxGenericLiveRead.Spec RatchetChain).Domain)
    (next : (RawCtxGenericLiveRead.Spec RatchetChain).Range query → OracleComp (RawCtxGenericLiveRead.Spec RatchetChain)
      (Result × RawCtxGenericLiveRead.OuterState RatchetChain Metadata serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxPendingMixedPrefix.scan RawCtxPendingLiveTails.selected impl
        (RawCtxPendingLiveTails.program exposure sender decode owner client state) index initial)) :
    ∃ context : Context Metadata Result serverCount beaconCount,
      (⟨query, next⟩ : Frame Metadata Result serverCount beaconCount) = frame exposure sender decode owner context ∧
      queryAddress query = some (address context) := by
  obtain ⟨context, same⟩ := tail_context exposure sender decode owner query next
    (RawCtxPendingLiveTails.reached_tail exposure sender decode owner impl client state index initial reached query next supported)
  refine ⟨context, same, ?_⟩
  have sameQuery := congrArg Sigma.fst same
  change query = (frame exposure sender decode owner context).1 at sameQuery
  rw [sameQuery]
  exact frame_address exposure sender decode owner context

end BeaconcryptCore.Computational.RawCtxSelectedParentContext

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentContext.tail_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentContext.tail_context

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentContext.frame_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentContext.frame_address

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentContext.native_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentContext.native_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentContext.reached_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentContext.reached_context
