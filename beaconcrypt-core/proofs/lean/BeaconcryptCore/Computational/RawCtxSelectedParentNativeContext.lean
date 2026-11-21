import BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler
import BeaconcryptCore.Computational.RawCtxSelectedParentContext

/-!
The supported original native frame resumes under its actual private pending interpreter and original optional live reader. Projection removes only the added frontend exposure ghost; the original owner, live history, complete shared primitive state and adaptive outside client are retained. These equalities identify the actual source continuation with the native context used by the retained-parent cut, with no supplied compatibility or security premise.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

noncomputable def live {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :=
  RawCtxGenericLiveRead.handler (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := Auxiliary)
    source writer prior entry target) RawCtxGenericLiveRead.nativeReader

/-- One original native live operation keeps its actual optional reply, owner and history, omitting only its operational exposure ghost. -/
theorem live_step {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (query : RawCtxSelectedLiveTrace.SourceSpec.Domain)
    (state : RawCtxGenericLiveRead.OuterState RatchetChain Metadata serverCount beaconCount) :
    Prod.map id Prod.fst <$> simulateQ (live (Auxiliary := Auxiliary) source writer prior entry target)
      ((RawCtxGenericLiveRead.compiler exposure sender decode owner query).run state) =
      (RawCtxSelectedParentLiveSource.nativeImpl source writer prior entry target sender decode owner query).run state.1 := by
  cases query with
  | inl request =>
    change Prod.map (id : RawCtxSelectedPublicTrace.SourceSpec.Range request → _) Prod.fst <$> _ = _
    rw [live, RawCtxGenericLiveRead.original_step, RawCtxSelectedParentNativeCompiler.compiler_step]
    simp only [RawCtxSelectedParentLiveSource.nativeImpl, StateT.run, Functor.map_map]
    rfl
  | inr read =>
    change Prod.map (id : RawCtxSelectedLiveRead.ReadSpec.Range read → _) Prod.fst <$> _ = _
    rw [live, RawCtxGenericLiveRead.read_step, map_pure]
    rfl

/-- The complete original live schedule equals the same native source execution with all actual history and shared effects retained. -/
theorem live_program {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp RawCtxSelectedLiveTrace.SourceSpec Result)
    (state : RawCtxGenericLiveRead.OuterState RatchetChain Metadata serverCount beaconCount) :
    Prod.map id Prod.fst <$> simulateQ (live (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxPendingLiveTails.program exposure sender decode owner client state) =
      (simulateQ (RawCtxSelectedParentLiveSource.nativeImpl source writer prior entry target sender decode owner) client).run state.1 := by
  rw [RawCtxPendingLiveTails.program, QueryImpl.simulateQ_mapStateTBase_run]
  exact map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (fun query state => live_step source writer prior entry target exposure sender decode owner query state) client state

private theorem receive_program {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := Auxiliary) source writer prior entry target)
      (simulateQ RawCtxPendingOwnerQueries.receiveForward (RawCtxPendingReceiveQueries.program effect)) =
      simulateQ (RawCtxSelectedParentSource.nativeReceive source writer prior entry target)
        (RawCtxInterpretedReceive.program (RawCtxChainReceive.nativeEffect id id effect)) := by
  have handler : RawCtxSelectedParentNativeCompiler.pending (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ
      RawCtxPendingOwnerQueries.receiveForward =
      RawCtxReachedParentCut.viewHandler (lookup prior entry target)
        (RawCtxReachedParentSource.sourceOpening source writer) := by
    funext query state
    cases query <;> simp [QueryImpl.compose, RawCtxSelectedParentNativeCompiler.pending,
      RawCtxSelectedParentNativeCompiler.original, RawCtxPendingOwnerQueries.receiveForward,
      RawCtxPendingOwnerQueries.erase, RawCtxReachedParentCut.viewHandler, RawCtxReachedParentCut.compiler,
      RawCtxRetainedTable.viewImpl, RawCtxReachedParentSource.chainView, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, handler, RawCtxReachedParentSource.view_native]

/-- The original pending receive resumption publishes the same optional opening and continues through the exact native owner tail. -/
theorem receive_tail {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (output : FullOutput) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := Auxiliary) source writer prior
      (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output))
      (RawCtxPendingOwnerTails.receiveTail sender decode before outside request
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))) =
      RawCtxSelectedParentOwnerCut.nativeReceiveTail source writer prior sender decode before outside request output := by
  simp only [RawCtxPendingOwnerTails.receiveTail, simulateQ_bind, receive_program,
    RawCtxSelectedParentOwnerCut.nativeReceiveTail]
  rw [← RawCtxChainReceive.normalResume_native]
  apply bind_congr
  intro result
  exact RawCtxSelectedParentNativeCompiler.compiler_schedule source writer prior
    (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output) sender decode _ _

/-- The original pending send keeps its advanced native state even after a failed seal, then runs the same outside owner client. -/
theorem send_tail {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := Auxiliary) source writer prior
      (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output))
      (RawCtxPendingOwnerTails.sendTail sender decode before outside request
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))) =
      RawCtxSelectedParentOwnerCut.nativeSendTail source writer prior sender decode before outside request output := by
  simp only [RawCtxPendingOwnerTails.sendTail, simulateQ_bind, simulateQ_spec_query,
    RawCtxSelectedParentOwnerCut.nativeSendTail, bind_assoc, pure_bind]
  have sealing (ready : RawCtxChainSend.Seal RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
      RawCtxSelectedParentNativeCompiler.pending (Auxiliary := Auxiliary) source writer prior
        (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output)
        (.inr (.inl (.inr ready))) = RawCtxSourceChainHandles.sendNative source writer
          (.inr (RawCtxInterpretedSend.nativeSeal (RawCtxChainSend.nativeSeal id id ready))) := by
    simp [RawCtxSelectedParentNativeCompiler.pending, QueryImpl.compose,
      RawCtxPendingOwnerQueries.erase, RawCtxSelectedParentNativeCompiler.original,
      RawCtxSelectedParentSource.nativeSend, OracleSpec.query]
  rw [sealing, RawCtxInterpretedSend.ready_native]
  apply bind_congr
  intro sealed
  exact RawCtxSelectedParentNativeCompiler.compiler_schedule source writer prior
    (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output) sender decode _ _

/-- Completing the original owner work precedes the same native history update and entire live outside client. -/
theorem lift_owner {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp RawCtxSelectedLiveTrace.SourceSpec Result)
    (work : OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain) (Value × Owner RatchetChain Metadata)) :
    Prod.map id Prod.fst <$> simulateQ (live (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxPendingLiveTails.liftOwner exposure sender decode owner history bad outside work) =
      (do let result ← simulateQ (RawCtxSelectedParentNativeCompiler.pending source writer prior entry target) work
          RawCtxSelectedParentLiveCut.nativeAfter source writer prior entry target sender decode owner history outside result) := by
  simp only [RawCtxPendingLiveTails.liftOwner, simulateQ_bind, map_bind]
  rw [← QueryImpl.simulateQ_compose, live, RawCtxGenericLiveRead.primitive_handler]
  apply bind_congr
  intro result
  exact live_program source writer prior entry target exposure sender decode owner
    (outside result.1) ((result.2, RawCtxProtocolReveals.tick history), bad)

noncomputable def frameReply {Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : RawCtxSelectedParentContext.Context Metadata Result serverCount beaconCount) (output : FullOutput) :
    (RawCtxGenericLiveRead.Spec RatchetChain).Range (RawCtxSelectedParentContext.frame exposure sender decode owner context).1 :=
  match context with
  | .receive _ _ _ _ _ _ _ => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)
  | .send _ _ _ _ _ _ _ => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)

/-- Resuming the exact reached native frame at the supplied complete response gives its original native context, retaining all original state except the frontend ghost. -/
theorem frame_native {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : RawCtxSelectedParentContext.Context Metadata Result serverCount beaconCount) (output : FullOutput) :
    Prod.map id Prod.fst <$> simulateQ (live (Auxiliary := Auxiliary) source writer prior
      (fromOutput (RawCtxSelectedParentContext.address context) output) (nextChain output))
      ((RawCtxSelectedParentContext.frame exposure sender decode owner context).2
        (frameReply exposure sender decode owner context output)) =
      RawCtxSelectedParentContext.native source writer prior sender decode owner context output := by
  cases context with
  | receive request history bad outside before ownerOutside pending =>
    simp only [RawCtxSelectedParentContext.frame, frameReply, RawCtxSelectedParentContext.address,
      lift_owner, receive_tail, RawCtxSelectedParentContext.native, RawCtxSelectedParentLiveCut.nativeReceiveTail]
  | send request history bad outside before ownerOutside pending =>
    simp only [RawCtxSelectedParentContext.frame, frameReply, RawCtxSelectedParentContext.address,
      lift_owner, send_tail, RawCtxSelectedParentContext.native, RawCtxSelectedParentLiveCut.nativeSendTail]

/-- The original selected callback returns precisely the frame response from its same retained full output and leaves shared state unchanged. -/
theorem frame_reply {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (exposure : RawCtxGenericLiveRead.Exposure RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : RawCtxSelectedParentContext.Context Metadata Result serverCount beaconCount) (output : FullOutput) :
    live (Auxiliary := Auxiliary) source writer prior
      (fromOutput (RawCtxSelectedParentContext.address context) output) (nextChain output)
      (RawCtxSelectedParentContext.frame exposure sender decode owner context).1 =
      pure (frameReply exposure sender decode owner context output) := by
  cases context <;> simp [live, RawCtxGenericLiveRead.handler, RawCtxSelectedParentContext.frame,
    RawCtxSelectedParentContext.address, frameReply, RawCtxSelectedParentNativeCompiler.pending,
    QueryImpl.compose, RawCtxPendingOwnerQueries.erase, RawCtxSelectedParentNativeCompiler.original,
    RawCtxReachedParentSource.chainView, RawCtxSelectedParentSource.response,
    lookup, fromOutput, OracleSpec.query,
    RawCtxSelectedPendingCut.requestAddress, RawCtxKdfRequestTable.address, RawCtxChainSend.nativeRequest]
  all_goals rw [show realize ⟨_, material output⟩ (nextChain output) = output from realize_fromOutput _ output]

end BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.live_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.live_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.live_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.live_program
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.receive_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.receive_tail
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.send_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.send_tail
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.lift_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.lift_owner
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.frame_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.frame_native
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.frame_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext.frame_reply
