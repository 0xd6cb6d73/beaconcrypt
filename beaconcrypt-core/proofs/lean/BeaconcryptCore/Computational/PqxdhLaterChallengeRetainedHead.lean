import BeaconcryptCore.Computational.PqxdhInitialNativeRetained
import BeaconcryptCore.Computational.PqxdhInitialNativeResponse
import BeaconcryptCore.Computational.RawCtxSelectedMessageDriver

/-!
The source frame's KDF head under the actual retained interpreter returns the retained full76 response without changing the complete interpreter state. This is an interpreter equation, including the real forwarding path, rather than an all-reply support argument.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedParentTable
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

private noncomputable def backend (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : Prior) :=
  RawCtxRetainedTable.viewImpl prior (RawCtxProtocolBackend.backend (Auxiliary := A) source writer) ∘ₛ RawCtxSelectiveKdfFamily.compiler

private theorem native_kdf (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (chain : RatchetChain) (state : RawCtxSharedPrimitive.SharedState A) :
    ((RawCtxInterpretedReceive.decodeResponse <$>
      ((backend source writer prior) ∘ₛ RawCtxServerServices.nativeLift)
        (.inl (RawCtxChainSend.nativeRequest chain))).run state) =
      pure (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
        (prior (RawCtxSelectedPendingCut.requestAddress chain))), state) := by
  simp [backend, QueryImpl.compose, RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler,
    OracleSpec.query, RawCtxRetainedTable.viewImpl,
    RawCtxSelectedPendingCut.requestAddress]

private theorem receive_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState A) :
    ((RawCtxPendingRetainedExecution.retained (S := S) (B := B) source writer prior)
      (.inl (.inl (.inl request)))).run state =
      pure (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
        (prior (RawCtxSelectedPendingCut.requestAddress request.request))), state) := by
  exact (congrArg (fun computation => computation.run state)
    (RawCtxPendingNativeCallbacks.receive_kdf
      ((backend source writer prior) ∘ₛ RawCtxServerServices.nativeLift)
      ((backend source writer prior) ∘ₛ RawCtxServerServices.publicLift) request)).trans
    (native_kdf source writer prior request.request state)
private theorem send_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState A) :
    ((RawCtxPendingRetainedExecution.retained (S := S) (B := B) source writer prior)
      (.inl (.inr (.inl (.inl request))))).run state =
      pure (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
        (prior (RawCtxSelectedPendingCut.requestAddress request.request))), state) := by
  exact (congrArg (fun computation => computation.run state)
    (RawCtxPendingNativeCallbacks.send_kdf
      ((backend source writer prior) ∘ₛ RawCtxServerServices.nativeLift)
      ((backend source writer prior) ∘ₛ RawCtxServerServices.publicLift) request)).trans
    (native_kdf source writer prior request.request state)

private theorem family_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B)
    (state : RawCtxSharedPrimitive.SharedState A) :
    ((RawCtxPendingRetainedExecution.retained source writer prior)
      (RawCtxSelectedFamilyContext.frame sender route decode context).1).run state =
      pure (RawCtxSelectedFamilyNativeContext.reply sender route decode context
        (prior (RawCtxSelectedFamilyContext.address context)), state) := by
  exact match context with
  | .family _ _ _ (.server _ _ _ _ (.owner _ _ _ _ _ (.receive _ _ pending))) =>
      receive_step source writer prior pending state
  | .family _ _ _ (.server _ _ _ _ (.owner _ _ _ _ _ (.send _ _ pending))) =>
      send_step source writer prior pending state
  | .family _ _ _ (.beacon _ _ _ _ _ _ (.receive _ _ pending)) =>
      receive_step source writer prior pending state
  | .family _ _ _ (.beacon _ _ _ _ _ _ (.send _ _ pending)) =>
      send_step source writer prior pending state

/-- Every complete original source frame head returns the retained response and leaves all interpreter fields unchanged. -/
theorem frame_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (state : PqxdhInitialNativeRetained.RetainedState A N C) :
    (PqxdhInitialNativeRetained.retained source writer prior external
      (PqxdhInitialBuilderContext.frame sender route decode context).1).run state =
      pure (PqxdhInitialParentBuilderContext.reply sender route decode context
        (prior (PqxdhInitialBuilderContext.address context)), state) := by
  rcases context with ((_ | _) | _)
  case inl.finish _ _ _ _ _ inner =>
    cases inner
    case receive before outside pending =>
      simpa only [PqxdhInitialNativeRetained.retained, PqxdhInitialBuilderContext.frame,
        PqxdhInitialPostContext.frame, RawCtxSelectedFamilyContext.ownerFrame,
        StateT.run, PqxdhInitialParentBuilderContext.reply, PqxdhInitialParentContext.reply,
        RawCtxSelectedFamilyNativeContext.ownerReply, PqxdhInitialBuilderContext.address,
        PqxdhInitialPostContext.address, RawCtxSelectedFamilyContext.ownerAddress, map_pure] using
        congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
          (receive_step (S := S) (B := B) source writer prior pending state.1)
    case send before outside pending =>
      simpa only [PqxdhInitialNativeRetained.retained, PqxdhInitialBuilderContext.frame,
        PqxdhInitialPostContext.frame, RawCtxSelectedFamilyContext.ownerFrame,
        StateT.run, PqxdhInitialParentBuilderContext.reply, PqxdhInitialParentContext.reply,
        RawCtxSelectedFamilyNativeContext.ownerReply, PqxdhInitialBuilderContext.address,
        PqxdhInitialPostContext.address, RawCtxSelectedFamilyContext.ownerAddress, map_pure] using
        congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
          (send_step (S := S) (B := B) source writer prior pending state.1)
  case inl.record request before outside inner =>
    simpa only [PqxdhInitialNativeRetained.retained, PqxdhInitialBuilderContext.frame,
      PqxdhInitialPostContext.frame, StateT.run, PqxdhInitialParentBuilderContext.reply,
      PqxdhInitialParentContext.reply, PqxdhInitialBuilderContext.address,
      PqxdhInitialPostContext.address, map_pure] using
      congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
        (family_step source writer prior sender route decode inner state.1)
  case inr context =>
    simpa only [PqxdhInitialNativeRetained.retained, PqxdhInitialBuilderContext.frame,
      PqxdhInitialBuilderContext.builderFrame, StateT.run, PqxdhInitialParentBuilderContext.reply,
      PqxdhInitialBuilderContext.address, map_pure] using
      congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
        (send_step (S := S) (B := B) source writer prior context.pending state.1)

/-- Origin metadata does not alter the real retained callback head or any interpreter field. -/
theorem origin_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (state : PqxdhInitialNativeRetained.RetainedState A N C) :
    (PqxdhInitialNativeRetained.retained source writer prior external
      (PqxdhInitialOriginContext.frame mark sender route decode context).1).run state =
      pure (PqxdhInitialParentBuilderContext.reply sender route decode context.original
        (prior (PqxdhInitialBuilderContext.address context.original)), state) :=
  frame_step source writer prior external sender route decode context.original state

/-- The retained parent slot wins even when its address aliases the selected child; this head equation needs no separation premise. -/
theorem parent_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) (output : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (atParent : PqxdhInitialBuilderContext.address context.original = entry.address)
    (state : PqxdhInitialNativeRetained.RetainedState A N C) :
    (PqxdhInitialNativeRetained.retained source writer
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external
      (PqxdhInitialOriginContext.frame mark sender route decode context).1).run state =
      pure (PqxdhInitialParentBuilderContext.reply sender route decode context.original
        (RawCtxSelectedParentEntry.realize entry target), state) := by
  simpa only [RawCtxSelectedMessageDriver.privateTable, lookup, atParent, ite_true] using
    origin_step source writer (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output)
      external mark sender route decode context state

/-- Executing the actual original parent head and its complete continuation equals resuming with the literal retained parent response in the same state. -/
theorem parent_execute (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) (output : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (atParent : PqxdhInitialBuilderContext.address context.original = entry.address)
    (state : PqxdhInitialNativeRetained.RetainedState A N C) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
      (((PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B).query
        (PqxdhInitialOriginContext.frame mark sender route decode context).1 :
          OracleComp (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B) _) >>=
        (PqxdhInitialOriginContext.frame mark sender route decode context).2)).run state =
      (simulateQ (PqxdhInitialNativeRetained.retained source writer
        (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original
            (RawCtxSelectedParentEntry.realize entry target)))).run state := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    parent_step source writer prior entry target output external mark sender route decode context atParent state,
    pure_bind]

end BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.frame_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.frame_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.origin_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.origin_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.parent_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.parent_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.parent_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead.parent_execute
