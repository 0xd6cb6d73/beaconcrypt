import BeaconcryptCore.Computational.RawCtxSelectedParentCompiler
import BeaconcryptCore.Computational.RawCtxSelectedPendingCut

/-!
A concrete original owner tail is retagged at its original pending KDF request, before the new chain coordinate is drawn. The stopped program retains the original owner, its actual public source continuation and all pending controls. The operational equations consume the exact full predecessor response and preserve complete native resumption, publication and later public/record effects. Reached support is supplied by the separately proved source grammar, not by an arbitrary continuation compatibility premise.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

abbrev SourceSpec := RawCtxSelectedPublicTrace.SourceSpec

def knownOwner {Metadata : Type} : Owner RatchetChain Metadata → Owner Slot Metadata :=
  RawCtxGenericOwnerMap.mapOwner (RawCtxChainInterpretation.mapChains Slot.known Slot.known)

/-- Retagging a pre-draw owner never compares with or reads the later target coordinate. -/
theorem known_owner {Metadata : Type} (target : RootOutput) (before : Owner RatchetChain Metadata) :
    mapOwner target (knownOwner before) = before := by
  rcases before with ⟨kernel, sender, ad, metadata, attempts⟩
  cases kernel
  rfl

noncomputable def receiveStop {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (value : Material) :=
  RawCtxPendingOwnerTails.receiveTail sender decode (knownOwner before) outside
    (RawCtxSelectedPendingCut.receivePending request) (.hidden, RawCtxFreshChainCut.concreteMaterial value)

noncomputable def nativeReceiveTail {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (output : FullOutput) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (Result × Owner RatchetChain Metadata) := do
  let entry := fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output
  let result ← simulateQ (RawCtxSelectedParentSource.nativeReceive source writer prior entry (nextChain output))
    (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalResume
      (RawCtxChainReceive.nativeKdf id id request)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))))
  let published := RawCtxChainOwner.publish before result
  (simulateQ (nativeOwner source writer prior entry (nextChain output) sender decode) (outside published.1)).run published.2

private theorem receive_pending_program {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse)
    (effect : RawCtxChainReceive.Effect Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxSelectedParentCompiler.pending (Auxiliary := Auxiliary) source writer prior entry response)
      (simulateQ RawCtxPendingOwnerQueries.receiveForward (RawCtxPendingReceiveQueries.program effect)) =
      simulateQ (RawCtxSelectedParentSource.labelReceive source writer prior entry response)
        (RawCtxChainReceive.program effect) := by
  have equation : RawCtxSelectedParentCompiler.pending (Auxiliary := Auxiliary) source writer prior entry response ∘ₛ
      RawCtxPendingOwnerQueries.receiveForward =
      RawCtxSelectedParentSource.labelReceive source writer prior entry response ∘ₛ RawCtxPendingReceiveQueries.forward := by
    funext query
    cases query <;> simp [QueryImpl.compose, RawCtxSelectedParentCompiler.pending,
      RawCtxPendingOwnerQueries.receiveForward, RawCtxPendingOwnerQueries.erase,
      RawCtxSelectedParentCompiler.original, RawCtxPendingReceiveQueries.forward, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, equation, QueryImpl.simulateQ_compose,
    RawCtxPendingReceiveQueries.program_forward]

private theorem receive_stop_interpreted {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (value : Material) :
    simulateQ (RawCtxSelectedParentCompiler.pending (Auxiliary := Auxiliary) source writer prior entry response)
      (receiveStop sender decode before outside request value) =
      (do let result ← simulateQ (RawCtxSelectedParentSource.labelReceive source writer prior entry response)
            (RawCtxChainReceive.program (RawCtxSelectedPendingCut.receiveStop request value))
          let published := RawCtxChainOwner.publish (knownOwner before) result
          (simulateQ (labelOwner source writer prior entry response sender decode) (outside published.1)).run published.2) := by
  simp only [receiveStop, RawCtxPendingOwnerTails.receiveTail, simulateQ_bind, receive_pending_program]
  apply bind_congr
  intro result
  exact RawCtxSelectedParentCompiler.owner_program source writer prior entry response sender decode _ _

/-- The actual pending receive finishes its original publication and original adaptive owner/public continuation after the same full predecessor response. -/
theorem receive_cut {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (output : FullOutput) :
    nativeReceiveTail (Auxiliary := Auxiliary) source writer prior sender decode before outside request output =
      Prod.map id (mapOwner (nextChain output)) <$>
        simulateQ (RawCtxSelectedParentCompiler.pending source writer prior
          (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
          (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output)))
          (receiveStop sender decode before outside request (material output)) := by
  rw [nativeReceiveTail, receive_stop_interpreted, RawCtxSelectedPendingCut.receive_cut,
    bind_map_left, map_bind]
  apply bind_congr
  intro result
  have equation := RawCtxSelectedParentOwner.schedule_map (Auxiliary := Auxiliary) source writer prior
    (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output) sender decode
    (outside result.2) (RawCtxChainOwner.publish (knownOwner before) result).2
  exact equation

noncomputable def sendStop {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (value : Material) :=
  RawCtxPendingOwnerTails.sendTail sender decode (knownOwner before) outside
    (RawCtxSelectedPendingCut.sendPending request) (.hidden, RawCtxFreshChainCut.concreteMaterial value)

noncomputable def nativeSendTail {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (Result × Owner RatchetChain Metadata) := do
  let result ← (do
    let ready := RawCtxSourceSend.resumeSend
      (RawCtxInterpretedSend.nativeKdf (RawCtxChainSend.nativeKdf id id request))
      (RawCtxKdfRequestTable.fullResponse output)
    let sealed ← RawCtxSourceChainHandles.sendNative source writer (.inr ready)
    pure (ready.advanced, sealed))
  let entry := fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output
  (simulateQ (nativeOwner source writer prior entry (nextChain output) sender decode) (outside result.2)).run
    {before with kernel := result.1.refined}

private theorem send_stop_interpreted {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (value : Material) :
    simulateQ (RawCtxSelectedParentCompiler.pending (Auxiliary := Auxiliary) source writer prior entry response)
      (sendStop sender decode before outside request value) =
      (do let ready := RawCtxSelectedPendingCut.sendStop request value
          let sealed ← RawCtxSelectedParentSource.labelSend source writer prior entry response (.inr ready)
          (simulateQ (labelOwner source writer prior entry response sender decode) (outside sealed)).run
            {knownOwner before with kernel := ready.advanced}) := by
  simp only [sendStop, RawCtxPendingOwnerTails.sendTail, simulateQ_bind, simulateQ_spec_query]
  have equation : RawCtxSelectedParentCompiler.pending (Auxiliary := Auxiliary) source writer prior entry response
      (.inr (.inl (.inr (RawCtxSelectedPendingCut.sendStop request value)))) =
      RawCtxSelectedParentSource.labelSend source writer prior entry response
        (.inr (RawCtxSelectedPendingCut.sendStop request value)) := by
    simp [RawCtxSelectedParentCompiler.pending, QueryImpl.compose, RawCtxPendingOwnerQueries.erase,
      RawCtxSelectedParentCompiler.original, OracleSpec.query]
  simp only [RawCtxSelectedPendingCut.sendStop] at equation
  rw [equation]
  apply bind_congr
  intro sealed
  exact RawCtxSelectedParentCompiler.owner_program source writer prior entry response sender decode _ _

/-- The actual selected send retains its advanced kernel even when sealing fails, then resumes the same complete original owner/public client. -/
theorem send_cut {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner RatchetChain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) :
    nativeSendTail (Auxiliary := Auxiliary) source writer prior sender decode before outside request output =
      Prod.map id (mapOwner (nextChain output)) <$>
        simulateQ (RawCtxSelectedParentCompiler.pending source writer prior
          (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
          (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output)))
          (sendStop sender decode before outside request (material output)) := by
  rw [nativeSendTail, send_stop_interpreted, RawCtxSelectedPendingCut.send_cut source writer prior request output
    (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output)),
    bind_map_left, map_bind]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro sealed
  exact RawCtxSelectedParentOwner.schedule_map (Auxiliary := Auxiliary) source writer prior
    (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output) sender decode
    (outside sealed) {knownOwner before with kernel := (RawCtxSelectedPendingCut.sendStop request (material output)).advanced}

end BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut.known_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut.known_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut.receive_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut.receive_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut.send_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut.send_cut
