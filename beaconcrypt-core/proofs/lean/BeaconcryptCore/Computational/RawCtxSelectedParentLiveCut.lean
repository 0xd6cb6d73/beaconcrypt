import BeaconcryptCore.Computational.RawCtxSelectedParentOwnerCut

/-!
The original receive/send owner tail finishes before the same live history update and original external client. Its stopped Slot program is constructed from the original pending state, owner, public source continuation and material coordinate alone. The complete native-to-Slot equations preserve all optional replies and shared state, and project away only the added exposure ghost. Actual supported tail provenance is established by the live source grammar; no arbitrary native continuation law is assumed here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

abbrev OwnerSpec := RawCtxSelectedPublicTrace.SourceSpec
abbrev SourceSpec := RawCtxSelectedLiveTrace.SourceSpec

noncomputable def nativeAfter {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount)
    (outside : Value → OracleComp SourceSpec Result) (result : Value × Owner RatchetChain Metadata) :=
  (simulateQ (RawCtxSelectedParentLiveSource.nativeImpl (Auxiliary := Auxiliary)
    source writer prior entry target sender decode owner) (outside result.1)).run
      (result.2, RawCtxProtocolReveals.tick history)

private theorem lift_interpreted {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (reader : RawCtxGenericLiveRead.Reader Slot) (outside : Value → OracleComp SourceSpec Result)
    (work : OracleComp (RawCtxPendingOwnerQueries.Spec Slot) (Value × Owner Slot Metadata)) :
    simulateQ (RawCtxSelectedParentCompiler.live (Auxiliary := Auxiliary) source writer prior entry response reader)
      (RawCtxPendingLiveTails.liftOwner RawCtxSelectedLiveRead.exposed sender decode owner history bad outside work) =
      (do let result ← simulateQ (RawCtxSelectedParentCompiler.pending source writer prior entry response) work
          simulateQ (RawCtxSelectedParentCompiler.live source writer prior entry response reader)
            (RawCtxPendingLiveTails.afterOwner RawCtxSelectedLiveRead.exposed sender decode owner history bad outside result)) := by
  simp only [RawCtxPendingLiveTails.liftOwner, simulateQ_bind]
  rw [← QueryImpl.simulateQ_compose, RawCtxSelectedParentCompiler.live,
    RawCtxGenericLiveRead.primitive_handler]

/-- Original live history and the full external client follow the same owner result; the private exposure flag alone is omitted from native state. -/
theorem after_map {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp SourceSpec Result) (result : Value × Owner Slot Metadata) :
    nativeAfter (Auxiliary := Auxiliary) source writer prior entry target sender decode owner history outside
      (Prod.map id (mapOwner target) result) =
      Prod.map id (RawCtxSelectedParentLiveSource.project target) <$>
        simulateQ (RawCtxSelectedParentCompiler.live source writer prior entry (childResponse prior entry target)
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)))
          (RawCtxPendingLiveTails.afterOwner RawCtxSelectedLiveRead.exposed sender decode owner history bad outside result) := by
  rw [RawCtxPendingLiveTails.afterOwner, RawCtxSelectedParentCompiler.live_program]
  exact RawCtxSelectedParentLiveSource.schedule_map source writer prior entry target sender decode owner
    (outside result.1) ((result.2, RawCtxProtocolReveals.tick history), bad)

noncomputable def receiveStop {Metadata Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp SourceSpec Result) (before : Owner RatchetChain Metadata)
    (ownerOutside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp OwnerSpec Value)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (value : Material) :=
  RawCtxPendingLiveTails.liftOwner RawCtxSelectedLiveRead.exposed sender decode owner history bad outside
    (RawCtxSelectedParentOwnerCut.receiveStop sender decode before ownerOutside request value)

noncomputable def nativeReceiveTail {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount)
    (outside : Value → OracleComp SourceSpec Result) (before : Owner RatchetChain Metadata)
    (ownerOutside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp OwnerSpec Value)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (output : FullOutput) :=
  RawCtxSelectedParentOwnerCut.nativeReceiveTail (Auxiliary := Auxiliary) source writer prior sender decode before ownerOutside request output >>=
    nativeAfter source writer prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
      (nextChain output) sender decode owner history outside

/-- The actual receive owner tail, original history update and full external live client resume from the same predecessor response through a program that does not inspect its next-chain coordinate. -/
theorem receive_cut {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp SourceSpec Result) (before : Owner RatchetChain Metadata)
    (ownerOutside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp OwnerSpec Value)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (output : FullOutput) :
    nativeReceiveTail (Auxiliary := Auxiliary) source writer prior sender decode owner history outside before ownerOutside request output =
      Prod.map id (RawCtxSelectedParentLiveSource.project (nextChain output)) <$>
        simulateQ (RawCtxSelectedParentCompiler.live source writer prior
          (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
          (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output))
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain output))))
          (receiveStop sender decode owner history bad outside before ownerOutside request (material output)) := by
  rw [nativeReceiveTail, receiveStop, lift_interpreted, RawCtxSelectedParentOwnerCut.receive_cut,
    bind_map_left, map_bind]
  apply bind_congr
  intro result
  exact after_map source writer prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
    (nextChain output) sender decode owner history bad outside result

noncomputable def sendStop {Metadata Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp SourceSpec Result) (before : Owner RatchetChain Metadata)
    (ownerOutside : Option RawCtxSourceSend.Encrypted → OracleComp OwnerSpec Value)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (value : Material) :=
  RawCtxPendingLiveTails.liftOwner RawCtxSelectedLiveRead.exposed sender decode owner history bad outside
    (RawCtxSelectedParentOwnerCut.sendStop sender decode before ownerOutside request value)

noncomputable def nativeSendTail {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount)
    (outside : Value → OracleComp SourceSpec Result) (before : Owner RatchetChain Metadata)
    (ownerOutside : Option RawCtxSourceSend.Encrypted → OracleComp OwnerSpec Value)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) :=
  RawCtxSelectedParentOwnerCut.nativeSendTail (Auxiliary := Auxiliary) source writer prior sender decode before ownerOutside request output >>=
    nativeAfter source writer prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
      (nextChain output) sender decode owner history outside

/-- The actual send owner tail, original history update and full external live client resume from the same predecessor response through a program that does not inspect its next-chain coordinate. -/
theorem send_cut {Metadata Auxiliary Value Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp SourceSpec Result) (before : Owner RatchetChain Metadata)
    (ownerOutside : Option RawCtxSourceSend.Encrypted → OracleComp OwnerSpec Value)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (output : FullOutput) :
    nativeSendTail (Auxiliary := Auxiliary) source writer prior sender decode owner history outside before ownerOutside request output =
      Prod.map id (RawCtxSelectedParentLiveSource.project (nextChain output)) <$>
        simulateQ (RawCtxSelectedParentCompiler.live source writer prior
          (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
          (childResponse prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output) (nextChain output))
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain output))))
          (sendStop sender decode owner history bad outside before ownerOutside request (material output)) := by
  rw [nativeSendTail, sendStop, lift_interpreted, RawCtxSelectedParentOwnerCut.send_cut,
    bind_map_left, map_bind]
  apply bind_congr
  intro result
  exact after_map source writer prior (fromOutput (RawCtxSelectedPendingCut.requestAddress request.request) output)
    (nextChain output) sender decode owner history bad outside result

end BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut.after_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut.after_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut.receive_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut.receive_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut.send_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLiveCut.send_cut
