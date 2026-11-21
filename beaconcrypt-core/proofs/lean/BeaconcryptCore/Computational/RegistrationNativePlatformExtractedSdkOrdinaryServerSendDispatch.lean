-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
open RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun (Sample runner source native observed observe)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView)
variable (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
variable (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (credential : RegistrationNativeMldsa.Credential mlSource)

noncomputable def step (current : Native ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (key : U64) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
          (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))) mlSource).run current.1).run current.2) := by
  cases selected:views.peer before.base.objects.server.known_ids key with
  | none=>
      let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.step setup RegistrationNativeConcreteCodec.wire reserve keyView failure erased route view views setup.joint created credential
        current before.base bytes key selected (back key) (get key) (borrow key)
      apply RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call
      intro packet
      rw [RegistrationNativePlatformExtractedSdkOrdinaryServerSendMissing.objects]
      exact before.otkPublic
  | some remote=>
      cases stored:remote.peer.ratchet.refined.kernel with
      | none=>
          exfalso
          obtain ⟨records,_present,_sender,_identity,related⟩:=before.base.server.peers
          have missing : records.records.server.peers key=none := by
            rw [←(related key).1,selected]
            simp only [Option.bind_some,peerView,stored,Option.map_none]
          have impossible: true=false := by
            simpa only [selected,missing,Option.isSome_some,Option.isSome_none] using (related key).2
          cases impossible
      | some kernel=>
          let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.live setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views setup.joint created credential
            current before.base bytes key remote selected kernel stored (back key) (lens key) (get key) (borrow key)
          apply RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call
          intro packet
          rw [RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.objects]
          exact before.otkPublic

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendDispatch.step
