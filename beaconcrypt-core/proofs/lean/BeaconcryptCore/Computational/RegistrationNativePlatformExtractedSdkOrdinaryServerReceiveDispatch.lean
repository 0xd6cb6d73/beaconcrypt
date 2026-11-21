-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
open RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun (Sample runner source native observed observe)
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
variable (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView)
variable (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
open RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep (route)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (credential : RegistrationNativeMldsa.Credential mlSource)

noncomputable def step (current : Native ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (bytes : Slice U8) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.base.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.base.objects.server.known_ids target=pure (views.peer before.base.objects.server.known_ids target,back target)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
          (.inl (.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
  cases routed:route (TranscriptAuthParts.absSlice bytes) with
  | none=>
      have refused : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused views before.base.objects.server bytes := by
        simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused,routed]
      let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.step setup reserve keyView failure erased view views setup.joint created credential
        current before.base bytes refused back get borrow
      apply RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call
      intro packet
      rw [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.objects]
      exact before.otkPublic
  | some key=>
      cases selected:views.peer before.base.objects.server.known_ids key with
      | none=>
          have refused : RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused views before.base.objects.server bytes := by
            simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.Refused,routed,selected]
          let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.step setup reserve keyView failure erased view views setup.joint created credential
            current before.base bytes refused back get borrow
          apply RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call
          intro packet
          rw [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRefused.objects]
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
              let call:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.live setup reserve length keyView failure erased view views setup.joint created credential
                current before.base bytes key remote routed selected kernel stored back lens get borrow
              apply RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call
              intro packet
              rw [RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.objects]
              exact before.otkPublic

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveDispatch.step
