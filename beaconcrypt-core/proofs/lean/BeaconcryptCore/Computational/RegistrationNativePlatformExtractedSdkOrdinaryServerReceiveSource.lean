-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerSender
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (M)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
open AdapterPublicWrapperStorage
open AdapterPublicWrapperRustT (RustT)

def returned (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap) :
    RustM AdapterRecordStatefulReceive.Result →RustM (Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server)
  | .ok result =>.ok (result.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back
      (some (AdapterPublicOrdinaryEnvelope.manager result.1)))
  | .fail error =>.fail error
  | .div =>.div

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] primitives [FrameDispatchFallback.Operations] in
private theorem returned_run (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (work : M Platform (RustM AdapterRecordStatefulReceive.Result)) :
    (do
      let result←(⟨work⟩ :RustT (M Platform) _)
      pure (result.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back
        (some (AdapterPublicOrdinaryEnvelope.manager result.1)))).run =returned self remote back <$>work := by
  rw [RustT.run_bind]
  simp only [RustT.run_pure]
  rw [←bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;>rfl

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem source_kernel (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (target : U64) :
    letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
    returned self remote back <$>
      RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup codec erased.bytes kernel target
        remote.peer.binding.associated_data bytes =
    (RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receiveKernel
      self bytes target remote back kernel :RustT (M Platform) _).run := by
  let := RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
  unfold RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receiveKernel RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample
  simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
  rw [AdapterPublicOrdinaryReceiveGate.prepare]
  cases selected : (RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).bind
      (AdapterPublicOrdinaryReceiveGate.admitted target) with
  | none=>rfl
  | some frame=>
      dsimp only
      rw [RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.begin_effect]
      rw [←returned_run self remote back]
      simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
      obtain ⟨pending,admitted⟩:=BeaconcryptCore.PanicFreedom.RecordEffects.begin_record_receive_total
        kernel frame.sequence frame.ciphertext remote.peer.binding.associated_data frame.sender
      simp only [admitted]
      rfl

theorem source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (views : Views) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (target : U64)
    (routed : (RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).map CborProductionBoundary.NativeFrame.sender=some target)
    (selected : views.peer self.known_ids target=some remote)
    (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
      ∀key,AdapterPublicOrdinaryServerLookup.read (m:=M Platform) self.known_ids key=pure (views.peer self.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
      ∀key,AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) self.known_ids key=pure (views.peer self.known_ids key,back key)) :
    returned self remote (back target) <$>
      RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup codec erased.bytes kernel target
        remote.peer.binding.associated_data bytes =
    RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup codec reserve view failure erased self bytes := by
  let := RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
  rw [RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_receive setup codec reserve view failure erased views self bytes back get borrow,
    AdapterPublicOrdinaryServerSender.source,routed]
  simp only [pure_bind]
  rw [selected,RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receive_kernel self bytes target remote (back target) kernel stored]
  exact source_kernel setup codec reserve view failure erased self remote (back target) kernel bytes target

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.source_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.source_kernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.source
