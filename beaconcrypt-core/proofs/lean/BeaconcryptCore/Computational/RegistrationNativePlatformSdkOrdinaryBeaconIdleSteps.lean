-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveRun
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
open RegistrationNativePlatformSdkOrdinaryBeaconRetain (snapshot strong)

noncomputable def send (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (selected : current.1.beacons[logical]?=some owner) (tag : PqxdhRecordLiftInterface.InactivePhase)
    (inactive : current.1.server.world.world.1.owners[owner.worldOwner]?=some (.inactive tag))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (idle : AdapterPublicOrdinaryBeacon.Inactive self) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
  let call : RegistrationNativePlatformExtractedSdkAdaptive.Step (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := {
    Packet:=Unit
    sample:=pure ()
    sourceType:=Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.beacon.Beacon
    sourceReply:=fun _=>.ok (none,self)
    sourceState:=fun _=>(snapshot current self owner.worldOwner false).committed
    sourceCall:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed owner.worldOwner self <$>
      RegistrationNativePlatformExtractedSdkOrdinary.run
        (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased self bytes)
        current.1 current.2 (current.1.server.world.world.1.ownerRaw owner.worldOwner) false
    source_exact:=by
      rw [RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.send setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased self idle bytes,
        RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.pure_run]
      simp only [map_pure]
      rfl
    native:=fun _=>(none,(snapshot current self owner.worldOwner false).committed)
    native_exact:=by
      rw [RegistrationNativePlatformOrdinaryBeaconIdleNative.inactive_send setup wire reserve route current.1 logical
        (TranscriptAuthParts.absSlice bytes) owner selected tag inactive]
      simp only [map_pure,RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot_false]
      rfl
    store:=fun _ _=>strong setup view views created credential current before self owner.worldOwner false }
  refine {step:=call,observe:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observe,normal:=fun _ _=>⟨(none,self),rfl⟩,reply:=?_}
  intro packet _supported returned same
  cases same
  rfl

noncomputable def receive (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (selected : current.1.beacons[logical]?=some owner) (tag : PqxdhRecordLiftInterface.InactivePhase)
    (inactive : current.1.server.world.world.1.owners[owner.worldOwner]?=some (.inactive tag))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (idle : AdapterPublicOrdinaryBeacon.Inactive self) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
  let call : RegistrationNativePlatformExtractedSdkAdaptive.Step (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := {
    Packet:=Unit
    sample:=pure ()
    sourceType:=Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.beacon.Beacon
    sourceReply:=fun _=>.ok (none,self)
    sourceState:=fun _=>(snapshot current self owner.worldOwner true).committed
    sourceCall:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveRun.observed owner.worldOwner self <$>
      RegistrationNativePlatformExtractedSdkOrdinary.run
        (RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased self bytes)
        current.1 current.2 (current.1.server.world.world.1.ownerRaw owner.worldOwner) true
    source_exact:=by
      rw [RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.receive setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased self idle bytes,
        RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.pure_run]
      simp only [map_pure]
      rfl
    native:=fun _=>(none,(snapshot current self owner.worldOwner true).committed)
    native_exact:=by
      rw [RegistrationNativePlatformOrdinaryBeaconIdleNative.inactive_receive setup wire reserve route current.1 logical
        (TranscriptAuthParts.absSlice bytes) owner selected tag inactive]
      simp only [StateT.run_pure,map_pure,RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot_true]
      rfl
    store:=fun _ _=>strong setup view views created credential current before self owner.worldOwner true }
  refine {step:=call,observe:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveRun.observe,normal:=fun _ _=>⟨(none,self),rfl⟩,reply:=?_}
  intro packet _supported returned same
  cases same
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive
