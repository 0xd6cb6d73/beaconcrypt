-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

theorem source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel)) (bytes : Slice U8) :
    AdapterPublicOrdinaryKernel.returned self control binding <$>
      RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup codec erased.bytes kernel
        control.server_binding.identity_key_id binding.associated_data bytes =
    RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup codec reserve view failure erased self bytes := by
  rw [RegistrationNativePlatformExtractedSdkOrdinaryBeacon.receive_source setup codec reserve view failure erased self control binding kernel stored bytes]
  unfold RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample RegistrationNativePlatformExtractedSdkOrdinaryBeacon.receive
  rw [AdapterPublicOrdinaryReceiveGate.prepare]
  have restored : {self with state:=beaconcrypt_public_wrapper.beacon.BeaconState.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel)}=self := by
    rw [←stored]
  cases selected:(RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).bind
      (AdapterPublicOrdinaryReceiveGate.admitted control.server_binding.identity_key_id) with
  | none=>
      simp only [map_pure,AdapterPublicOrdinaryKernel.returned_exact]
      exact congrArg pure (congrArg (RustM.ok ∘Prod.mk none) restored)
  | some frame=>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveSource.source
