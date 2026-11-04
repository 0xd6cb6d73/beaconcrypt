-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open AdapterPublicWrapperRustT (RustT)
variable {n : Nat} {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (inactive : AdapterPublicOrdinaryBeacon.Inactive self) (bytes : Slice U8) :
    RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup codec reserve view failure erased self bytes=
      pure (.ok (none,self)) := by
  let :=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
  unfold RegistrationNativePlatformExtractedSdkOrdinary.beaconSend
  rw [AdapterPublicOrdinaryBeacon.send_inactive self inactive bytes]
  rfl

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (inactive : AdapterPublicOrdinaryBeacon.Inactive self) (bytes : Slice U8) :
    RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup codec reserve view failure erased self bytes=
      pure (.ok (none,self)) := by
  let :=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
  unfold RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive
  rw [AdapterPublicOrdinaryBeacon.receive_inactive self inactive bytes]
  rfl

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem pure_run {Self Reply : Type} (outcome : RustM (Reply ×Self))
    (before : RegistrationNativeExperiment.State n KemSK mlSource) (previous : Platform) (rawBefore : Nat) (invoked : Bool) :
    RegistrationNativePlatformExtractedSdkOrdinary.run (pure outcome) before previous rawBefore invoked=
      pure (⟨outcome,(before,previous),[],rawBefore,invoked⟩ :
        RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet Self Reply (RegistrationNativeExperiment.State n KemSK mlSource) Platform) := by
  unfold RegistrationNativePlatformExtractedSdkOrdinary.run
  simp only [StateT.run_pure,map_pure]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.receive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.pure_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconIdleSource.pure_run
