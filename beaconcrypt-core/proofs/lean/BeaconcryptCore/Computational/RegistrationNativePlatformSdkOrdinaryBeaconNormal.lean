-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconReceiveStrongSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconNormal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (ledgerCodec)
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw strongPhysical)
open RegistrationNativePlatformPublicAdapterStore (erase)

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8)
    (result : RustM (Option RawCtxSourceSend.Encrypted×RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform)×
      (RegistrationNativePlatformSdkReification.Backend n KemSK×Platform))
    (supported : result∈support (RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup reserve keyView failure erased (erase before.base.objects) logical bytes)) :
    ∃returned,result.1=.ok returned ∧result.2=returned.2.backend :=by
  have actual := Eq.mp (congrArg (fun work=>result∈support work)
    (RegistrationNativePlatformSdkOrdinaryBeaconErasure.send setup reserve length keyView converted failure erased route view views created credential current before logical bytes).symm) supported
  simp only [RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw,support_map] at actual
  obtain ⟨packet,_possible,same⟩:=actual
  cases same
  exact ⟨_,rfl,rfl⟩

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8)
    (result : RustM (Option RawCtxWholeOwner.Decrypted×RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform)×
      (RegistrationNativePlatformSdkReification.Backend n KemSK×Platform))
    (supported : result∈support (RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup reserve keyView failure erased (erase before.base.objects) logical bytes)) :
    ∃returned,result.1=.ok returned ∧result.2=returned.2.backend :=by
  have actual := Eq.mp (congrArg (fun work=>result∈support work)
    (RegistrationNativePlatformSdkOrdinaryBeaconErasure.receive setup reserve length keyView failure erased route view views created credential current before logical bytes).symm) supported
  simp only [RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw,support_map] at actual
  obtain ⟨packet,_possible,same⟩:=actual
  cases same
  exact ⟨_,rfl,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconNormal.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconNormal.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconNormal.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconNormal.receive
