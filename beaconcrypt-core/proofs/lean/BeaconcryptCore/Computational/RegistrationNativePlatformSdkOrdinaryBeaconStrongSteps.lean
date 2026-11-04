-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier OtkPublic update_public)
open RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun (Sample)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

noncomputable def active_send (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native ×Platform) (before : StrongCarrier (R:=R) setup view containers created credential current)
    (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (selected : current.1.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.base.objects.beacons logical=some self)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel))
    (completed : RegistrationBeaconSeed.PublicCompleted) (phase : owner.phase=.established completed)
    (present : current.1.server.world.world.1.owners[owner.worldOwner]?=some
      (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) kernel))
    (bytes : Slice U8) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (StrongCarrier (R:=R) setup view containers created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform) =>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
  let call:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps.active_send setup wire reserve length keyView converted failure erased route
    view containers created credential current before.base logical owner selected self sourceSelected control binding kernel stored completed phase present bytes
  apply RegistrationNativePlatformSdkStrongStep.of_base setup view containers created credential call
  intro packet
  have progress:=RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_normal setup (ledgerCodec wire) reserve length keyView converted failure erased
    self control binding kernel bytes (current.1.server.world.world.1.primitive,[]) packet.val.1.2 current.2 packet.val.2 packet.val.1.1 packet.property
  obtain ⟨⟨final,pubReply⟩,normal⟩:=progress
  rcases packet with ⟨⟨⟨outcome,after⟩,afterP⟩,supported⟩
  dsimp only at normal
  subst outcome
  change OtkPublic _ view (Function.update before.base.objects.beacons logical
    (some (RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.returned self control binding final)))
  apply update_public view _ before.base.objects.beacons before.otkPublic logical
    (RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.returned self control binding final)
  intro fresh prekey oneTime kem impossible
  change beaconcrypt_public_wrapper.beacon.BeaconState.Established control binding (AdapterPublicOrdinaryEnvelope.manager final)=.FreshWithCoins fresh prekey oneTime kem at impossible
  cases impossible

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps.active_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps.active_send
