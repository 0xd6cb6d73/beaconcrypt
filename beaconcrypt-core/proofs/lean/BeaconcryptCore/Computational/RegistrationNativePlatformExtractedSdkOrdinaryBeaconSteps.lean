-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
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
    (current : Native ×Platform) (before : Carrier (R:=R) view containers setup.joint created credential current)
    (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (selected : current.1.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons logical=some self)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel))
    (completed : RegistrationBeaconSeed.PublicCompleted) (phase : owner.phase=.established completed)
    (present : current.1.server.world.world.1.owners[owner.worldOwner]?=some
      (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) kernel))
    (bytes : Slice U8) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (Carrier (R:=R) view containers setup.joint created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform) =>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
  let call : RegistrationNativePlatformExtractedSdkAdaptive.Step (Carrier (R:=R) view containers setup.joint created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform) =>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
    refine {
      Packet:=Sample Platform
      sample:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.runner setup wire reserve keyView failure erased self control binding kernel bytes current.1 current.2
      sourceType:=Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.beacon.Beacon
      sourceReply:=fun reached=>(RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source current.1 owner.worldOwner self control binding reached).outcome
      sourceState:=fun reached=>(RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed owner.worldOwner self
        (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source current.1 owner.worldOwner self control binding reached)).2
      sourceCall:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed owner.worldOwner self <$>
        RegistrationNativePlatformExtractedSdkOrdinary.run
          (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (ledgerCodec wire) reserve keyView failure erased self bytes)
          current.1 current.2 (current.1.server.world.world.1.ownerRaw owner.worldOwner) false
      source_exact:=?_
      native:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.native current.1 owner.worldOwner self control binding kernel
      native_exact:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.native_exact setup wire reserve length keyView converted failure erased route
        current.1 current.2 logical owner selected self control binding kernel bytes present
      store:=?_ }
    · change (fun reached=>RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed owner.worldOwner self
        (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source current.1 owner.worldOwner self control binding reached)) <$>_= _
      exact RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed_source setup wire reserve keyView failure erased self control binding kernel stored bytes current.1 current.2 owner.worldOwner
    · intro reached _supported
      dsimp only [RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source,
        RegistrationNativePlatformExtractedSdkOrdinary.pack]
      cases normal:reached.1.1 with
      | fail error=>exact PUnit.unit
      | div=>exact PUnit.unit
      | ok value=>
          rcases value with ⟨final,pubReply⟩
          rw [AdapterPublicOrdinaryKernel.returned_exact]
          rw [RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.native_eq current.1 owner.worldOwner self control binding kernel final pubReply reached normal]
          exact RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.put view containers setup.joint created credential current before logical owner selected self sourceSelected
            control binding kernel final stored completed phase pubReply reached normal
  refine {step:=call,observe:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observe,normal:=?_,reply:=?_}
  · intro reached supported
    exact RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.normal setup wire reserve length keyView converted failure erased
      self control binding kernel bytes current.1 current.2 owner.worldOwner reached supported
  · intro reached _supported returned same
    exact RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.reply current.1 owner.worldOwner self control binding kernel reached returned same

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps.active_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSteps.active_send
