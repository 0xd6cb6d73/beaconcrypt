-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconDispatch
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


noncomputable def sendModel (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (current : Native×Platform) (logical : Nat) (bytes : Slice U8) : ProbComp (Option RawCtxSourceSend.Encrypted×(Native×Platform)) :=
  ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
          (.inr (logical,.inl (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2)

noncomputable def receiveModel (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (current : Native×Platform) (logical : Nat) (bytes : Slice U8) : ProbComp (CoreModels.core.option.Option RawCtxWholeOwner.Decrypted×(Native×Platform)) :=
  ((fun result : ((CoreModels.core.option.Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
          (.inr (logical,.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2)

noncomputable def send (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (StrongCarrier (R:=R) setup view views created credential)
      (sendModel setup reserve route current logical bytes) := by
  cases selected:current.1.beacons[logical]? with
  | none=>
      exact RegistrationNativePlatformSdkOrdinaryBeaconMissing.send setup RegistrationNativeConcreteCodec.wire reserve route view views created credential
        current before logical (TranscriptAuthParts.absSlice bytes) selected
  | some owner=>
      have found:=before.base.beacons logical
      rw [selected] at found
      let self:=Classical.choose found
      have sourceSelected:= (Classical.choose_spec found).1
      have related:= (Classical.choose_spec found).2
      cases stored:self.state
      case Established control binding manager=>
        have active:=RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related control binding manager stored
        let kernel:=Classical.choose active
        let completed:=Classical.choose (Classical.choose_spec active)
        have actual:=Classical.choose_spec (Classical.choose_spec active)
        have normalized : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel) := stored.trans (congrArg _ actual.1)
        exact RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps.active_send setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views created credential
          current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes
      all_goals
        have idle : AdapterPublicOrdinaryBeacon.Inactive self :=by simp only [AdapterPublicOrdinaryBeacon.Inactive,stored]
        have dormant:=RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial.inactive view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related idle
        let tag:=Classical.choose dormant
        exact RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential
          current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle

noncomputable def receive (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (StrongCarrier (R:=R) setup view views created credential)
      (receiveModel setup reserve route current logical bytes) := by
  cases selected:current.1.beacons[logical]? with
  | none=>
      exact RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive setup RegistrationNativeConcreteCodec.wire reserve route view views created credential
        current before logical (TranscriptAuthParts.absSlice bytes) selected
  | some owner=>
      have found:=before.base.beacons logical
      rw [selected] at found
      let self:=Classical.choose found
      have sourceSelected:= (Classical.choose_spec found).1
      have related:= (Classical.choose_spec found).2
      cases stored:self.state
      case Established control binding manager=>
        have active:=RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related control binding manager stored
        let kernel:=Classical.choose active
        let completed:=Classical.choose (Classical.choose_spec active)
        have actual:=Classical.choose_spec (Classical.choose_spec active)
        have normalized : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel) := stored.trans (congrArg _ actual.1)
        exact RegistrationNativePlatformSdkOrdinaryBeaconReceiveStrongSteps.active_receive setup reserve length keyView failure erased route view views created credential
          current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes
      all_goals
        have idle : AdapterPublicOrdinaryBeacon.Inactive self :=by simp only [AdapterPublicOrdinaryBeacon.Inactive,stored]
        have dormant:=RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial.inactive view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related idle
        let tag:=Classical.choose dormant
        exact RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential
          current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive
