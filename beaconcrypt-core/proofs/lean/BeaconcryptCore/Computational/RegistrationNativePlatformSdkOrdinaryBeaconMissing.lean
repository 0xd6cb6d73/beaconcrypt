-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]

noncomputable def send (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Pqxdh.Bytes) (missing : current.1.beacons[logical]?=none) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl bytes))) mlSource).run current.1).run current.2) := by
  let call : RegistrationNativePlatformExtractedSdkAdaptive.Step (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl bytes))) mlSource).run current.1).run current.2) := {
    Packet:=Unit
    sample:=pure ()
    sourceType:=Option beaconcrypt_record_send.shared.Encrypted
    sourceReply:=fun _=>.ok none
    sourceState:=fun _=>before.base.objects.snapshot.committed
    sourceCall:=pure (.ok none,before.base.objects.snapshot.committed)
    source_exact:=by simp only [map_pure]
    native:=fun _=>(none,current)
    native_exact:=by
      rw [RegistrationNativePlatformOrdinaryBeaconIdleNative.missing_send setup wire reserve route current.1 logical bytes missing]
      simp only [map_pure]
      rfl
    store:=fun _ _=>before }
  refine {step:=call,observe:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply,normal:=fun _ _=>⟨none,rfl⟩,reply:=?_}
  intro packet _supported returned same
  cases same
  rfl

noncomputable def receive (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Pqxdh.Bytes) (missing : current.1.beacons[logical]?=none) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inr bytes))) mlSource).run current.1).run current.2) := by
  let call : RegistrationNativePlatformExtractedSdkAdaptive.Step (StrongCarrier (R:=R) setup view views created credential)
      ((fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inr bytes))) mlSource).run current.1).run current.2) := {
    Packet:=Unit
    sample:=pure ()
    sourceType:=Option beaconcrypt.shared.Decrypted
    sourceReply:=fun _=>.ok none
    sourceState:=fun _=>before.base.objects.snapshot.committed
    sourceCall:=pure (.ok none,before.base.objects.snapshot.committed)
    source_exact:=by simp only [map_pure]
    native:=fun _=>(none,current)
    native_exact:=by
      rw [RegistrationNativePlatformOrdinaryBeaconIdleNative.missing_receive setup wire reserve route current.1 logical bytes missing]
      simp only [map_pure]
      rfl
    store:=fun _ _=>before }
  refine {step:=call,observe:=RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply,normal:=fun _ _=>⟨none,rfl⟩,reply:=?_}
  intro packet _supported returned same
  cases same
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive
