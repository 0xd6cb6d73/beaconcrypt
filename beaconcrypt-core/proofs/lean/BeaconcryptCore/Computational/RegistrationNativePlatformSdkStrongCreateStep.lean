-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateStep
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCreateStep
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Objects BeaconTable Carrier SourceSnapshot)
variable {n : Nat} {KemSK Platform R : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

variable {I Error : Type} {base : OracleSpec I}
variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (AdapterPublicWrapperRustT.RustT (RegistrationNativePlatformExtractedSdkCreateReceipt.SourceM n KemSK source Platform))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations
  (AdapterPublicWrapperRustT.RustT (RegistrationNativePlatformExtractedSdkCreateReceipt.SourceM n KemSK source Platform))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations
  (AdapterPublicWrapperRustT.RustT (RegistrationNativePlatformExtractedSdkCreateReceipt.SourceM n KemSK source Platform))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (generator : rand_core.TryCryptoRng R Error)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : AdapterBeaconConstructorNative.Leaves (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State)
  coins setup checks representation created generator view kem)
variable (containers : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)


noncomputable def putPacket (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (before : Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containers created credential (before,previous))
    (packet : RegistrationNativePlatformExtractedSdkCreateReceipt.Result n KemSK R source×Platform)
    (supported : packet∈support ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created
      generator view kem leaves keyId serverId mlPin objects.base.objects.rng before).run previous)) :
    RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containers created credential
      ((RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet.1).2,packet.2) := by
  refine ⟨RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket coins setup checks representation created generator view kem leaves containers credential
    keyId serverId mlPin before previous objects.base packet supported, ?_⟩
  rw [RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket_objects]
  obtain ⟨captured,owners,environment,current,_called,same⟩:=
    RegistrationNativePlatformExtractedSdkCreateCommit.decompose coins setup checks representation created generator view kem leaves
      keyId serverId mlPin objects.base.objects.rng before previous packet.2 packet.1 supported
  rw [same]
  cases selected:captured.1 with
  | none=>simpa only [RegistrationNativePlatformExtractedSdkCreateCommit.result,selected,
      AdapterBeaconConstructorNative.sourceResult,AdapterBeaconConstructorJoint.sourceResult,
      RegistrationNativePlatformExtractedSdkCarrierCreate.update] using objects.otkPublic
  | some generated=>
    simp only [RegistrationNativePlatformExtractedSdkCreateCommit.result,selected,
      AdapterBeaconConstructorNative.sourceResult,AdapterBeaconConstructorJoint.sourceResult,
      RegistrationNativePlatformExtractedSdkCarrierCreate.update]
    apply RegistrationNativePlatformSdkStrongCarrier.update_public view _ _ objects.otkPublic
    intro control prekey oneTime kem stored
    simp only [AdapterBeaconConstructorJoint.object] at stored
    cases stored

noncomputable def total
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize)
    (identityBytes mldsaBytes : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityBytes=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mldsaBytes=.ok (.Ok mlPin))
    (before : Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containers created credential (before,previous)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containers created credential)
      (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source (view.edPublic serverId) mlPin keyId))).run before).run previous)) :=
  RegistrationNativePlatformExtractedSdkCreateStep.total coins setup checks representation created generator view kem leaves
    keyId serverId mlPin objects.base.objects.rng identityBytes mldsaBytes parsed parsedMl before previous
    (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containers created credential)
    (putPacket coins setup checks representation created generator view kem leaves containers credential
      keyId serverId mlPin before previous objects)

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCreateStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCreateStep.putPacket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCreateStep.putPacket

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCreateStep.total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCreateStep.total
