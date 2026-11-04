-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported
import BeaconcryptCore.Computational.RegistrationNativeCreateHandle
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
/-! Source constructor receipts commit only literal owner registration after capture. The backend erasure retains the exact captured source state, environment and platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateStep
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformExtractedSdkCreateReceipt (SourceM Packet Result)
variable {n : Nat} {I KemSK R Error Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (SourceM n KemSK source Platform))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (SourceM n KemSK source Platform))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (SourceM n KemSK source Platform))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)


open RegistrationNativePlatformExtractedSdkAdaptive (pack)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)

noncomputable def total
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (identityBytes mldsaBytes : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityBytes=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mldsaBytes=.ok (.Ok mlPin))
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (Private : RegistrationNativeExperiment.State n KemSK source ×Platform →Type)
    (put : ∀packet,packet∈support
      ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous) →
      Private ((RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet.1).2,packet.2)) :
    TotalStep Private (pack <$>
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source (view.edPublic serverId) mlPin keyId))).run before).run previous)) where
  step := {
    Packet := Result n KemSK R source ×Platform
    sample := (RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous
    sourceType := AdapterBeaconConstructorBody.Outcome R
    sourceReply := (fun packet =>.ok packet.1.1.1.1.outcome)
    sourceState := (fun packet =>(packet.1.1.1.1.sourceAfter,packet.2))
    sourceCall := pack <$>
      (((RegistrationNativePlatformExtractedSdkCreate.close
        (beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m := RustT (SourceM n KemSK source Platform))
          generator keyId identityBytes mldsaBytes rng).run).run before).run previous)
    source_exact := by
      have equation := congrArg (fun work =>pack <$>work.run previous)
        (RegistrationNativePlatformExtractedSdkCreateCommon.typed_source coins setup checks representation created generator view kem leaves
          keyId serverId mlPin rng identityBytes mldsaBytes parsed parsedMl before)
      simp only [StateT.run_map,Functor.map_map] at equation
      exact equation
    native := (fun packet =>pack (RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet.1,packet.2))
    native_exact := by
      have equation := congrArg (fun work =>pack <$>work.run previous)
        (RegistrationNativePlatformExtractedSdkCreateCommon.native coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before)
      simp only [StateT.run_map,Functor.map_map] at equation
      exact equation
    store := put }
  observe := RegistrationNativePlatformExtractedSdkCreateCommit.observe before.beacons.length
  normal := by intro packet _supported; exact ⟨packet.1.1.1.1.outcome,rfl⟩
  reply := by
    intro packet supported returned actual
    change RustM.ok packet.1.1.1.1.outcome=RustM.ok returned at actual
    cases RustM.ok.inj actual
    exact RegistrationNativePlatformExtractedSdkCreateSupported.reply coins setup checks representation created generator view kem leaves
      keyId serverId mlPin rng before previous packet.2 packet.1 supported

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateStep.total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateStep.total
