-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
variable (current :RegistrationNativeExperiment.State n KemSK source×P)
variable (before :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current)
variable (keyId :U64) (serverId :beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin :Std.Array U8 1952#usize)
variable (identityKey mlKey :Slice U8)
variable (parsed :beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey=.ok (.Ok serverId))
variable (parsedMl :core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  1952#usize core.U8.Insts.CoreMarkerCopy mlKey=.ok (.Ok mlPin))

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
noncomputable def typed :=
  letI :AdapterBeaconConstructorRequestMonad.Operations (RustT
      (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks configuration.agreement.representation created configuration.view
  letI :CryptoOperations (RustT
      (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto configuration.view
      (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks configuration.agreement.representation created)
  letI :ChildOperations (RustT
      (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterCreateDictionaries.children RegistrationNativePlatformPublicAdapterDispatcherCore.children
      (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks configuration.agreement.representation created)
  let leaves:=RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceLeaves coins setup checks configuration.agreement.representation created configuration.view
    RegistrationNativePlatformPublicAdapterDispatcherCore.children configuration.generator configuration.kem configuration.mlGeneration configuration.edGeneration
    configuration.prekeyGeneration configuration.kemGeneration
  RegistrationNativePlatformSdkStrongCreateStep.total coins setup checks configuration.agreement.representation created configuration.generator configuration.view
    configuration.kem leaves configuration.views credential keyId serverId mlPin identityKey mlKey parsed parsedMl current.1 current.2 before

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem mapped :
    RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
      (typed configuration created credential current before keyId serverId mlPin identityKey mlKey parsed parsedMl)=
      RegistrationNativePlatformPublicAdapterCreatePhysical.active coins setup checks configuration.agreement.representation created configuration.view
        RegistrationNativePlatformPublicAdapterDispatcherCore.children configuration.generator configuration.kem configuration.mlGeneration configuration.edGeneration
        configuration.prekeyGeneration configuration.kemGeneration configuration.views credential keyId serverId mlPin identityKey mlKey parsed parsedMl current before :=rfl

omit [PublicWrapperPlatform.CryptoOperations] in
theorem target :
    (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks configuration.agreement.representation created
          (RegistrationNativeBeaconFrontend.create setup source (configuration.view.edPublic serverId) mlPin keyId))).run current.1).run current.2))=
      ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
        (.inr (.create (configuration.view.edPublic serverId) mlPin keyId))).run current) :=rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def step :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (target configuration created credential current keyId serverId mlPin)
    (typed configuration created credential current before keyId serverId mlPin identityKey mlKey parsed parsedMl)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.typed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.mapped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.target
