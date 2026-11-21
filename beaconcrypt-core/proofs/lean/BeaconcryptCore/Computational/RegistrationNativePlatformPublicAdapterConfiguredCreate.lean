-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawCreateModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical children raw_cast)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)

noncomputable def precast (current :Native×P) (before :Private configuration created credential current)
    (identityKey mlKey :Slice U8) (keyId :U64) :=
  RegistrationNativePlatformPublicAdapterCreatePhysical.dispatch coins setup checks configuration.agreement.representation created configuration.view
    children configuration.generator configuration.kem configuration.edGeneration configuration.prekeyGeneration configuration.kemGeneration
    configuration.views credential configuration.pins keyId identityKey mlKey current before

noncomputable def step (current :Native×P) (before :Private configuration created credential current)
    (identityKey mlKey :Slice U8) (keyId :U64) :
    TotalStep (Private configuration created credential) ((model configuration created credential (.inr (.create identityKey mlKey keyId))).run current) :=by
  let call:=precast configuration created credential current before identityKey mlKey keyId
  refine RegistrationNativePlatformPublicAdapterBuildRaw.modelCast ?_ call
  exact (RegistrationNativePlatformPublicAdapterRawCreateModel.create setup checks configuration.agreement.representation created credential
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased helper writer keyId identityKey mlKey current).symm

theorem query (current :Native×P) (before :Private configuration created credential current)
    (identityKey mlKey :Slice U8) (keyId :U64) :
    raw (physical configuration created credential) (step configuration created credential current before identityKey mlKey keyId)=
      RegistrationNativePlatformPublicAdapterCreateNormalized.source coins setup checks configuration.agreement.representation created configuration.view children
        configuration.generator keyId identityKey mlKey (physical configuration created credential current before) :=by
  unfold step
  rw [raw_cast]
  exact RegistrationNativePlatformPublicAdapterCreateNormalized.query coins setup checks configuration.agreement.representation created configuration.view
    children children configuration.generator configuration.kem configuration.edGeneration configuration.prekeyGeneration configuration.kemGeneration
    configuration.views credential configuration.pins keyId identityKey mlKey current before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate.precast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate.precast

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate.query
