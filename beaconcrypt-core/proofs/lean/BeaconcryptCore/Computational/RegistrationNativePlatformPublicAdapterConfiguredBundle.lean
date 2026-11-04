-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle
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
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical children other recording packedLocal packedCrypto)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "CutM"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)
local notation "previousLocal"=>RegistrationNativePlatformPublicAdapterLeaves.localOperations
  (S:=RegistrationNativePlatformCutJournal.State Native) originalLocal
noncomputable local instance idleLocal :LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedLocal
noncomputable local instance idleCrypto :CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedCrypto
noncomputable local instance idleChildren :ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=children

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)

noncomputable def typed (current :Native×P) (before :Private configuration created credential current) (index :Nat) :=
  RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks configuration.agreement.representation created
    configuration.reservePackets index configuration.edFailure (other (m:=CutM)) (recording (m:=CutM)) configuration.views credential
    configuration.view configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
    (current.1,none) current.2 before

noncomputable def step (current :Native×P) (before :Private configuration created credential current) (index :Nat) :
    TotalStep (Private configuration created credential) ((model configuration created credential (.inr (.bundle index))).run current) :=
  RegistrationNativePlatformPublicAdapterBundleRawSteps.step previousLocal setup checks configuration.agreement.representation created
    configuration.reservePackets index configuration.edFailure (other (m:=CutM)) (recording (m:=CutM)) configuration.views credential
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer
    configuration.reserveFrame configuration.erased helper configuration.view configuration.generator
    (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration) (current.1,none) current.2 before

theorem query (current :Native×P) (before :Private configuration created credential current) (index :Nat) :
    raw (physical configuration created credential) (step configuration created credential current before index)=
      RegistrationNativePlatformPublicAdapterBundlePhysical.run coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure writer children
        configuration.generator (physical configuration created credential current before) index :=
  RegistrationNativePlatformPublicAdapterBundleRawSteps.query previousLocal setup checks configuration.agreement.representation created
    configuration.reservePackets index configuration.edFailure (other (m:=CutM)) (recording (m:=CutM)) configuration.views credential
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer
    configuration.reserveFrame configuration.erased helper configuration.view configuration.generator
    (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration) (current.1,none) current.2 before
    (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) children

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle.query
