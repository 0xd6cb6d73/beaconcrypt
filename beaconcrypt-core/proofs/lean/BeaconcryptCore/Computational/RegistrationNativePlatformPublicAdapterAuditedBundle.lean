-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle
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

variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

theorem target (current :Native×P) (index :Nat) :
    (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
      ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks configuration.agreement.representation created source writer index).run current.1).run current.2)=
      (RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.bundle index))).run current :=by
  unfold RegistrationNativePlatformPublicAdapterAuditModel.typed RegistrationNativePlatformPublicAdapterRawModel.typed RegistrationNativePlatformPackedState.pack
  rfl

noncomputable def step (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) :
    TotalStep auditPrivate ((auditModel (.inr (.bundle index))).run before) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential
    (.inr (.bundle index)) (.inr (.bundle index)) RegistrationNativeRawAdapter.resultOption rfl before.1 before.2
    (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (target configuration created credential before.1 index)
      (RegistrationNativePlatformPublicAdapterConfiguredBundle.typed configuration created credential before.1 stored index))

theorem query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) :
    raw auditPhysical (step configuration created credential before stored index)=
      RegistrationNativePlatformPublicAdapterBundlePhysical.run coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure writer children
        configuration.generator (auditPhysical before stored) index :=by
  unfold step
  refine (RegistrationNativePlatformPublicAdapterAuditLift.selected_physical configuration created credential
    (.inr (.bundle index)) (.inr (.bundle index)) RegistrationNativeRawAdapter.resultOption rfl before.1 before.2 _).trans ?_
  change raw (physical configuration created credential)
    (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
      (RegistrationNativePlatformPublicAdapterConfiguredBundle.typed configuration created credential before.1 stored index))=_
  exact (RegistrationNativePlatformPublicAdapterNormalizedRaw.raw
    (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup configuration.view configuration.views created credential) _).trans
    ((congrArg (fun tree=>RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>tree)
      (RegistrationNativePlatformPublicAdapterBundleDispatchSource.query coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure configuration.reservePackets children
        previousLocal (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential index configuration.generator
        (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration) (before.1.1,none) before.1.2 stored)).trans
      (RegistrationNativePlatformPublicAdapterBundleNormalization.run_source coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure writer children configuration.generator
        (RegistrationNativePlatformPublicAdapterStore.erase stored.base.objects) index))

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle.target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle.query
