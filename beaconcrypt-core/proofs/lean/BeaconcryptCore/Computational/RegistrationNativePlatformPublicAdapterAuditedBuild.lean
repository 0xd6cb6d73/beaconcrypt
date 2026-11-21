-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBuild
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
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec wire
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

noncomputable def step (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (handle :Nat) (payload :Option (Slice U8)) :TotalStep auditPrivate ((auditModel (.inr (.build handle payload))).run before) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential
    (.inr (.build handle (payload.map TranscriptAuthParts.absSlice)))
    (.inr (.build handle (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice))))
    RegistrationNativeRawAdapter.responseOption rfl before.1 before.2
    (RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.typed configuration created credential before.1 stored handle payload)

theorem query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (handle :Nat) (payload :Option (Slice U8)) :
    raw auditPhysical (step configuration created credential before stored handle payload)=
      RegistrationNativePlatformPublicAdapterConfiguredBuild.sourceOperation configuration (auditPhysical before stored) handle payload :=by
  unfold step
  exact (RegistrationNativePlatformPublicAdapterAuditLift.selected_physical configuration created credential
    (.inr (.build handle (payload.map TranscriptAuthParts.absSlice)))
    (.inr (.build handle (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice))))
    RegistrationNativeRawAdapter.responseOption rfl before.1 before.2 _).trans
    (RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.query configuration created credential before.1 stored handle payload)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBuild.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBuild.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBuild.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBuild.query
