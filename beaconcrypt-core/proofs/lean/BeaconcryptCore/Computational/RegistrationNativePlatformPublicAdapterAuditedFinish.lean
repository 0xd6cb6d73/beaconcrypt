-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
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
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical children packedLocal packedCrypto raw_cast)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
noncomputable local instance idleLocal :LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedLocal
noncomputable local instance idleCrypto :CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedCrypto
noncomputable local instance idleChildren :ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=children
local instance idleCodecs :Codecs (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=AdapterPublicConcreteCodecs.codecs
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

noncomputable def typed (current :Native×P) (before :Private configuration created credential current) (index :Nat) (input :Slice U8) :
    TotalStep (Private configuration created credential)
      ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
        (.inr (.finish index (RegistrationNativeWire.readResponse RegistrationNativeConcreteCodec.wire (TranscriptAuthParts.absSlice input))))).run current) :=by
  let call:=RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current before index input
  refine RegistrationNativePlatformPublicAdapterBuildRaw.modelCast ?_ call
  unfold RegistrationNativePlatformPublicAdapterAuditModel.typed RegistrationNativePlatformPublicAdapterRawModel.typed RegistrationNativePlatformPackedState.pack
  rw [RegistrationNativeConcreteReaders.response]
  rfl

noncomputable def step (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) (input :Slice U8) :
    TotalStep auditPrivate ((auditModel (.inr (.finish index input))).run before) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential
    (.inr (.finish index (TranscriptAuthParts.absSlice input)))
    (.inr (.finish index (RegistrationNativeWire.readResponse RegistrationNativeConcreteCodec.wire (TranscriptAuthParts.absSlice input))))
    RegistrationNativeRawAdapter.resultOption rfl before.1 before.2 (typed configuration created credential before.1 stored index input)

theorem query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) (input :Slice U8) :
    raw auditPhysical (step configuration created credential before stored index input)=
      RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall configuration created (auditPhysical before stored) index input :=by
  unfold step
  refine (RegistrationNativePlatformPublicAdapterAuditLift.selected_physical configuration created credential
    (.inr (.finish index (TranscriptAuthParts.absSlice input)))
    (.inr (.finish index (RegistrationNativeWire.readResponse RegistrationNativeConcreteCodec.wire (TranscriptAuthParts.absSlice input))))
    RegistrationNativeRawAdapter.resultOption rfl before.1 before.2 _).trans ?_
  change raw (physical configuration created credential)
    (RegistrationNativePlatformPublicAdapterConfiguredFinish.step configuration created credential before.1 stored index input)=_
  exact RegistrationNativePlatformPublicAdapterConfiguredFinish.query configuration created credential before.1 stored index input

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish.query
