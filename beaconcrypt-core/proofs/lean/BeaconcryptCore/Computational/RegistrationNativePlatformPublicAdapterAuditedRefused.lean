-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations]
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
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

noncomputable def sourceOperation (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    ProbComp (RustM (Option RawCtxSourceSend.Encrypted×RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)×
      (RegistrationNativePlatformSdkReification.Backend n KemSK×P)):=pure (.ok (none,before),before.backend)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem server_target (current :Native×P) (selected :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    pure (none,current)=((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.serverSend selected bytes))).run current) :=by
  have law:=RegistrationNativePlatformPublicAdapterSendRepresentability.raw_server (n:=n) setup checks configuration.agreement.representation created credential
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased helper writer selected bytes oversized
  have packed:=congrArg (fun action=>(RegistrationNativePlatformPackedState.pack action).run current) law
  have nativeTyped:(RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.serverSend selected bytes)))).run current=
      (RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.serverSend selected bytes))).run current :=by
    unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native RegistrationNativePlatformPublicAdapterAuditModel.typed
    simp only [RegistrationNativePlatformPublicAdapterRawModel.raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  refine (nativeTyped.symm.trans ?_).symm
  exact packed.trans rfl

noncomputable def server (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (selected :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    TotalStep (RegistrationNativePlatformPublicAdapterAuditLowModel.Private configuration created credential)
      ((RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential (.inr (.serverSend selected bytes oversized))).run before) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (congrArg (fun action=>action.run before) (RegistrationNativePlatformPublicAdapterAuditLowModel.server_query configuration created credential selected bytes oversized).symm)
    (RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential
      (.inr (.serverSend selected bytes)) (.inr (.serverSend selected bytes)) id rfl before.1 before.2
      (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (server_target configuration created credential before.1 selected bytes oversized)
        (RegistrationNativePlatformPublicAdapterEffectPhysical.pureStep setup configuration.view configuration.views created credential before.1 stored none)))

omit [PublicWrapperPlatform.CryptoOperations] in
theorem server_query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (selected :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    raw (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration created credential)
      (server configuration created credential before stored selected bytes oversized)=
      sourceOperation (auditPhysical before stored) :=by
  unfold server
  unfold RegistrationNativePlatformPublicAdapterAuditLowModel.physical
  erw [raw_cast,RegistrationNativePlatformPublicAdapterAuditLift.selected_physical]
  change raw (physical configuration created credential)
    (RegistrationNativePlatformPublicAdapterEffectPhysical.pureStep setup configuration.view configuration.views created credential before.1 stored none)=_
  have same:=RegistrationNativePlatformPublicAdapterEffectPhysical.pure_source setup configuration.view configuration.views created credential before.1 stored (none:Option RawCtxSourceSend.Encrypted)
  have basis:=stored.base.backend
  change (RegistrationNativePlatformPublicAdapterStore.erase stored.base.objects).backend=RegistrationNativePlatformSdkReification.persistent before.1 at basis
  unfold sourceOperation
  rw [←basis] at same
  exact same

omit [PublicWrapperPlatform.CryptoOperations] in
theorem beacon_target (current :Native×P) (selected :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    pure (none,current)=((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.beaconSend selected bytes))).run current) :=by
  have law:=RegistrationNativePlatformPublicAdapterSendRepresentability.raw_beacon (n:=n) setup checks configuration.agreement.representation created credential
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased helper writer selected bytes oversized
  have packed:=congrArg (fun action=>(RegistrationNativePlatformPackedState.pack action).run current) law
  have nativeTyped:(RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.beaconSend selected bytes)))).run current=
      (RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.beaconSend selected bytes))).run current :=by
    unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native RegistrationNativePlatformPublicAdapterAuditModel.typed
    simp only [RegistrationNativePlatformPublicAdapterRawModel.raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  refine (nativeTyped.symm.trans ?_).symm
  exact packed.trans rfl

noncomputable def beacon (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (selected :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    TotalStep (RegistrationNativePlatformPublicAdapterAuditLowModel.Private configuration created credential)
      ((RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential (.inr (.beaconSend selected bytes oversized))).run before) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (congrArg (fun action=>action.run before) (RegistrationNativePlatformPublicAdapterAuditLowModel.beacon_query configuration created credential selected bytes oversized).symm)
    (RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential
      (.inr (.beaconSend selected bytes)) (.inr (.beaconSend selected bytes)) id rfl before.1 before.2
      (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (beacon_target configuration created credential before.1 selected bytes oversized)
        (RegistrationNativePlatformPublicAdapterEffectPhysical.pureStep setup configuration.view configuration.views created credential before.1 stored none)))

omit [PublicWrapperPlatform.CryptoOperations] in
theorem beacon_query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (selected :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    raw (RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration created credential)
      (beacon configuration created credential before stored selected bytes oversized)=
      sourceOperation (auditPhysical before stored) :=by
  unfold beacon
  unfold RegistrationNativePlatformPublicAdapterAuditLowModel.physical
  erw [raw_cast,RegistrationNativePlatformPublicAdapterAuditLift.selected_physical]
  change raw (physical configuration created credential)
    (RegistrationNativePlatformPublicAdapterEffectPhysical.pureStep setup configuration.view configuration.views created credential before.1 stored none)=_
  have same:=RegistrationNativePlatformPublicAdapterEffectPhysical.pure_source setup configuration.view configuration.views created credential before.1 stored (none:Option RawCtxSourceSend.Encrypted)
  have basis:=stored.base.backend
  change (RegistrationNativePlatformPublicAdapterStore.erase stored.base.objects).backend=RegistrationNativePlatformSdkReification.persistent before.1 at basis
  unfold sourceOperation
  rw [←basis] at same
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.server_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.server_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.server_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.beacon_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.beacon_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.beacon_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused.beacon_query
