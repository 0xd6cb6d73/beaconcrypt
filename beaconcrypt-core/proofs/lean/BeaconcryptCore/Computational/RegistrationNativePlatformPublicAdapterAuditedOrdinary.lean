-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary
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
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "N"=>RegistrationNativeExperiment.State n KemSK source×P
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "objects"=>RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential
local notation "publicPhysical"=>RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential

theorem serverSend_target (current :N) (bytes :Slice U8) (key :U64) :
    (RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.serverSend key bytes))).run current=
      (typed (.inr (.serverSend key (TranscriptAuthParts.absSlice bytes)))).run current :=by
  change RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    ((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.serverSend key (TranscriptAuthParts.absSlice bytes)))).run current.1).run current.2=_
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native RegistrationNativePlatformPublicAdapterAuditModel.typed
  simp only [RegistrationNativePlatformPublicAdapterRawModel.raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    simulateQ_spec_query]
  rfl

noncomputable def serverSend (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (bytes :Slice U8) (key :U64) :
    TotalStep auditPrivate ((auditModel (.inr (.serverSend key bytes))).run before) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential (.inr (.serverSend key (TranscriptAuthParts.absSlice bytes))) (.inr (.serverSend key (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (serverSend_target configuration created credential before.1 bytes key) (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverSend configuration created credential before.1 stored bytes key))

theorem serverSend_query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (bytes :Slice U8) (key :U64) :
    raw auditPhysical (serverSend configuration created credential before stored bytes key)=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased configuration.view configuration.views (auditPhysical before stored) bytes key :=by
  unfold serverSend
  refine (RegistrationNativePlatformPublicAdapterAuditLift.selected_physical configuration created credential
    (.inr (.serverSend key (TranscriptAuthParts.absSlice bytes))) (.inr (.serverSend key (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 _).trans ?_
  change raw publicPhysical (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverSend configuration created credential before.1 stored bytes key)=_
  exact RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverSend_query configuration created credential before.1 stored bytes key

theorem serverReceive_target (current :N) (bytes :Slice U8) :
    (RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.serverRaw bytes))).run current=
      (typed (.inr (.serverRaw (TranscriptAuthParts.absSlice bytes)))).run current :=by
  change RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    ((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.serverRaw (TranscriptAuthParts.absSlice bytes)))).run current.1).run current.2=_
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native RegistrationNativePlatformPublicAdapterAuditModel.typed
  simp only [RegistrationNativePlatformPublicAdapterRawModel.raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    simulateQ_spec_query]
  rfl

noncomputable def serverReceive (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (bytes :Slice U8) :
    TotalStep auditPrivate ((auditModel (.inr (.serverRaw bytes))).run before) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential (.inr (.serverRaw (TranscriptAuthParts.absSlice bytes))) (.inr (.serverRaw (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (serverReceive_target configuration created credential before.1 bytes) (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverReceive configuration created credential before.1 stored bytes))

theorem serverReceive_query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (bytes :Slice U8) :
    raw auditPhysical (serverReceive configuration created credential before stored bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased configuration.view configuration.views (auditPhysical before stored) bytes :=by
  unfold serverReceive
  refine (RegistrationNativePlatformPublicAdapterAuditLift.selected_physical configuration created credential
    (.inr (.serverRaw (TranscriptAuthParts.absSlice bytes))) (.inr (.serverRaw (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 _).trans ?_
  change raw publicPhysical (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverReceive configuration created credential before.1 stored bytes)=_
  exact RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverReceive_query configuration created credential before.1 stored bytes

theorem beaconSend_target (current :N) (index :Nat) (bytes :Slice U8) :
    (RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.beaconSend index bytes))).run current=
      (typed (.inr (.beaconSend index (TranscriptAuthParts.absSlice bytes)))).run current :=by
  change RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    ((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.beaconSend index (TranscriptAuthParts.absSlice bytes)))).run current.1).run current.2=_
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native RegistrationNativePlatformPublicAdapterAuditModel.typed
  simp only [RegistrationNativePlatformPublicAdapterRawModel.raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    simulateQ_spec_query]
  rfl

noncomputable def beaconSend (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) (bytes :Slice U8) :
    TotalStep auditPrivate ((auditModel (.inr (.beaconSend index bytes))).run before) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential (.inr (.beaconSend index (TranscriptAuthParts.absSlice bytes))) (.inr (.beaconSend index (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (beaconSend_target configuration created credential before.1 index bytes) (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconSend configuration created credential before.1 stored index bytes))

theorem beaconSend_query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) (bytes :Slice U8) :
    raw auditPhysical (beaconSend configuration created credential before stored index bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased (auditPhysical before stored) index bytes :=by
  unfold beaconSend
  refine (RegistrationNativePlatformPublicAdapterAuditLift.selected_physical configuration created credential
    (.inr (.beaconSend index (TranscriptAuthParts.absSlice bytes))) (.inr (.beaconSend index (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 _).trans ?_
  change raw publicPhysical (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconSend configuration created credential before.1 stored index bytes)=_
  exact RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconSend_query configuration created credential before.1 stored index bytes

theorem beaconReceive_target (current :N) (index :Nat) (bytes :Slice U8) :
    (RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.beaconRaw index bytes))).run current=
      (typed (.inr (.beaconRaw index (TranscriptAuthParts.absSlice bytes)))).run current :=by
  change RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    ((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential (.inr (.beaconRaw index (TranscriptAuthParts.absSlice bytes)))).run current.1).run current.2=_
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native RegistrationNativePlatformPublicAdapterAuditModel.typed
  simp only [RegistrationNativePlatformPublicAdapterRawModel.raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    simulateQ_spec_query]
  rfl

noncomputable def beaconReceive (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) (bytes :Slice U8) :
    TotalStep auditPrivate ((auditModel (.inr (.beaconRaw index bytes))).run before) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential (.inr (.beaconRaw index (TranscriptAuthParts.absSlice bytes))) (.inr (.beaconRaw index (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (beaconReceive_target configuration created credential before.1 index bytes) (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconReceive configuration created credential before.1 stored index bytes))

theorem beaconReceive_query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) (index :Nat) (bytes :Slice U8) :
    raw auditPhysical (beaconReceive configuration created credential before stored index bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased (auditPhysical before stored) index bytes :=by
  unfold beaconReceive
  refine (RegistrationNativePlatformPublicAdapterAuditLift.selected_physical configuration created credential
    (.inr (.beaconRaw index (TranscriptAuthParts.absSlice bytes))) (.inr (.beaconRaw index (TranscriptAuthParts.absSlice bytes))) id rfl before.1 before.2 _).trans ?_
  change raw publicPhysical (RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconReceive configuration created credential before.1 stored index bytes)=_
  exact RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconReceive_query configuration created credential before.1 stored index bytes

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive_query
