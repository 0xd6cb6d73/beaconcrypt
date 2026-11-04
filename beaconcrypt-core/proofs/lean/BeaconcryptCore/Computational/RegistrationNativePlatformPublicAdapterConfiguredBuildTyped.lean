-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuild
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped
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
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
noncomputable def nativeStep (current :Native×P) (before :Private configuration created credential current)
    (handle :Nat) (payload :Option (Slice U8)) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep coins setup codec configuration.keyView configuration.converted configuration.sealFailure
    configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets originalLocal originalContainers children
    configuration.view configuration.views created credential current before handle (payload.map TranscriptAuthParts.absSlice) configuration.pins
    (configuration.peerAllocate before.base.objects.server.known_ids) (configuration.peerReserve before.base.objects.server.known_ids)
    (configuration.peerFootprint before.base.objects.server.known_ids) (configuration.peerMember before.base.objects.server.known_ids)
    (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.base.objects.server with known_ids:=known} inserting publicKey)

noncomputable def typed (current :Native×P) (before :Private configuration created credential current)
    (handle :Nat) (payload :Option (Slice U8)) :
    TotalStep (Private configuration created credential)
      ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
        (.inr (.build handle (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice))))).run current) :=by
  let call:=RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.bytes
    (nativeStep configuration created credential current before handle payload)
  refine RegistrationNativePlatformPublicAdapterBuildRaw.modelCast ?_ call
  have changed:=congrArg (fun reservePeer=>RegistrationNativePlatformPublicAdapterRawModel.typed (n:=n) setup checks configuration.agreement.representation created credential
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration reservePeer configuration.reserveFrame configuration.erased helper writer
    (.inr (.build handle (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)))))
    (configuration.peerAdmission before.base.objects.server.known_ids)
  have actual:=RegistrationNativePlatformPublicAdapterBuildModel.typed (n:=n) setup checks configuration.agreement.representation created credential
    configuration.keyView configuration.sealFailure configuration.allocateJoin configuration.reserveRegistration
    (configuration.peerAllocate before.base.objects.server.known_ids) configuration.reserveFrame configuration.erased configuration.reservePackets handle (payload.map TranscriptAuthParts.absSlice)
  have lifted:=congrArg (fun action=>RegistrationNativePlatformPackedState.pack action current) (changed.symm.trans actual)
  refine Eq.trans ?_ lifted.symm
  simp only [RegistrationNativePlatformPackedState.pack,StateT.run_map,Functor.map_map]
  rfl

theorem query (current :Native×P) (before :Private configuration created credential current)
    (handle :Nat) (payload :Option (Slice U8)) :
    raw (physical configuration created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.responseOption
        (typed configuration created credential current before handle payload))=
      RegistrationNativePlatformPublicAdapterConfiguredBuild.sourceOperation configuration
        (physical configuration created credential current before) handle payload :=by
  change raw (physical configuration created credential)
    (RegistrationNativePlatformPublicAdapterConfiguredBuild.step configuration created credential current before handle payload)=_
  exact RegistrationNativePlatformPublicAdapterConfiguredBuild.query configuration created credential current before handle payload

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.nativeStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.nativeStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildTyped.query
