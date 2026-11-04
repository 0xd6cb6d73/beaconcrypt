-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSuccessStage
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformSdkReification (Backend)
variable {n :Nat} {I KemSK P E R Error Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
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
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=mlSource) setup checks)
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)

local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
open RegistrationNativePlatformExtractedSdkPublic (returned returned_exact store)
open RegistrationNativePlatformSdkReification (backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private physical)

open RegistrationNativePlatformPublicAdapterLoggedRuntime (Augmentation unchanged)
open RegistrationNativePlatformPublicAdapterFinishLoggedJoint (output physicalLog)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential mlSource)

open RegistrationNativePlatformPublicAdapterFinishLoggedDispatch (augmentation transport)


def Witness (current:Native×P) (index:Nat) (input:Slice U8) (pending:registration.BeaconPending) (note:Stage→Log) (past:List Log)
    {target:ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call:TotalStep (Private configuration created credential) target) (result:call.step.Packet×List Log) :Prop:=
  ∃owner scalar,∃reached:(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×List Log,
    current.1.beacons[index]?=some owner ∧owner.phase=.initSent pending scalar ∧
    reached∈support (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks
      configuration.agreement.representation created pending (AdapterPublicFinishLifetime.packet input) owner scalar current.1 current.2 past) ∧
    HEq result reached ∧result.2=reached.2 ∧
    call.step.native result.1=
      ((RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons reached.1.1).1,
        ((RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons reached.1.1).2,reached.1.2))

omit [FrameDispatchFallback.Operations] [PublicWrapperPlatform.CryptoOperations] in
private theorem transport_witness {target:ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    {left right:TotalStep (Private configuration created credential) target}
    (same:left=right) (augmented:Augmentation left (List Log))
    (current:Native×P) (index:Nat) (input:Slice U8) (pending:registration.BeaconPending) (note:Stage→Log) (past:List Log)
    (law:∀result,result∈support augmented.sample→Witness configuration created credential current index input pending note past left result)
    (result:right.step.Packet×List Log)
    (supported:result∈support (transport configuration created credential same augmented).sample) :
    Witness configuration created credential current index input pending note past right result:=by
  cases same
  exact law result supported

omit [FrameDispatchFallback.Operations] in
theorem configured (current:Native×P) (objects:Private configuration created credential current)
    (index:Nat) (input:Slice U8) (self:beaconcrypt_public_wrapper.beacon.Beacon)
    (pending:registration.BeaconPending) (prekey oneTime:beaconcrypt_crypto.crypto_kx.KeyPair) (kem:beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (sourceSelected:objects.base.objects.beacons index=some self) (stored:self.state=.InitSent pending prekey oneTime kem)
    (note:Stage→Log) (past:List Log)
    (result:(RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input).step.Packet×List Log)
    (supported:result∈support (augmentation configuration created credential current objects index input note past).sample) :
    Witness configuration created credential current index input pending note past
      (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) result:=by
  cases selected:current.1.beacons[index]? with
  | none=>
    have missing:=objects.base.beacons index
    rw [selected] at missing
    rw [sourceSelected] at missing
    contradiction
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let actual:=Classical.choose prior
    have found:objects.base.objects.beacons index=some actual:=(Classical.choose_spec prior).1
    have related:AdapterPublicWrapperState.Beacon configuration.view setup.joint current.1.pool actual owner
      current.1.server.world.world.1.owners[owner.worldOwner]?:=(Classical.choose_spec prior).2
    have sameSelf:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
    have actualStored:actual.state=.InitSent pending prekey oneTime kem:=sameSelf.symm ▸stored
    have phase:∃scalar,owner.phase=.initSent pending scalar:=by
      have matched:=related.phase
      cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,actualStored,phaseEq] at matched
      cases matched.1
      exact ⟨_,rfl⟩
    let scalar:=Classical.choose phase
    have phase:owner.phase=.initSent pending scalar:=Classical.choose_spec phase
    have callEq:RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input=
        RegistrationNativePlatformSdkFinishCoupled.active coins setup checks configuration.agreement.representation created wire
          configuration.view configuration.views credential actual pending prekey oneTime kem actualStored input owner scalar current.1 index selected phase current.2 objects found:=by
      unfold RegistrationNativePlatformPublicAdapterConfiguredFinish.typed RegistrationNativePlatformSdkFinishCoupledDispatch.step
      exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
        ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
          ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem actualStored).trans
            ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ actualStored).trans (by rfl))))
    have augEq:augmentation configuration created credential current objects index input note past=
        transport configuration created credential callEq.symm
          (RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active configuration created credential actual pending prekey oneTime kem actualStored input owner scalar
            current.1 index selected phase current.2 objects found note past):=by
      unfold augmentation
      exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
        ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
          ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem actualStored).trans
            ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ actualStored).trans (by rfl))))
    rw [augEq] at supported
    apply transport_witness configuration created credential callEq.symm _ current index input pending note past _ result supported
    intro reached called
    exact ⟨owner,scalar,reached,selected,phase,called,HEq.rfl,rfl,rfl⟩

omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations] originalGenerators originalCrypto in
private theorem bytes_some (reply:RustM (Option registration.CompletedBeacon)) (application:Pqxdh.Bytes)
    (success:RegistrationNativeRawAdapter.resultOption (RegistrationNativeFinishTerminalTree.bytes reply)=some application) :
    ∃completed,reply=.ok (some completed) ∧TranscriptAuthParts.absSlice completed.application=application:=by
  cases reply with
  | fail error | div=>cases success
  | ok optional=>cases optional with
    | none=>cases success
    | some completed=>exact ⟨completed,rfl,Option.some.inj success⟩

omit [FrameDispatchFallback.Operations] in
theorem configured_success (current:Native×P) (objects:Private configuration created credential current)
    (index:Nat) (input:Slice U8) (self:beaconcrypt_public_wrapper.beacon.Beacon)
    (pending:registration.BeaconPending) (prekey oneTime:beaconcrypt_crypto.crypto_kx.KeyPair) (kem:beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (sourceSelected:objects.base.objects.beacons index=some self) (stored:self.state=.InitSent pending prekey oneTime kem)
    (note:Stage→Log) (past:List Log)
    (result:(RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input).step.Packet×List Log)
    (supported:result∈support (augmentation configuration created credential current objects index input note past).sample)
    (application:Pqxdh.Bytes)
    (success:RegistrationNativeRawAdapter.resultOption ((RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input).step.native result.1).1=some application) :
    ∃owner scalar,∃reached:(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×List Log,∃completed initial,
      current.1.beacons[index]?=some owner ∧owner.phase=.initSent pending scalar ∧
      reached∈support (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks
        configuration.agreement.representation created pending (AdapterPublicFinishLifetime.packet input) owner scalar current.1 current.2 past) ∧
      HEq result reached ∧result.2=reached.2 ∧reached.1.1.1.1=.ok (some completed) ∧
      TranscriptAuthParts.absSlice completed.application=application ∧
      reached.2=past++[note (.beaconFirstRecord initial (.ok (.Ok completed)))] ∧
      (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input).step.native result.1=
        ((RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons reached.1.1).1,
          ((RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons reached.1.1).2,reached.1.2)):=by
  obtain ⟨owner,scalar,reached,selected,phase,called,samePacket,sameLog,nativeEq⟩:=
    configured configuration created credential current objects index input self pending prekey oneTime kem sourceSelected stored note past result supported
  have seen:RegistrationNativeRawAdapter.resultOption (RegistrationNativeFinishTerminalTree.bytes reached.1.1.1.1)=some application:=by
    rw [nativeEq] at success
    exact success
  obtain ⟨completed,completedEq,appEq⟩:=bytes_some _ application seen
  obtain ⟨initial,emitted⟩:=RegistrationNativePlatformPublicAdapterFinishSuccessStage.sample coins setup checks configuration.agreement.representation created wire
    note pending input owner scalar current.1 current.2 past reached called completed completedEq
  exact ⟨owner,scalar,reached,completed,initial,selected,phase,called,samePacket,sameLog,completedEq,appEq,emitted,nativeEq⟩

open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P
local notation "AuditPrivate"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential

/-- The full audited dispatcher packet is the same supported active Finish packet; the native owner and scalar are derived from the actual stored source object. -/
theorem dispatcher (before:RegistrationNativePlatformExtractedSdkPublic.State AuditPrivate)
    (index:Nat) (input:Slice U8) (self:beaconcrypt_public_wrapper.beacon.Beacon)
    (pending:registration.BeaconPending) (prekey oneTime:beaconcrypt_crypto.crypto_kx.KeyPair) (kem:beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (sourceSelected:before.2.base.objects.beacons index=some self) (stored:self.state=.InitSent pending prekey oneTime kem)
    (past:Events)
    (result:(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.Packet×Events)
    (supported:result∈support (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential
      (.inl (.inr (.finish index input))) before past).sample) :
    Witness configuration created credential before.1.1 index input pending Event.stage past
      (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential before.1.1 before.2 index input) result:=by
  change result∈support (augmentation configuration created credential before.1.1 before.2 index input Event.stage past).sample at supported
  exact configured configuration created credential before.1.1 before.2 index input self pending prekey oneTime kem sourceSelected stored Event.stage past result supported

theorem dispatcher_success (before:RegistrationNativePlatformExtractedSdkPublic.State AuditPrivate)
    (index:Nat) (input:Slice U8) (self:beaconcrypt_public_wrapper.beacon.Beacon)
    (pending:registration.BeaconPending) (prekey oneTime:beaconcrypt_crypto.crypto_kx.KeyPair) (kem:beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (sourceSelected:before.2.base.objects.beacons index=some self) (stored:self.state=.InitSent pending prekey oneTime kem)
    (past:Events)
    (result:(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.Packet×Events)
    (supported:result∈support (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential
      (.inl (.inr (.finish index input))) before past).sample)
    (application:Pqxdh.Bytes)
    (success:((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.native result.1).1=some application) :
    ∃owner scalar,∃reached:(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×Events,∃completed initial,
      before.1.1.1.beacons[index]?=some owner ∧owner.phase=.initSent pending scalar ∧
      reached∈support (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire Event.stage coins checks
        configuration.agreement.representation created pending (AdapterPublicFinishLifetime.packet input) owner scalar before.1.1.1 before.1.1.2 past) ∧
      HEq result reached ∧result.2=reached.2 ∧reached.1.1.1.1=.ok (some completed) ∧
      TranscriptAuthParts.absSlice completed.application=application ∧
      reached.2=past++[Event.stage (.beaconFirstRecord initial (.ok (.Ok completed)))] ∧
      ((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.native result.1).2.1=
        ((RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending before.1.1.1.beacons reached.1.1).2,reached.1.2):=by
  change result∈support (augmentation configuration created credential before.1.1 before.2 index input Event.stage past).sample at supported
  change RegistrationNativeRawAdapter.resultOption
    ((RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential before.1.1 before.2 index input).step.native result.1).1=some application at success
  obtain ⟨owner,scalar,reached,completed,initial,selected,phase,called,samePacket,sameLog,completedEq,appEq,emitted,nativeEq⟩:=
    configured_success configuration created credential before.1.1 before.2 index input self pending prekey oneTime kem sourceSelected stored Event.stage past result supported application success
  refine ⟨owner,scalar,reached,completed,initial,selected,phase,called,samePacket,sameLog,completedEq,appEq,emitted,?_⟩
  exact congrArg Prod.snd nativeEq

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.configured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.configured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.configured_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.configured_success

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.dispatcher' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.dispatcher

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.dispatcher_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.dispatcher_success
