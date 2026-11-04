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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary
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
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
open AdapterPublicWrapperStorage (PeerMap)
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets

theorem get (known :PeerMap) :
    let _ :AdapterPublicOrdinaryRequestMonad.Operations (RustT (RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P)):=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire)
      configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased
    ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) known target=
      pure (configuration.views.peer known target) :=by
  let _ :AdapterPublicOrdinaryRequestMonad.Operations (RustT (RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P)):=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire)
    configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased
  dsimp only
  intro target
  change AdapterRecordRequestMonad.liftRust (AdapterPublicOrdinaryPlatform.LookupOperations.get _ _ _ _ _ _ known target)=_
  rw [configuration.peerGet]
  rfl

theorem borrow (known :PeerMap) :
    let _ :AdapterPublicOrdinaryRequestMonad.Operations (RustT (RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P)):=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire)
      configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased
    ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P) known target=
      pure (configuration.views.peer known target,configuration.peerBack known target) :=by
  let _ :AdapterPublicOrdinaryRequestMonad.Operations (RustT (RegistrationNativePlatformExtractedSdkOrdinaryDriver.M P)):=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire)
    configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased
  dsimp only
  intro target
  change AdapterRecordRequestMonad.liftRust (AdapterPublicOrdinaryPlatform.LookupOperations.getMut _ _ _ _ _ _ known target)=_
  rw [configuration.peerBorrow]
  rfl

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)

noncomputable def serverSend (current :Native×P) (before :Private configuration created credential current) (bytes :Slice U8) (key :U64) :
    TotalStep (Private configuration created credential)
      ((model configuration created credential (.inr (.serverSend key bytes))).run current) :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverSend setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before bytes key (configuration.peerBack before.base.objects.server.known_ids) (configuration.peerLens before.base.objects.server.known_ids) (get configuration before.base.objects.server.known_ids) (borrow configuration before.base.objects.server.known_ids)

theorem serverSend_query (current :Native×P) (before :Private configuration created credential current) (bytes :Slice U8) (key :U64) :
    raw (physical configuration created credential) (serverSend configuration created credential current before bytes key)=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased configuration.view configuration.views (physical configuration created credential current before) bytes key :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverSend_physical setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before bytes key (configuration.peerBack before.base.objects.server.known_ids) (configuration.peerLens before.base.objects.server.known_ids) (get configuration before.base.objects.server.known_ids) (borrow configuration before.base.objects.server.known_ids)

noncomputable def serverReceive (current :Native×P) (before :Private configuration created credential current) (bytes :Slice U8) :
    TotalStep (Private configuration created credential)
      ((model configuration created credential (.inr (.serverRaw bytes))).run current) :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverReceive setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before bytes (configuration.peerBack before.base.objects.server.known_ids) (configuration.peerLens before.base.objects.server.known_ids) (get configuration before.base.objects.server.known_ids) (borrow configuration before.base.objects.server.known_ids)

theorem serverReceive_query (current :Native×P) (before :Private configuration created credential current) (bytes :Slice U8) :
    raw (physical configuration created credential) (serverReceive configuration created credential current before bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased configuration.view configuration.views (physical configuration created credential current before) bytes :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.serverReceive_physical setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before bytes (configuration.peerBack before.base.objects.server.known_ids) (configuration.peerLens before.base.objects.server.known_ids) (get configuration before.base.objects.server.known_ids) (borrow configuration before.base.objects.server.known_ids)

noncomputable def beaconSend (current :Native×P) (before :Private configuration created credential current) (index :Nat) (bytes :Slice U8) :
    TotalStep (Private configuration created credential)
      ((model configuration created credential (.inr (.beaconSend index bytes))).run current) :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconSend setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before index bytes

theorem beaconSend_query (current :Native×P) (before :Private configuration created credential current) (index :Nat) (bytes :Slice U8) :
    raw (physical configuration created credential) (beaconSend configuration created credential current before index bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased (physical configuration created credential current before) index bytes :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconSend_physical setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before index bytes

noncomputable def beaconReceive (current :Native×P) (before :Private configuration created credential current) (index :Nat) (bytes :Slice U8) :
    TotalStep (Private configuration created credential)
      ((model configuration created credential (.inr (.beaconRaw index bytes))).run current) :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconReceive setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before index bytes

theorem beaconReceive_query (current :Native×P) (before :Private configuration created credential current) (index :Nat) (bytes :Slice U8) :
    raw (physical configuration created credential) (beaconReceive configuration created credential current before index bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup configuration.reserveFrame configuration.keyView configuration.sealFailure configuration.erased (physical configuration created credential current before) index bytes :=
  RegistrationNativePlatformPublicAdapterOrdinaryRawSteps.beaconReceive_physical setup checks configuration.agreement.representation created credential configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer configuration.sealLength configuration.openLength configuration.converted configuration.view configuration.views current before index bytes

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.get

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.borrow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.borrow

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverSend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverSend_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverSend_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverReceive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverReceive_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.serverReceive_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconSend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconSend_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconSend_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconReceive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconReceive_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredOrdinary.beaconReceive_query
