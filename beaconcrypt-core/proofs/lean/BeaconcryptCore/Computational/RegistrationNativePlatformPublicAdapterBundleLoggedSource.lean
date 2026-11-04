-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageActual
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource
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
local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable {Log :Type}

local notation "M"=>StateT (Backend n KemSK) (StateT P ProbComp)
local notation "physicalLocal"=>RegistrationNativePlatformPublicAdapterLeaves.localOperations (S:=Backend n KemSK) originalLocal
local notation "observedCrypto"=>RegistrationNativePlatformPublicAdapterUniformObserver.operations
  (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks configuration.agreement.representation created) originalCrypto
local notation "localSource"=>RegistrationNativePlatformPublicAdapterBundleDictionaries.locals coins setup checks configuration.agreement.representation created configuration.view physicalLocal
local notation "cryptoSource"=>RegistrationNativePlatformPublicAdapterBundleDictionaries.crypto setup configuration.view observedCrypto configuration.edFailure
local notation "childrenSource"=>RegistrationNativePlatformPublicAdapterBundleDictionaries.children coins setup checks configuration.agreement.representation created writer children

noncomputable def leaves (self :beaconcrypt_public_wrapper.beacon.Beacon) :=
  RegistrationNativePlatformPublicAdapterBundleDictionaries.leaves coins setup checks configuration.agreement.representation created configuration.view
    physicalLocal observedCrypto configuration.edFailure writer children self

noncomputable def handler (self :beaconcrypt_public_wrapper.beacon.Beacon) :QueryImpl (RegistrationNativePlatformWriter.Spec E) M :=
  let :LocalOperations (RustT M):=localSource
  let :CryptoOperations (RustT M):=cryptoSource
  let :ChildOperations (RustT M):=childrenSource
  fun query=>match query with
  | .inl query=>AdapterPublicInitPublication.outgoing
      (AdapterPublicBundleMaterial.PublicationLeaves.hash (self:=self) (leaves (n:=n) configuration created self))
      (AdapterPublicBundleMaterial.PublicationLeaves.sign (self:=self) (leaves (n:=n) configuration created self))
      (AdapterPublicInitPublication.edMethod (configuration.view.edPublic self.identity_key.public_key)
        (AdapterPublicBundleMaterial.PublicationLeaves.edSign (self:=self) (leaves (n:=n) configuration created self))) query
  | .inr query=>StateT.lift (writer query)

noncomputable def withKeys (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (control :pqxdh.BeaconFresh) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R)
    (before :Backend n KemSK) (previous :P) (prior :List Log) :
    ProbComp ((RustM (RegistrationNativePlatformPublicAdapterBundlePhysical.Word R)×(Backend n KemSK×P))×List Log) :=
  (fun result=>((AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1.1,(result.1.2.1,result.2)),result.1.2.2)) <$>
    (RegistrationNativePlatformPublicAdapterBundleStageActual.publication (handler configuration created self)
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBundleStageLog.observation query reply).map note)
      control ⟨configuration.view.edPublic self.identity_key.public_key,configuration.view.kxPublic prekey.public_key,
        RegistrationNativeBeaconFrontend.pqArray (configuration.view.kemPublic kem.public_key)⟩
      ⟨configuration.view.kxPublic oneTime.public_key⟩ self.authentication.server_pin
      (configuration.view.mldsa self.authentication.identity).publicKey (before,prior)).run previous

omit [FrameDispatchFallback.Operations] in
private theorem withKeys_unlogged (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (control :pqxdh.BeaconFresh) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R) :
    let :LocalOperations (RustT M):=localSource
    let :CryptoOperations (RustT M):=cryptoSource
    let :ChildOperations (RustT M):=childrenSource
    (AdapterPublicBundleBody.withKeys (m:=M) self control prekey oneTime kem rng).run=
      AdapterPublicBundlePublication.install self prekey oneTime kem rng <$>
        simulateQ (handler configuration created self)
          (RegistrationNativePlatformWriter.begin E control
            ⟨configuration.view.edPublic self.identity_key.public_key,configuration.view.kxPublic prekey.public_key,
              RegistrationNativeBeaconFrontend.pqArray (configuration.view.kemPublic kem.public_key)⟩
            ⟨configuration.view.kxPublic oneTime.public_key⟩ self.authentication.server_pin
            (configuration.view.mldsa self.authentication.identity).publicKey) :=by
  let :LocalOperations (RustT M):=localSource
  let :CryptoOperations (RustT M):=cryptoSource
  let :ChildOperations (RustT M):=childrenSource
  dsimp only
  rw [AdapterPublicBundlePublication.withKeys self control prekey oneTime kem rng
    (configuration.view.kxPublic prekey.public_key) (configuration.view.kxPublic oneTime.public_key)
    (configuration.view.edPublic self.identity_key.public_key)
    (RegistrationNativeBeaconFrontend.pqArray (configuration.view.kemPublic kem.public_key))
    (configuration.view.mldsa self.authentication.identity).publicKey
    (AdapterPublicBundleMaterial.PublicationLeaves.edSign (self:=self) (leaves (n:=n) configuration created self))
    (AdapterPublicBundleMaterial.PublicationLeaves.hash (self:=self) (leaves (n:=n) configuration created self))
    (AdapterPublicBundleMaterial.PublicationLeaves.sign (self:=self) (leaves (n:=n) configuration created self))
    rfl rfl rfl rfl rfl (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)]
  rw [RegistrationNativePlatformWriter.begin_interpret]
  have encoded : (fun signed :registration.SignedInitView=>(ChildOperations.encodeInit (m:=RustT M) (AdapterPublicBundleBody.packet signed)).run)=
      (fun signed=>simulateQ (fun query=>StateT.lift (writer query))
        (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket signed)).run) :=by
    funext signed
    exact (simulateQ_liftTarget (n:=M) writer _).symm
  rw [encoded]
  rfl

omit [FrameDispatchFallback.Operations] in
theorem withKeys_erase (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (control :pqxdh.BeaconFresh) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R)
    (before :Backend n KemSK) (previous :P) (prior :List Log) :
    let :LocalOperations (RustT M):=localSource
    let :CryptoOperations (RustT M):=cryptoSource
    let :ChildOperations (RustT M):=childrenSource
    Prod.fst <$>withKeys configuration created note self control prekey oneTime kem rng before previous prior=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (((AdapterPublicBundleBody.withKeys (m:=M) self control prekey oneTime kem rng).run).run before).run previous :=by
  let :LocalOperations (RustT M):=localSource
  let :CryptoOperations (RustT M):=cryptoSource
  let :ChildOperations (RustT M):=childrenSource
  dsimp only
  unfold withKeys
  rw [RegistrationNativePlatformPublicAdapterBundleStageActual.source,withKeys_unlogged configuration created self control prekey oneTime kem rng]
  have erased:=congrArg (fun work=>work.run previous)
    (RegistrationNativePlatformPublicAdapterSourceTrace.erase (handler configuration created self)
      (fun query reply=>(RegistrationNativePlatformPublicAdapterBundleStageLog.observation query reply).map note)
      (RegistrationNativePlatformWriter.begin E control
        ⟨configuration.view.edPublic self.identity_key.public_key,configuration.view.kxPublic prekey.public_key,
          RegistrationNativeBeaconFrontend.pqArray (configuration.view.kemPublic kem.public_key)⟩
        ⟨configuration.view.kxPublic oneTime.public_key⟩ self.authentication.server_pin
        (configuration.view.mldsa self.authentication.identity).publicKey) (before,prior))
  have same:=congrArg (fun tree=>(fun result=>(AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1.1,(result.1.2,result.2))) <$>tree) erased
  simpa only [StateT.run_map,Functor.map_map,Prod.map,id_eq] using same

noncomputable def call (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (rng :R) (before :Backend n KemSK) (previous :P) (prior :List Log) :
    ProbComp ((RustM (RegistrationNativePlatformPublicAdapterBundlePhysical.Word R)×(Backend n KemSK×P))×List Log) :=
  match self.state with
  | .Fresh control prekey kem=>do
    let sampled←((RegistrationNativePlatformPublicAdapterBundleSigning.sample coins setup checks configuration.agreement.representation created PqxdhJointGapDh.sampleScalar).run before).run previous
    let realized:=(RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize sampled.1.1 rng
    withKeys configuration created note self control prekey realized.1 kem realized.2 sampled.1.2 sampled.2 prior
  | .FreshWithCoins control prekey oneTime kem=>withKeys configuration created note self control prekey oneTime kem rng before previous prior
  | _=>pure ((.ok (.None,self,rng),(before,previous)),prior)

omit [FrameDispatchFallback.Operations] in
theorem call_source (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (rng :R) (before :Backend n KemSK) (previous :P) (prior :List Log) :
    call configuration created note self rng before previous prior=
      RegistrationNativePlatformPublicAdapterBundleObservedSource.call configuration created note self rng before previous prior :=by
  rw [RegistrationNativePlatformPublicAdapterBundleObservedSource.call_code]
  unfold call
  cases stored:self.state with
  | Fresh control prekey kem=>
    dsimp only
    apply bind_congr
    rintro ⟨⟨scalar,after⟩,next⟩
    exact (RegistrationNativePlatformPublicAdapterBundleObservedSource.withKeys_source configuration created note self control prekey
      ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).1 kem
      ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).2 after next prior).symm
  | FreshWithCoins control prekey oneTime kem=>
    dsimp only
    exact (RegistrationNativePlatformPublicAdapterBundleObservedSource.withKeys_source configuration created note self control prekey oneTime kem rng before previous prior).symm
  | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control=>
    rfl


def finish (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) (index :Nat)
    (result :(RustM (RegistrationNativePlatformPublicAdapterBundlePhysical.Word R)×(Backend n KemSK×P))×RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P) :
    RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P (Option Pqxdh.Bytes) :=
  let final:=RegistrationNativePlatformPublicAdapterBundlePhysical.finish (RegistrationNativePlatformPublicAdapterSourceEvents.store before) index result.1
  (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects <$>final.1,
    (final.2.1,(final.2.2,result.2)))

noncomputable def operation (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) (index :Nat) :
    ProbComp (RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P (Option Pqxdh.Bytes)) :=
  match before.beacons index with
  | none=>pure (.ok (none,RegistrationNativePlatformPublicAdapterSourceRuntime.objects before),before.backend)
  | some self=>finish before index <$>
    RegistrationNativePlatformPublicAdapterBundleObservedSource.call configuration created RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage self before.rng before.backend.1 before.backend.2.1 before.backend.2.2



omit [FrameDispatchFallback.Operations] in
theorem call_erase (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon) (rng :R)
    (before :Backend n KemSK) (previous :P) (prior :List Log) :
    Prod.fst <$>call configuration created note self rng before previous prior=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        ((RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks configuration.agreement.representation created configuration.view
          physicalLocal observedCrypto configuration.edFailure writer children configuration.generator self rng).run before).run previous :=by
  let :LocalOperations (RustT M):=localSource
  let :CryptoOperations (RustT M):=cryptoSource
  let :ChildOperations (RustT M):=childrenSource
  unfold RegistrationNativePlatformPublicAdapterBundleSource.call
  dsimp only
  cases stored:self.state with
  | Fresh control prekey kem=>
    rw [AdapterPublicBundleBody.fresh configuration.generator self rng control prekey kem stored]
    let generation:=RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_backend (n:=n) (P:=P)
      coins setup checks configuration.agreement.representation created configuration.view configuration.edFailure configuration.generator
      (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
    unfold AdapterPublicBundleBody.generated
    rw [generation.operation]
    unfold call
    rw [stored]
    simp only [map_bind,RustT.run_bind,RustT.run_lift,StateT.run_bind,bind_map_left]
    apply bind_congr
    rintro ⟨⟨scalar,current⟩,nextP⟩
    simpa only [generation,RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_backend] using
      (withKeys_erase configuration created note self control prekey
        ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).1 kem
        ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).2 current nextP prior)
  | FreshWithCoins control prekey oneTime kem=>
    rw [AdapterPublicBundleBody.with_coins configuration.generator self rng control prekey oneTime kem stored]
    unfold call
    rw [stored]
    exact withKeys_erase configuration created note self control prekey oneTime kem rng before previous prior
  | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control=>
    have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
    rw [RegistrationNativePlatformExtractedSdkIdle.bundle_source configuration.generator self rng idle]
    unfold call
    rw [stored]
    simp only [map_pure,StateT.run_pure]


omit [FrameDispatchFallback.Operations] in
theorem erase (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) (index :Nat) :
    RegistrationNativePlatformPublicAdapterSourceEvents.outcome <$>operation configuration created before index=
      RegistrationNativePlatformPublicAdapterSourceRuntime.run
        (RegistrationNativePlatformPublicAdapterSourceRuntime.raw (fun current=>RegistrationNativePlatformPublicAdapterBundlePhysical.run
          coins setup checks configuration.agreement.representation created configuration.view physicalLocal configuration.edFailure writer children configuration.generator current index))
        (RegistrationNativePlatformPublicAdapterSourceEvents.store before) :=by
  rw [RegistrationNativePlatformPublicAdapterSourceRuntime.run_raw]
  unfold operation RegistrationNativePlatformPublicAdapterBundlePhysical.run
  cases selected:before.beacons index with
  | none=>simp only [RegistrationNativePlatformPublicAdapterSourceEvents.store,selected,map_pure];rfl
  | some self=>
    simp only [RegistrationNativePlatformPublicAdapterSourceEvents.store,selected,Functor.map_map]
    rw [←call_source]
    have called:=call_erase configuration created RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage self before.rng
      before.backend.1 before.backend.2.1 before.backend.2.2
    have same:=congrArg (fun tree=>(fun result=>
      let final:=RegistrationNativePlatformPublicAdapterBundlePhysical.finish (RegistrationNativePlatformPublicAdapterSourceEvents.store before) index result
      (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects <$>final.1,final.2)) <$>tree) called
    simpa only [finish,RegistrationNativePlatformPublicAdapterSourceEvents.outcome,RegistrationNativePlatformPublicAdapterSourceEvents.backend,
      RegistrationNativePlatformPublicAdapterBundlePhysical.call,RegistrationNativePlatformPublicAdapterSourceEvents.store,Functor.map_map] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.withKeys_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.withKeys_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.call_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.call_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource.call_source
