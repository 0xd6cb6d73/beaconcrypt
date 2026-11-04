-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageActual
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedBody
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource
private theorem map_apply {m :Type→Type} [Monad m] [LawfulMonad m] {T A B :Type}
    (f :A→B) (action :StateT T m A) (before :T) :
    (f <$>action) before=Prod.map f id <$>action before:=StateT.run_map f action before
private theorem bind_apply {m :Type→Type} [Monad m] {T A B :Type}
    (action :StateT T m A) (next :A→StateT T m B) (before :T) :
    (action >>=next) before=(do let result←action before;next result.1 result.2):=rfl
private theorem pure_apply {m :Type→Type} [Monad m] {T A :Type} (value :A) (before :T) :
    (pure value :StateT T m A) before=pure (value,before):=rfl
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

local notation "Base"=>StateT P ProbComp
local notation "Ctx"=>RegistrationNativePlatformCutJournal.State (Backend n KemSK×List Log)
local notation "ObservedM"=>StateT Ctx Base

noncomputable def liftLog {A :Type} (action :StateT (Backend n KemSK) Base A) :StateT (Backend n KemSK×List Log) Base A :=
  fun before=>(fun result=>(result.1,(result.2,before.2))) <$>action.run before.1

noncomputable def liftBackend {A :Type} (action :StateT (Backend n KemSK) Base A) :ObservedM A :=
  fun before=>(fun result=>(result.1,((result.2,before.1.2),before.2))) <$>action.run before.1.1

noncomputable def uniform :QueryImpl unifSpec ObservedM:=fun query=>liftBackend
  (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks configuration.agreement.representation created query)

noncomputable def observedEdSign (message :Slice U8) (key :beaconcrypt_crypto.crypto_sign.SecretKey) :
    ObservedM (core.result.Result (alloc.vec.Vec U8) ed.Error):=
  liftBackend (RegistrationNativePlatformPublicAdapterBundleDictionaries.edSign (n:=n) (P:=P) setup configuration.view configuration.edFailure message key)

noncomputable def fallback (self :beaconcrypt_public_wrapper.beacon.Beacon) (request :registration.MldsaSigningRequest) :
    StateT (Backend n KemSK×List Log) Base RegistrationSigningShared.SignReply:=
  AdapterPublicInitPublication.borrowed <$>liftLog
    (RegistrationNativePlatformPublicAdapterBundleDictionaries.sign coins setup checks configuration.agreement.representation created configuration.view self.authentication.identity request)

noncomputable def observe (note :Stage→Log) (query :(RegistrationNativePlatformWriter.Spec E).Domain)
    (reply :(RegistrationNativePlatformWriter.Spec E).Range query) :List Log:=
  (RegistrationNativePlatformPublicAdapterBundleStageLog.observation query reply).map note

local notation "observedLocal"=>RegistrationNativePlatformPublicAdapterLeaves.localOperations (S:=Ctx) originalLocal
local notation "observedPreviousCrypto"=>RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform configuration created) originalCrypto
local notation "observedChildren"=>RegistrationNativePlatformPublicAdapterDispatcherCore.children (m:=ObservedM)

omit [FrameDispatchFallback.Operations] in
theorem uniform_program {A :Type} (work :ProbComp A) :
    simulateQ (uniform (n:=n) (Log:=Log) configuration created) work=
      liftBackend (Log:=Log) (RegistrationNativePlatformPublicAdapterBundleSigning.sample coins setup checks configuration.agreement.representation created work) :=by
  funext before
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks configuration.agreement.representation created)
    (uniform (n:=n) (Log:=Log) configuration created)
    (fun backend=>( (backend,before.1.2),before.2)) (fun _ _=>rfl) work before.1.1
  rw [RegistrationNativePlatformPublicAdapterBundleGeneration.backend_program] at same
  exact same.symm

omit [FrameDispatchFallback.Operations] in
theorem ed_leaf (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon) (request :registration.Ed25519SigningRequest) :
    AdapterPublicInitPublication.edMethod (configuration.view.edPublic self.identity_key.public_key)
      (fun message=>observedEdSign (n:=n) (Log:=Log) configuration message self.identity_key.secret_key) request=
      RegistrationNativePlatformCutJournal.liftNative
        (RegistrationNativePlatformPublicAdapterSourceTrace.recorded (handler configuration created self) (observe note) (.inl (.inr request))) :=by
  funext before
  unfold RegistrationNativePlatformPublicAdapterSourceTrace.recorded RegistrationNativePlatformCutJournal.liftNative
  dsimp only [StateT.run,observe,RegistrationNativePlatformPublicAdapterBundleStageLog.observation,List.map_nil]
  unfold handler AdapterPublicInitPublication.outgoing
  dsimp only [leaves,RegistrationNativePlatformPublicAdapterBundleDictionaries.leaves]
  unfold AdapterPublicInitPublication.edMethod
  by_cases owns:(configuration.view.edPublic self.identity_key.public_key).val=request.public_key.val
  · simp only [owns,decide_true,ite_true]
    simp only [observedEdSign,map_apply,liftBackend,Functor.map_map,List.map_nil,List.append_nil]
    rfl
  · simp only [owns,decide_false,Bool.false_eq_true,ite_false,pure_apply,map_pure,List.map_nil,List.append_nil]

noncomputable def withKeys (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (control :pqxdh.BeaconFresh) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R)
    (before :Backend n KemSK) (previous :P) (prior :List Log) :
    ProbComp ((RustM (RegistrationNativePlatformPublicAdapterBundlePhysical.Word R)×(Backend n KemSK×P))×List Log) :=
  (fun result=>((result.1.1,(result.1.2.1.1,result.2)),result.1.2.1.2)) <$>
    ((RegistrationNativePlatformPublicAdapterBundleObservedBody.withKeys configuration.view (handler configuration created self) (observe note)
      (fallback configuration created self) observedLocal observedPreviousCrypto observedChildren (observedEdSign configuration)
      self control prekey oneTime kem rng).run ((before,prior),none)).run previous

noncomputable def call (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (rng :R) (before :Backend n KemSK) (previous :P) (prior :List Log) :
    ProbComp ((RustM (RegistrationNativePlatformPublicAdapterBundlePhysical.Word R)×(Backend n KemSK×P))×List Log) :=
  (fun result=>((result.1.1,(result.1.2.1.1,result.2)),result.1.2.1.2)) <$>
    ((RegistrationNativePlatformPublicAdapterBundleObservedBody.call configuration.view (handler configuration created self) (observe note)
      (fallback configuration created self) observedLocal observedPreviousCrypto observedChildren (observedEdSign configuration)
      configuration.generator self rng).run ((before,prior),none)).run previous

omit [FrameDispatchFallback.Operations] in
theorem withKeys_source (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (control :pqxdh.BeaconFresh) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R)
    (before :Backend n KemSK) (previous :P) (prior :List Log) :
    withKeys configuration created note self control prekey oneTime kem rng before previous prior=
      (fun result=>((AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1.1,(result.1.2.1,result.2)),result.1.2.2)) <$>
        (RegistrationNativePlatformPublicAdapterBundleStageActual.publication (handler configuration created self) (observe note)
          control ⟨configuration.view.edPublic self.identity_key.public_key,configuration.view.kxPublic prekey.public_key,
            RegistrationNativeBeaconFrontend.pqArray (configuration.view.kemPublic kem.public_key)⟩
          ⟨configuration.view.kxPublic oneTime.public_key⟩ self.authentication.server_pin
          (configuration.view.mldsa self.authentication.identity).publicKey (before,prior)).run previous :=by
  have actual:=RegistrationNativePlatformPublicAdapterBundleObservedBody.source configuration.view (handler configuration created self) (observe note)
    (fallback configuration created self) observedLocal observedPreviousCrypto observedChildren (observedEdSign configuration)
    self control prekey oneTime kem rng (ed_leaf configuration created note self) (before,prior)
  have observed:=congrArg (fun computation=>(fun result=>((result.1.1,(result.1.2.1,result.2)),result.1.2.2)) <$>computation.run previous) actual
  simp only [StateT.run_map,Functor.map_map] at observed
  exact observed

omit [FrameDispatchFallback.Operations] in
theorem generated (rng :R) :
    ((RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (uniform (n:=n) (Log:=Log) configuration created) originalCrypto).kxGenerate configuration.generator rng).run=
      (fun scalar=>RustM.ok (core.result.Result.Ok ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).1,
        ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).2)) <$>
        liftBackend (n:=n) (Log:=Log) (RegistrationNativePlatformPublicAdapterBundleSigning.sample coins setup checks configuration.agreement.representation created PqxdhJointGapDh.sampleScalar) :=by
  let :CryptoOperations (RustT ObservedM):=observedPreviousCrypto
  let mapped:=RegistrationNativePlatformPublicAdapterUniformObserver.generation
    (uniform (n:=n) (Log:=Log) configuration created) configuration.generator configuration.view
    (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar
    (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
  have operation:=congrArg RustT.run (mapped.operation rng)
  rw [RustT.run_lift] at operation
  simp only [Functor.map_map] at operation
  change ((observedPreviousCrypto).kxGenerate configuration.generator rng).run=
    (fun scalar=>RustM.ok (core.result.Result.Ok ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).1,
      ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).2)) <$>
      simulateQ (uniform (n:=n) (Log:=Log) configuration created) PqxdhJointGapDh.sampleScalar at operation
  rw [uniform_program] at operation
  exact operation

omit [FrameDispatchFallback.Operations] in
theorem call_code (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (rng :R) (before :Backend n KemSK) (previous :P) (prior :List Log) :
    call configuration created note self rng before previous prior=
      (match self.state with
      | .Fresh control prekey kem=>do
        let sampled←((RegistrationNativePlatformPublicAdapterBundleSigning.sample coins setup checks configuration.agreement.representation created PqxdhJointGapDh.sampleScalar).run before).run previous
        let realized:=(RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize sampled.1.1 rng
        withKeys configuration created note self control prekey realized.1 kem realized.2 sampled.1.2 sampled.2 prior
      | .FreshWithCoins control prekey oneTime kem=>withKeys configuration created note self control prekey oneTime kem rng before previous prior
      | _=>pure ((.ok (.None,self,rng),(before,previous)),prior)) :=by
  unfold call
  rw [RegistrationNativePlatformPublicAdapterBundleObservedBody.call_code]
  cases stored:self.state with
  | Fresh control prekey kem=>
    unfold RegistrationNativePlatformPublicAdapterBundleObservedBody.code
    rw [stored,generated]
    simp only [StateT.run_bind,map_bind,bind_map_left]
    unfold liftBackend
    dsimp only [StateT.run]
    rw [map_apply,bind_map_left]
    apply bind_congr
    rintro ⟨⟨scalar,after⟩,next⟩
    rfl
  | FreshWithCoins control prekey oneTime kem=>
    unfold RegistrationNativePlatformPublicAdapterBundleObservedBody.code
    rw [stored]
    rfl
  | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control=>
    unfold RegistrationNativePlatformPublicAdapterBundleObservedBody.code
    rw [stored]
    simp only [StateT.run_pure,map_pure]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.uniform_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.uniform_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.ed_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.ed_leaf
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.withKeys_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.withKeys_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.generated
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.call_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedSource.call_code
