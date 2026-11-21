-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource
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
/-! The source-stage observer augments the exact original Bundle packet through every phase. Its support-indexed source objects and terminal physical poststate remain paired with the actual chronological leaf log; future source continuations use only returned public replies and source objects. Missing and inactive objects retain their prior log. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged
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

open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable {Log :Type}

open RegistrationNativePlatformPublicAdapterBundleLoggedSource (withKeys call finish operation)

noncomputable def withCoinsAugmentation (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh) (scalar :PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.FreshWithCoins control prekey oneTime kem) (phase :owner.phase=.freshWithCoins scalar)
    (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (selected :before.1.beacons[index]?=some owner)
    (note :Stage→Log) (prior :List Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks configuration.agreement.representation created
        configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
        control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected) (List Log) where
  sample:=RegistrationNativePlatformPublicAdapterBundleStageLog.runner coins setup checks configuration.agreement.representation created writer index owner note scalar before.1 previous prior
  erase:=RegistrationNativePlatformPublicAdapterBundleStageLog.runner_erase coins setup checks configuration.agreement.representation created writer index owner note scalar before.1 previous prior

noncomputable def freshAugmentation (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh)
    (prekey :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.Fresh control prekey kem) (phase :owner.phase=.fresh)
    (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (selected :before.1.beacons[index]?=some owner)
    (note :Stage→Log) (prior :List Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks configuration.agreement.representation created
        configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
        control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
        stored phase before previous objects sourceSelected selected) (List Log) where
  sample:=RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner coins setup checks configuration.agreement.representation created writer index owner note before.1 previous prior
  erase:=RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner_erase coins setup checks configuration.agreement.representation created writer index owner note before.1 previous prior

omit [FrameDispatchFallback.Operations] in
private theorem withKeys_operands (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (owner :RegistrationNativeBeaconFrontend.Owner source) (pool :PqxdhLiveKemBirth.Pool KemSK)
    (world :Option PqxdhRecordLiftBeacon.Phase)
    (related :AdapterPublicWrapperState.Beacon configuration.view setup.joint pool self owner world)
    (control :pqxdh.BeaconFresh) (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R) (scalar :PqxdhJointGapDh.ScalarBytes)
    (controlView :control.expected_server_binding=owner.pin.binding)
    (prekeyView :configuration.view.kxPublic prekey.public_key=owner.prekeyPublic)
    (oneTimeView :configuration.view.kxPublic oneTime.public_key=PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
    (kemView :configuration.view.kemPublic kem.public_key=owner.kemPublic)
    (before :Backend n KemSK) (previous :P) (prior :List Log) :
    withKeys configuration created note self control prekey oneTime kem rng before previous prior=
      (fun result=>((AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1.1,(result.1.2.1,result.2)),result.1.2.2)) <$>
        ((RegistrationNativePlatformPublicAdapterBundleStageLog.physical coins setup checks configuration.agreement.representation created writer note
          owner.identitySeed ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin).run (before,prior)).run previous :=by
  have controlSame :control=⟨owner.pin.binding⟩ :=by cases control;exact congrArg pqxdh.BeaconFresh.mk controlView
  have handlerSame :RegistrationNativePlatformPublicAdapterBundleLoggedSource.handler (n:=n) configuration created self=
      RegistrationNativePlatformPublicAdapterBundlePublication.handler (n:=n) coins setup checks configuration.agreement.representation created writer owner.identitySeed :=by
    let previousCrypto :CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks configuration.agreement.representation created) originalCrypto
    let :LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))):=RegistrationNativePlatformPublicAdapterBundleDictionaries.locals
      coins setup checks configuration.agreement.representation created configuration.view (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal)
    let :CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))):=RegistrationNativePlatformPublicAdapterBundleDictionaries.crypto setup configuration.view previousCrypto configuration.edFailure
    let :ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))):=RegistrationNativePlatformPublicAdapterBundleDictionaries.children coins setup checks configuration.agreement.representation created writer children
    have sourceLaw:=RegistrationNativePlatformPublicAdapterBundleDictionaries.outgoing_source coins setup checks configuration.agreement.representation created configuration.view
      (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) previousCrypto configuration.edFailure writer children self owner related.identitySecret
    funext query
    cases query with
    | inl query=>
      unfold RegistrationNativePlatformPublicAdapterBundleLoggedSource.handler
      rw [related.identityPublic]
      exact congrArg (fun implementation=>implementation query) sourceLaw
    | inr query=>rfl
  unfold RegistrationNativePlatformPublicAdapterBundleLoggedSource.withKeys
  rw [RegistrationNativePlatformPublicAdapterBundleStageActual.source,handlerSame,
    related.identityPublic,prekeyView,oneTimeView,kemView,related.pin,controlSame]
  rfl


noncomputable abbrev step (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) :=
  RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks configuration.agreement.representation created configuration.reservePackets
    index configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential configuration.view configuration.generator
    (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration) before previous objects

noncomputable def augmentation (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) (note :Stage→Log) (prior :List Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation (step configuration created credential index before previous objects) (List Log) :=by
  cases selected:before.1.beacons[index]? with
  | none=>exact RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged _ prior
  | some owner=>
    have found:=objects.base.beacons index
    rw [selected] at found
    let self:=Classical.choose found
    have sourceSelected :objects.base.objects.beacons index=some self:=(Classical.choose_spec found).1
    have related :AdapterPublicWrapperState.Beacon configuration.view setup.joint before.1.pool self owner
        before.1.server.world.world.1.owners[owner.worldOwner]? :=(Classical.choose_spec found).2
    cases stored:self.state with
    | Fresh control prekey kem=>
      have phase :owner.phase=.fresh :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        rfl
      have callEq :step configuration created credential index before previous objects=
          RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
            stored phase before previous objects sourceSelected selected :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      exact callEq.symm ▸freshAugmentation configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected note prior
    | FreshWithCoins control prekey oneTime kem=>
      have hasScalar :∃scalar,owner.phase=.freshWithCoins scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose hasScalar
      have phase :owner.phase=.freshWithCoins scalar:=Classical.choose_spec hasScalar
      have callEq :step configuration created credential index before previous objects=
          RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      exact callEq.symm ▸withCoinsAugmentation configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected note prior
    | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control=>
      exact RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged _ prior


noncomputable def raw {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :TotalStep (Private configuration created credential) target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call (List Log)) :
    ProbComp ((RustM (Option Pqxdh.Bytes×Store n KemSK R P)×(Backend n KemSK×P))×List Log) :=
  (fun packet=>
    let selected:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
    let after:=RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
      (RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call selected).base.objects)
    ((.ok (RegistrationNativeRawAdapter.resultOption (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call selected)),after),after.backend),packet.val.2)) <$>
    PFunctor.FreeM.attachSupp augmented.sample

omit [FrameDispatchFallback.Operations] in
private theorem raw_active {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (current :Native×P) (objects :Private configuration created credential current) (index :Nat)
    (call :TotalStep (Private configuration created credential) target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call (List Log))
    (decode :call.step.sourceType→RegistrationNativePlatformPublicAdapterBundlePhysical.Word R)
    (observed :∀word,call.observe word=RegistrationNativePlatformExtractedSdkAdaptiveBundle.bytes (.ok (decode word)))
    (kept :∀packet,(RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects=
      RegistrationNativePlatformExtractedSdkCarrierBundle.update objects.base.objects index
        (decode (RegistrationNativePlatformExtractedSdkPublic.returned call packet)) (call.step.sourceState packet.val)) :
    raw configuration created credential call augmented=
      (fun result=>(RegistrationNativePlatformPublicAdapterBundlePhysical.finish
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects)) index
        (decode <$>call.step.sourceReply result.1,
          RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent (RegistrationNativePlatformSdkReification.persistent (call.step.sourceState result.1))),result.2)) <$>
        augmented.sample :=by
  let output :call.step.Packet×List Log→((RustM (Option Pqxdh.Bytes×Store n KemSK R P)×(Backend n KemSK×P))×List Log) :=fun result=>
    (RegistrationNativePlatformPublicAdapterBundlePhysical.finish
      (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects)) index
      (decode <$>call.step.sourceReply result.1,
        RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent (RegistrationNativePlatformSdkReification.persistent (call.step.sourceState result.1))),result.2)
  have attached:=congrArg (fun tree=>output <$>tree) (PFunctor.FreeM.map_attachSupp augmented.sample)
  simp only [Functor.map_map] at attached
  refine Eq.trans ?_ attached
  unfold raw
  apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp augmented.sample)
  funext packet
  let selected:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
  change ((RustM.ok (RegistrationNativeRawAdapter.resultOption (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call selected)),
    RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call selected).base.objects)),
    (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call selected).base.objects)).backend),packet.val.2)=_
  rw [kept selected,RegistrationNativePlatformPublicAdapterStore.bundle_update,RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_bundle]
  have normal :call.step.sourceReply packet.val.1=.ok (RegistrationNativePlatformExtractedSdkPublic.returned call selected):=
    RegistrationNativePlatformExtractedSdkPublic.returned_exact call selected
  dsimp only [output]
  rw [normal,observed]
  rfl

omit [FrameDispatchFallback.Operations] in
private theorem physical_frame (note :Stage→Log) (identity :PqxdhJointIdentity.IdentitySeed)
    (control :pqxdh.BeaconFresh)
    (inputs :pqxdh.BeaconStartInputs) (oneTime :pqxdh.BeaconCoins) (pin :session.ServerAuthenticationPin)
    (before :Backend n KemSK×List Log) :
    Prod.map id (Prod.map RegistrationNativePlatformPublicAdapterPhysicalBackend.erase id) <$>
      (RegistrationNativePlatformPublicAdapterBundleStageLog.physical coins setup checks configuration.agreement.representation created writer note
        identity control inputs oneTime pin).run before=
      (RegistrationNativePlatformPublicAdapterBundleStageLog.physical coins setup checks configuration.agreement.representation created writer note
        identity control inputs oneTime pin).run (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase before.1,before.2) :=by
  apply RegistrationNativePlatformPublicAdapterSourceTrace.source
  intro query current
  cases query with
  | inl query=>exact RegistrationNativePlatformPublicAdapterBundleFrame.outgoing coins setup checks configuration.agreement.representation created identity query current
  | inr query=>exact RegistrationNativePlatformPublicAdapterPhysicalFrame.lift_frame (writer query) current

omit [FrameDispatchFallback.Operations] in
private theorem runner_normalized (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (note :Stage→Log) (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (prior :List Log) :
    (fun result=>(((result.1.1.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend result.1.1.2)),result.1.2),result.2)) <$>
      RegistrationNativePlatformPublicAdapterBundleStageLog.runner coins setup checks configuration.agreement.representation created writer index owner note scalar before previous prior=
      (fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
        ((RegistrationNativePlatformPublicAdapterBundleStageLog.physical coins setup checks configuration.agreement.representation created writer note owner.identitySeed
          ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin).run
          (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend before),prior)).run previous :=by
  have first:=congrArg (fun tree=>(fun result=>(((result.1.1.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.erase result.1.1.2),result.1.2),result.2)) <$>tree)
    (RegistrationNativePlatformPublicAdapterBundleStageLog.runner_source coins setup checks configuration.agreement.representation created writer index owner note scalar before previous prior)
  have second:=congrArg (fun work=>work.run previous)
    (physical_frame configuration created note owner.identitySeed ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin (backend before,prior))
  have final:=congrArg (fun tree=>(fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>tree) second
  simp only [StateT.run_map,Functor.map_map,Prod.map,id_eq] at first final
  exact first.trans final


omit [FrameDispatchFallback.Operations] in
theorem with_coins_joint (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh) (scalar :PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.FreshWithCoins control prekey oneTime kem) (phase :owner.phase=.freshWithCoins scalar)
    (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (selected :before.1.beacons[index]?=some owner)
    (note :Stage→Log) (prior :List Log) :
    raw configuration created credential
      (RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks configuration.agreement.representation created
        configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
        control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected)
      (withCoinsAugmentation configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected note prior)=
      (fun result=>(RegistrationNativePlatformPublicAdapterBundlePhysical.finish
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects)) index result.1,result.2)) <$>
        withKeys configuration created note self control prekey oneTime kem objects.base.objects.rng
          (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend before.1)) previous prior :=by
  have material:=objects.base.beacons index
  rw [selected] at material
  obtain ⟨actual,found,related⟩:=material
  have same :actual=self:=Option.some.inj (found.symm.trans sourceSelected)
  subst actual
  have fields:=related.phase
  simp only [AdapterPublicWrapperState.Phase,stored,phase] at fields
  have publicView:=RegistrationNativePlatformSdkStrongCarrier.one_time_public setup configuration.view configuration.views created credential
    (before.1,previous) objects index self control prekey oneTime kem scalar sourceSelected stored fields.2.2.1
  have kept:=RegistrationNativePlatformPublicAdapterBundleStepSource.with_coins_objects previousLocal coins setup checks configuration.agreement.representation created
    configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential
    self configuration.view control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected
  rw [raw_active configuration created credential (before.1,previous) objects index _ _ id (fun _=>rfl) kept]
  rw [withKeys_operands configuration created note self owner before.1.pool before.1.server.world.world.1.owners[owner.worldOwner]?
    related control prekey oneTime kem objects.base.objects.rng scalar fields.1 fields.2.1.2 publicView fields.2.2.2.1.1]
  have joined:=congrArg (fun tree=>(fun result=>(RegistrationNativePlatformPublicAdapterBundlePhysical.finish
    (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects)) index
    (AdapterPublicBundlePublication.install self prekey oneTime kem objects.base.objects.rng result.1.1.1,(result.1.1.2,result.1.2)),result.2)) <$>tree)
    (runner_normalized configuration created index owner note scalar before.1 previous prior)
  simp only [Functor.map_map] at joined
  simp only [id_map,Functor.map_map]
  exact joined

omit [FrameDispatchFallback.Operations] in
private theorem fresh_normalized (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (note :Stage→Log) (before :Native) (previous :P) (prior :List Log) :
    (fun result=>(((result.1.1.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend result.1.1.2)),result.1.2),result.2)) <$>
      RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner coins setup checks configuration.agreement.representation created writer index owner note before previous prior=
      RegistrationNativePlatformPublicAdapterBundleStageLog.freshPhysical coins setup checks configuration.agreement.representation created writer note owner.identitySeed
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner) owner.pin
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend before)) previous prior :=by
  have first:=congrArg (fun work=>work.run previous)
    (RegistrationNativePlatformPublicAdapterBundleSigning.sample_source (source:=source) coins setup checks configuration.agreement.representation created PqxdhJointGapDh.sampleScalar before)
  have second:=congrArg (fun work=>work.run previous)
    (RegistrationNativePlatformPublicAdapterBundleFrame.sample coins setup checks configuration.agreement.representation created PqxdhJointGapDh.sampleScalar (backend before))
  have projected:=congrArg (fun tree=>(fun result=>((result.1.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.erase result.1.2),result.2)) <$>tree) first
  simp only [StateT.run_map,Functor.map_map,Prod.map,id_eq] at projected second
  have firstLaw:=projected.trans second
  unfold RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner RegistrationNativeBundleLifetime.sample
    RegistrationNativePlatformPublicAdapterBundleStageLog.freshPhysical
  rw [RegistrationNativeBundleInterpretation.legacy]
  simp only [map_bind]
  rw [←firstLaw,bind_map_left]
  apply bind_congr
  rintro ⟨⟨scalar,current⟩,nextP⟩
  have joined:=congrArg (fun tree=>(fun result=>((((scalar,result.1.1.1),result.1.1.2),result.1.2),result.2)) <$>tree)
    (runner_normalized configuration created index owner note scalar current nextP prior)
  simpa only [map_pure,bind_pure_comp,Functor.map_map] using joined

omit [FrameDispatchFallback.Operations] in
private theorem fresh_call (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (owner :RegistrationNativeBeaconFrontend.Owner source) (pool :PqxdhLiveKemBirth.Pool KemSK)
    (world :Option PqxdhRecordLiftBeacon.Phase)
    (related :AdapterPublicWrapperState.Beacon configuration.view setup.joint pool self owner world)
    (control :pqxdh.BeaconFresh) (prekey :beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R)
    (stored :self.state=.Fresh control prekey kem) (phase :owner.phase=.fresh)
    (before :Backend n KemSK) (previous :P) (prior :List Log) :
    call configuration created note self rng before previous prior=
      (fun result=>
        let realized:=(RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize result.1.1.1.1 rng
        ((AdapterPublicBundlePublication.install self prekey realized.1 kem realized.2 result.1.1.1.2,(result.1.1.2,result.1.2)),result.2)) <$>
      RegistrationNativePlatformPublicAdapterBundleStageLog.freshPhysical coins setup checks configuration.agreement.representation created writer note
        owner.identitySeed ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner) owner.pin before previous prior :=by
  have fields:=related.phase
  simp only [AdapterPublicWrapperState.Phase,stored,phase] at fields
  unfold call
  rw [stored]
  unfold RegistrationNativePlatformPublicAdapterBundleStageLog.freshPhysical
  simp only [map_bind]
  apply bind_congr
  rintro ⟨⟨scalar,current⟩,nextP⟩
  rw [withKeys_operands configuration created note self owner pool world related control prekey
    ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).1 kem
    ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize scalar rng).2 scalar fields.1 fields.2.1.2
    ((RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).publicView scalar rng) fields.2.2.1.1]
  simp only [map_pure,bind_pure_comp]

omit [FrameDispatchFallback.Operations] in
theorem fresh_joint (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh)
    (prekey :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.Fresh control prekey kem) (phase :owner.phase=.fresh)
    (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (selected :before.1.beacons[index]?=some owner)
    (note :Stage→Log) (prior :List Log) :
    raw configuration created credential
      (RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks configuration.agreement.representation created
        configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
        control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration) stored phase before previous objects sourceSelected selected)
      (freshAugmentation configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected note prior)=
      (fun result=>(RegistrationNativePlatformPublicAdapterBundlePhysical.finish
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects)) index result.1,result.2)) <$>
        call configuration created note self objects.base.objects.rng
          (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend before.1)) previous prior :=by
  have material:=objects.base.beacons index
  rw [selected] at material
  obtain ⟨actual,found,related⟩:=material
  have same :actual=self:=Option.some.inj (found.symm.trans sourceSelected)
  subst actual
  have fields:=related.phase
  simp only [AdapterPublicWrapperState.Phase,stored,phase] at fields
  have kept:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh_objects previousLocal coins setup checks configuration.agreement.representation created
    configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential
    self configuration.view control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
    stored phase before previous objects sourceSelected selected
  rw [raw_active configuration created credential (before.1,previous) objects index _ _ id (fun _=>rfl) kept]
  rw [fresh_call configuration created note self owner before.1.pool before.1.server.world.world.1.owners[owner.worldOwner]?
    related control prekey kem objects.base.objects.rng stored phase]
  have joined:=congrArg (fun tree=>(fun result=>
    let realized:=(RegistrationNativePlatformPublicAdapterConfiguration.generation configuration).realize result.1.1.1.1 objects.base.objects.rng
    (RegistrationNativePlatformPublicAdapterBundlePhysical.finish
      (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects)) index
      (AdapterPublicBundlePublication.install self prekey realized.1 kem realized.2 result.1.1.1.2,(result.1.1.2,result.1.2)),result.2)) <$>tree)
    (fresh_normalized configuration created index owner note before.1 previous prior)
  simp only [id_map,Functor.map_map] at joined ⊢
  exact joined


noncomputable def run (note :Stage→Log) (before :Store n KemSK R P) (index :Nat) (prior :List Log) :
    ProbComp ((RustM (Option Pqxdh.Bytes×Store n KemSK R P)×(Backend n KemSK×P))×List Log) :=
  match before.beacons index with
  | none=>pure ((.ok (none,before),before.backend),prior)
  | some self=>(fun result=>(RegistrationNativePlatformPublicAdapterBundlePhysical.finish before index result.1,result.2)) <$>
    call configuration created note self before.rng before.backend.1 before.backend.2 prior

omit [FrameDispatchFallback.Operations] in
private theorem run_idle (note :Stage→Log) (before :Store n KemSK R P) (index :Nat) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (found :before.beacons index=some self) (idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state) (prior :List Log) :
    run configuration created note before index prior=pure ((.ok (none,before),before.backend),prior) :=by
  have callIdle :call configuration created note self before.rng before.backend.1 before.backend.2 prior=
      pure ((.ok (.None,self,before.rng),before.backend),prior) :=by
    unfold call
    cases phase:self.state <;>simp only [phase,RegistrationNativePlatformExtractedSdkIdle.BundleIdle] at idle ⊢
  unfold run
  simp only [found]
  rw [callIdle]
  simp only [map_pure]
  have unchanged :Function.update before.beacons index (some self)=before.beacons :=by rw [←found,Function.update_eq_self]
  have same :RegistrationNativePlatformPublicAdapterStore.bundle before index (.None,self,before.rng) before.backend=before :=by
    cases before
    simp only [RegistrationNativePlatformPublicAdapterStore.bundle,unchanged]
  change pure ((RustM.ok ((none :Option Pqxdh.Bytes),RegistrationNativePlatformPublicAdapterStore.bundle before index (.None,self,before.rng) before.backend),before.backend),prior)=_
  rw [same]

omit [FrameDispatchFallback.Operations] in
private theorem raw_unchanged {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :TotalStep (Private configuration created credential) target) (prior :List Log) :
    raw configuration created credential call (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior)=
      (fun result=>(result,prior)) <$>
        RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical configuration created credential)
          (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call) :=by
  let augmented:=RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior
  let observe :{value //value∈support call.step.sample}→
      ((RustM (Option Pqxdh.Bytes×Store n KemSK R P)×(Backend n KemSK×P))×List Log) :=fun packet=>
    let after:=physical configuration created credential (call.step.native packet.val).2 (RegistrationNativePlatformExtractedSdkPublic.store call packet)
    ((.ok (RegistrationNativeRawAdapter.resultOption (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet)),after),after.backend),prior)
  have same:=congrArg (fun tree=>observe <$>tree) (RegistrationNativePlatformPublicAdapterLoggedRuntime.project_sample call augmented)
  simp only [Functor.map_map] at same
  have tail :observe <$>PFunctor.FreeM.attachSupp call.step.sample=
      (fun result=>(result,prior)) <$>
        RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical configuration created credential)
          (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call) :=by
    simp only [RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw,Functor.map_map]
    rfl
  refine Eq.trans ?_ (same.trans tail)
  unfold raw
  apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp augmented.sample)
  funext packet
  have logEq:=RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log call prior packet
  dsimp only [observe]
  rw [logEq]
  rfl

omit [FrameDispatchFallback.Operations] in
private theorem plain_query (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical configuration created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption (step configuration created credential index before previous objects))=
      RegistrationNativePlatformPublicAdapterBundlePhysical.run coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure writer children configuration.generator
        (physical configuration created credential (before.1,previous) objects) index :=by
  exact (RegistrationNativePlatformPublicAdapterNormalizedRaw.raw
    (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup configuration.view configuration.views created credential) _).trans
    ((congrArg (fun tree=>RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>tree)
      (RegistrationNativePlatformPublicAdapterBundleDispatchSource.query coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure configuration.reservePackets children
        previousLocal (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential index configuration.generator
        (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration) before previous objects)).trans
      (RegistrationNativePlatformPublicAdapterBundleNormalization.run_source coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure writer children configuration.generator
        (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects) index))

omit [FrameDispatchFallback.Operations] in
private theorem raw_transport {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (left right :TotalStep (Private configuration created credential) target) (same :left=right)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation right (List Log)) :
    raw configuration created credential left (same.symm ▸augmented)=raw configuration created credential right augmented :=by
  cases same
  rfl

omit [FrameDispatchFallback.Operations] in
theorem query (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) (note :Stage→Log) (prior :List Log) :
    raw configuration created credential (step configuration created credential index before previous objects)
      (augmentation configuration created credential index before previous objects note prior)=
      run configuration created note (physical configuration created credential (before.1,previous) objects) index prior :=by
  let beforeStore:=physical configuration created credential (before.1,previous) objects
  have backendEq :beforeStore.backend=(RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend before.1),previous):=
    congrArg RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent objects.base.backend
  cases selected:before.1.beacons[index]? with
  | none=>
    have absent:=objects.base.beacons index
    rw [selected] at absent
    have augEq :augmentation configuration created credential index before previous objects note prior=
        RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
      unfold augmentation
      exact (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
        ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans (by rfl))
    rw [augEq,raw_unchanged,plain_query]
    unfold RegistrationNativePlatformPublicAdapterBundlePhysical.run run
    change (fun result=>(result,prior)) <$>(match objects.base.objects.beacons index with | none => _ | some self => _)=
      (match objects.base.objects.beacons index with | none => _ | some self => _)
    rw [absent]
    simp only [map_pure]
  | some owner=>
    have found:=objects.base.beacons index
    rw [selected] at found
    let self:=Classical.choose found
    have sourceSelected :objects.base.objects.beacons index=some self:=(Classical.choose_spec found).1
    have related :AdapterPublicWrapperState.Beacon configuration.view setup.joint before.1.pool self owner
        before.1.server.world.world.1.owners[owner.worldOwner]? :=(Classical.choose_spec found).2
    have sourceLookup :beforeStore.beacons index=some self:=sourceSelected
    cases stored:self.state with
    | Fresh control prekey kem=>
      have phase :owner.phase=.fresh :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        rfl
      let active:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
            stored phase before previous objects sourceSelected selected
      let activeAug:=freshAugmentation configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected note prior
      have callEq :step configuration created credential index before previous objects=active :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq :augmentation configuration created credential index before previous objects note prior=callEq.symm ▸activeAug :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,raw_transport configuration created credential _ _ callEq]
      unfold run
      change _=(match beforeStore.beacons index with | none => _ | some self => _)
      simp only [sourceLookup]
      change _=(fun result=>(RegistrationNativePlatformPublicAdapterBundlePhysical.finish beforeStore index result.1,result.2)) <$>
        call configuration created note self beforeStore.rng beforeStore.backend.1 beforeStore.backend.2 prior
      rw [backendEq]
      exact fresh_joint configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected note prior
    | FreshWithCoins control prekey oneTime kem=>
      have hasScalar :∃scalar,owner.phase=.freshWithCoins scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose hasScalar
      have phase :owner.phase=.freshWithCoins scalar:=Classical.choose_spec hasScalar
      let active:=RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (fun _=>pure (.fail .panic)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected
      let activeAug:=withCoinsAugmentation configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected note prior
      have callEq :step configuration created credential index before previous objects=active :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq :augmentation configuration created credential index before previous objects note prior=callEq.symm ▸activeAug :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,raw_transport configuration created credential _ _ callEq]
      unfold run
      change _=(match beforeStore.beacons index with | none => _ | some self => _)
      simp only [sourceLookup]
      change _=(fun result=>(RegistrationNativePlatformPublicAdapterBundlePhysical.finish beforeStore index result.1,result.2)) <$>
        call configuration created note self beforeStore.rng beforeStore.backend.1 beforeStore.backend.2 prior
      rw [backendEq]
      unfold call
      rw [stored]
      exact with_coins_joint configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected note prior
    | InitSent pending prekey oneTime kem=>
      have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have augEq :augmentation configuration created credential index before previous objects note prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,raw_unchanged,plain_query]
      have noStage:=RegistrationNativePlatformPublicAdapterBundleDispatchSource.physical_idle coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure configuration.reservePackets children configuration.generator
        beforeStore index self sourceLookup idle
      rw [noStage,map_pure]
      exact (run_idle configuration created note beforeStore index self sourceLookup idle prior).symm
    | Established control binding manager=>
      have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have augEq :augmentation configuration created credential index before previous objects note prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,raw_unchanged,plain_query]
      have noStage:=RegistrationNativePlatformPublicAdapterBundleDispatchSource.physical_idle coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure configuration.reservePackets children configuration.generator
        beforeStore index self sourceLookup idle
      rw [noStage,map_pure]
      exact (run_idle configuration created note beforeStore index self sourceLookup idle prior).symm
    | Aborted control=>
      have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have augEq :augmentation configuration created credential index before previous objects note prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ control stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,raw_unchanged,plain_query]
      have noStage:=RegistrationNativePlatformPublicAdapterBundleDispatchSource.physical_idle coins setup checks configuration.agreement.representation created configuration.view
        (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure configuration.reservePackets children configuration.generator
        beforeStore index self sourceLookup idle
      rw [noStage,map_pure]
      exact (run_idle configuration created note beforeStore index self sourceLookup idle prior).symm


def outcome (result :(RustM (Option Pqxdh.Bytes×Store n KemSK R P)×(Backend n KemSK×P))×RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P) :
    RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P (Option Pqxdh.Bytes) :=
  (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects <$>result.1.1,(result.1.2.1,(result.1.2.2,result.2)))

noncomputable def loggedPhysical (current :Native×P) (objects :Private configuration created credential current)
    (prior :RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P) :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P :=
  let before:=physical configuration created credential current objects
  {before with backend:=(before.backend.1,(before.backend.2,prior))}

omit [FrameDispatchFallback.Operations] in
theorem operation_run (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) (index :Nat) :
    operation configuration created before index=
      outcome <$>run configuration created RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage
        (RegistrationNativePlatformPublicAdapterSourceEvents.store before) index before.backend.2.2 :=by
  unfold operation run
  cases selected:before.beacons index with
  | none=>simp only [RegistrationNativePlatformPublicAdapterSourceEvents.store,selected,map_pure];rfl
  | some self=>
    simp only [RegistrationNativePlatformPublicAdapterSourceEvents.store,selected,Functor.map_map]
    rw [←RegistrationNativePlatformPublicAdapterBundleLoggedSource.call_source]
    rfl

omit [FrameDispatchFallback.Operations] in
theorem source_joint (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous))
    (prior :RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P) :
    outcome <$>raw configuration created credential (step configuration created credential index before previous objects)
      (augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior)=
      operation configuration created (loggedPhysical configuration created credential (before.1,previous) objects prior) index :=by
  have same:=congrArg (fun tree=>outcome <$>tree)
    (query configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior)
  exact same.trans (operation_run configuration created (loggedPhysical configuration created credential (before.1,previous) objects prior) index).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.with_coins_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.with_coins_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.fresh_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.fresh_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.augmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.augmentation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.operation_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.operation_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged.source_joint
