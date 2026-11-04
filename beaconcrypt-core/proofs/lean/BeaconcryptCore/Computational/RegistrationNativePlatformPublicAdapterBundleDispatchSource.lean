-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases
/-! The full Bundle source dispatcher has the literal SDK physical marginal, including missing and inactive source objects. Active source primitive dictionaries and their same-result object/RNG updates are derived by the existing paired Bundle source laws. Public result conversion retains the same private packet and full terminal backend. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep returned returned_exact store)
open RegistrationNativePlatformPublicAdapterStore (Store erase bundle)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw strongPhysical)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterBundlePhysical (Word)
variable {n : Nat} {I KemSK E P R Error : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

omit material platform ed original in
private noncomputable def transport {N A : Type} {Private : N→Type} {left right : ProbComp (A×N)}
    (same : left=right) (call : TotalStep Private left) :TotalStep Private right:=same ▸call
omit material platform ed original in
private theorem mpr_transport {N A : Type} {Private : N→Type} {left right : ProbComp (A×N)}
    (same : left=right) (typeEq : TotalStep Private left=TotalStep Private right) (call : TotalStep Private right) :
    Eq.mpr typeEq call=transport same.symm call :=by
  cases same
  rfl
omit original in
private theorem raw_transport {N A B : Type} {Private : N→Type} {left right : ProbComp (A×N)}
    (same : left=right) (call : TotalStep Private left) (observe : A→B)
    (project : ∀current,Private current→Store n KemSK R P) :
    raw project (RegistrationNativePlatformPublicAdapterReply.map observe (transport same call))=
      raw project (RegistrationNativePlatformPublicAdapterReply.map observe call) :=by
  cases same
  rfl

variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (physicalLocal : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (failure : ed.Error) (reservePackets : Usize→StateT P ProbComp (core.result.Result Unit E))
variable (physicalChildren : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
local notation "packetWriter"=>RegistrationNativePlatformConcreteSource.writer reservePackets

 theorem call_idle (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state) :
    RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks representation created view physicalLocal
      (RegistrationNativePlatformPublicAdapterUniformObserver.operations
        (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original)
      failure packetWriter physicalChildren generator self rng=pure (.ok (.None,self,rng)) :=by
  let : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterBundleDictionaries.locals coins setup checks representation created view physicalLocal
  let : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterBundleDictionaries.crypto setup view
      (RegistrationNativePlatformPublicAdapterUniformObserver.operations
        (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original) failure
  let : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterBundleDictionaries.children coins setup checks representation created packetWriter physicalChildren
  unfold RegistrationNativePlatformPublicAdapterBundleSource.call
  exact RegistrationNativePlatformExtractedSdkIdle.bundle_source generator self rng idle

 theorem physical_idle (generator : rand_core.TryCryptoRng R Error) (before : Store n KemSK R P)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (found : before.beacons index=some self) (idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state) :
    RegistrationNativePlatformPublicAdapterBundlePhysical.run coins setup checks representation created view physicalLocal failure packetWriter physicalChildren
      generator before index=pure (.ok (none,before),before.backend) :=by
  unfold RegistrationNativePlatformPublicAdapterBundlePhysical.run
  simp only [found]
  unfold RegistrationNativePlatformPublicAdapterBundlePhysical.call
  rw [call_idle coins setup checks representation created view physicalLocal failure reservePackets physicalChildren generator self before.rng idle]
  simp only [StateT.run_pure,map_pure]
  have unchanged : Function.update before.beacons index (some self)=before.beacons :=by
    rw [←found,Function.update_eq_self]
  have same : bundle before index (.None,self,before.rng) before.backend=before :=by
    cases before
    simp only [bundle,unchanged]
  change pure (RustM.ok ((none :Option Pqxdh.Bytes),bundle before index (.None,self,before.rng) before.backend),before.backend)=_
  rw [same]

omit original in
private noncomputable def missing
    (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source) (current : Native×P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (pure ((.ok none :RustM (Option Pqxdh.Bytes)),current)) := {
  step:={ Packet:=Unit
          sample:=pure ()
          sourceType:=Option Pqxdh.Bytes
          sourceReply:=fun _=>.ok none
          sourceState:=fun _=>objects.base.objects.snapshot.committed
          sourceCall:=pure (.ok none,objects.base.objects.snapshot.committed)
          source_exact:=rfl
          native:=fun _=>(.ok none,current)
          native_exact:=rfl
          store:=fun _ _=>objects }
  observe:=RustM.ok
  normal:=fun _ _=>⟨none,rfl⟩
  reply:=by intro _packet _supported returned actual;cases actual;rfl }

omit original in
private theorem missing_raw
    (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source) (current : Native×P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    raw (strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
        (missing setup created view views credential current objects))=
      pure (.ok (none,erase objects.base.objects),(erase objects.base.objects).backend) :=by
  let call:=missing setup created view views credential current objects
  let result:=(RustM.ok ((none :Option Pqxdh.Bytes),erase objects.base.objects),(erase objects.base.objects).backend)
  unfold raw
  calc
    _=(fun _ :{value //value∈support call.step.sample}=>result) <$>PFunctor.FreeM.attachSupp call.step.sample :=by
      congr 1
      funext packet
      have same : returned call packet=none := (RustM.ok.inj (returned_exact call packet)).symm
      change (RustM.ok (RegistrationNativeRawAdapter.resultOption (call.observe (returned call packet)),erase (store call packet).base.objects),
        (erase (store call packet).base.objects).backend)=_
      rw [same]
      rfl
    _=pure result :=rfl

variable [idleLocal : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp))]
variable [idleCrypto : CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp))]
variable [idleChildren : ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp))]
omit original in
private theorem idle_raw (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×P) (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state) :
    raw (strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
        (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle
          (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
          current objects.base.objects.snapshot.committed objects generator self objects.base.objects.rng idle))=
      pure (.ok (none,erase objects.base.objects),(erase objects.base.objects).backend) :=by
  let call:=RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      current objects.base.objects.snapshot.committed objects generator self objects.base.objects.rng idle
  let result:=(RustM.ok ((none :Option Pqxdh.Bytes),erase objects.base.objects),(erase objects.base.objects).backend)
  unfold raw
  calc
    _=(fun _ :{value //value∈support call.step.sample}=>result) <$>PFunctor.FreeM.attachSupp call.step.sample :=by
      congr 1
      funext packet
      have same : returned call packet=(core.option.Option.None,self,objects.base.objects.rng) := (RustM.ok.inj (returned_exact call packet)).symm
      change (RustM.ok (RegistrationNativeRawAdapter.resultOption (call.observe (returned call packet)),erase (store call packet).base.objects),
        (erase (store call packet).base.objects).backend)=_
      rw [same]
      rfl
    _=pure result :=rfl

variable (previousLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp))))
variable (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp)))
variable (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)


theorem query (index : Nat) (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential (before.1,previous)) :
    raw (strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
        (RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks representation created reservePackets
          index failure other recording views credential view generator contract before previous objects))=
      RegistrationNativePlatformPublicAdapterBundlePhysical.run coins setup checks representation created view physicalLocal failure
        packetWriter physicalChildren generator (erase objects.base.objects) index :=by
  cases selected:before.1.beacons[index]? with
  | none=>
    have absent:=objects.base.beacons index
    rw [selected] at absent
    have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
      (RegistrationNativePlatformExtractedSdkBundleDispatch.missing_model coins setup checks representation created reservePackets index before.1 previous selected)
    simp only [map_pure] at pureLaw
    have callEq : RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks representation created reservePackets
        index failure other recording views credential view generator contract before previous objects = transport pureLaw.symm
          (missing setup created view views credential (before.1,previous) objects) :=by
      unfold RegistrationNativePlatformPublicAdapterStrongBundle.step
      apply (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
      apply (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
      exact mpr_transport pureLaw _ _
    calc
      _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption _) :=
        congrArg (fun call=>raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)) callEq
      _=pure (.ok (none,erase objects.base.objects),(erase objects.base.objects).backend) :=by
        rw [raw_transport]
        exact missing_raw setup created view views credential (before.1,previous) objects
      _=_ :=by
        unfold RegistrationNativePlatformPublicAdapterBundlePhysical.run
        change _=(match objects.base.objects.beacons index with | none=>_ | some self=>_)
        rw [absent]
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected:objects.base.objects.beacons index=some self:=(Classical.choose_spec prior).1
    have related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner
      before.1.server.world.world.1.owners[owner.worldOwner]? := (Classical.choose_spec prior).2
    cases stored:self.state with
    | Fresh control prekey kem=>
      have phase : owner.phase=.fresh :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;> simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        rfl
      have callEq : RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks representation created reservePackets
          index failure other recording views credential view generator contract before previous objects =
          RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks representation created reservePackets index owner failure other recording views credential
            self view control prekey kem generator contract stored phase before previous objects sourceSelected selected :=by
        unfold RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      calc
        _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption _) :=
          congrArg (fun call=>raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)) callEq
        _=_ :=by
          rw [RegistrationNativePlatformPublicAdapterBundlePhysical.fresh coins setup checks representation created failure previousLocal reservePackets index owner other recording views credential
            self view control prekey kem generator contract stored phase before previous objects sourceSelected selected physicalLocal physicalChildren]
          unfold RegistrationNativePlatformPublicAdapterBundlePhysical.run
          change _=(match objects.base.objects.beacons index with | none=>_ | some self=>_)
          rw [sourceSelected]
    | FreshWithCoins control prekey oneTime kem=>
      have phase : ∃scalar,owner.phase=.freshWithCoins scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;> simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose phase
      have phase:owner.phase=.freshWithCoins scalar:=Classical.choose_spec phase
      have callEq : RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks representation created reservePackets
          index failure other recording views credential view generator contract before previous objects =
          RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks representation created reservePackets index owner failure other recording views credential
            self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected :=by
        unfold RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      calc
        _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption _) :=
          congrArg (fun call=>raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)) callEq
        _=_ :=by
          rw [RegistrationNativePlatformPublicAdapterBundlePhysical.with_coins coins setup checks representation created failure previousLocal reservePackets index owner other recording views credential
            self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected physicalLocal physicalChildren]
          unfold RegistrationNativePlatformPublicAdapterBundlePhysical.run
          change _=(match objects.base.objects.beacons index with | none=>_ | some self=>_)
          rw [sourceSelected]
    | InitSent pending prekey oneTime kem=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.bundle_phase view before.1.pool owner self.state
        before.1.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
        (RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model coins setup checks representation created reservePackets index owner before.1 previous selected inactive)
      simp only [map_pure] at pureLaw
      have callEq : RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks representation created reservePackets
          index failure other recording views credential view generator contract before previous objects = transport pureLaw.symm
          (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle
            (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
            (before.1,previous) objects.base.objects.snapshot.committed objects generator self objects.base.objects.rng idle) :=by
        unfold RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by exact mpr_transport pureLaw _ _))))
      calc
        _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption _) :=
          congrArg (fun call=>raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)) callEq
        _=pure (.ok (none,erase objects.base.objects),(erase objects.base.objects).backend) :=by
          rw [raw_transport]
          exact idle_raw setup created view views credential (before.1,previous) objects generator self idle
        _=_ :=by
          exact (physical_idle coins setup checks representation created view physicalLocal failure reservePackets physicalChildren
            generator (erase objects.base.objects) index self sourceSelected idle).symm
    | Established control binding manager=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.bundle_phase view before.1.pool owner self.state
        before.1.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
        (RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model coins setup checks representation created reservePackets index owner before.1 previous selected inactive)
      simp only [map_pure] at pureLaw
      have callEq : RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks representation created reservePackets
          index failure other recording views credential view generator contract before previous objects = transport pureLaw.symm
          (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle
            (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
            (before.1,previous) objects.base.objects.snapshot.committed objects generator self objects.base.objects.rng idle) :=by
        unfold RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by exact mpr_transport pureLaw _ _))))
      calc
        _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption _) :=
          congrArg (fun call=>raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)) callEq
        _=pure (.ok (none,erase objects.base.objects),(erase objects.base.objects).backend) :=by
          rw [raw_transport]
          exact idle_raw setup created view views credential (before.1,previous) objects generator self idle
        _=_ :=by
          exact (physical_idle coins setup checks representation created view physicalLocal failure reservePackets physicalChildren
            generator (erase objects.base.objects) index self sourceSelected idle).symm
    | Aborted control=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.bundle_phase view before.1.pool owner self.state
        before.1.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
        (RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model coins setup checks representation created reservePackets index owner before.1 previous selected inactive)
      simp only [map_pure] at pureLaw
      have callEq : RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal coins setup checks representation created reservePackets
          index failure other recording views credential view generator contract before previous objects = transport pureLaw.symm
          (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle
            (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
            (before.1,previous) objects.base.objects.snapshot.committed objects generator self objects.base.objects.rng idle) :=by
        unfold RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ control stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by exact mpr_transport pureLaw _ _))))
      calc
        _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption _) :=
          congrArg (fun call=>raw (strongPhysical setup view views created credential) (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)) callEq
        _=pure (.ok (none,erase objects.base.objects),(erase objects.base.objects).backend) :=by
          rw [raw_transport]
          exact idle_raw setup created view views credential (before.1,previous) objects generator self idle
        _=_ :=by
          exact (physical_idle coins setup checks representation created view physicalLocal failure reservePackets physicalChildren
            generator (erase objects.base.objects) index self sourceSelected idle).symm

include previousLocal other recording in
theorem normal (index : Nat) (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential (before.1,previous))
    (result : RustM (Option Pqxdh.Bytes×Store n KemSK R P) ×(Backend n KemSK ×P))
    (supported : result∈support (RegistrationNativePlatformPublicAdapterBundlePhysical.run coins setup checks representation created view physicalLocal failure
      packetWriter physicalChildren generator (erase objects.base.objects) index)) :
    ∃word,result.1=.ok word ∧result.2=word.2.backend :=by
  have actual:=Eq.mp (congrArg (fun tree=>result∈support tree)
    (query coins setup checks representation created view physicalLocal failure reservePackets physicalChildren
      previousLocal other recording views credential index generator contract before previous objects).symm) supported
  simp only [raw,support_map] at actual
  obtain ⟨packet,_possible,same⟩:=actual
  cases same
  exact ⟨_,rfl,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.call_idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.call_idle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.physical_idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.physical_idle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource.normal
