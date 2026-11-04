-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle
/-! The selected actual SDK Bundle source marginal factors to independent physical source dictionaries. Concrete signing instrumentation and paired generation observers are derived internally; the same source result and actual primitive/platform poststate determine the next stored objects. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource
open RegistrationNativePlatformExtractedSdkAdaptive (pack)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformExtractedSdkAdaptiveBundle (bytes bytes_public)
open RegistrationNativePlatformExtractedSdkBundle (Publication withCoinsRunner freshRunner withCoinsNative freshNative)
open BeaconcryptCore.Refinement
open BeaconcryptCore.Computational
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK E Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "M" => StateT Platform ProbComp
local notation "CutM" => StateT (RegistrationNativePlatformCutJournal.State Native) M
variable [original : CryptoOperations (RustT ProbComp)]
variable (previousLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp))))
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
local notation "packetWriter" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
variable (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)


noncomputable abbrev withCoins {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (stored : self.state=.FreshWithCoins control prekey oneTime kem) (phase : owner.phase=.freshWithCoins scalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner) :=
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform (n:=n) (source:=source) coins setup checks representation created) original
  letI : LocalOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.locals
    coins setup checks representation created packetWriter view index owner self previousLocal
  letI : CryptoOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.crypto
    coins setup checks representation created packetWriter view index owner self previousCrypto failure
  RegistrationNativePlatformSdkStrongBundleSteps.withCoins coins setup checks representation created reservePackets index owner failure
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.fallback (n:=n) coins setup checks representation created owner) other recording containersView credential
    self view
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.getters coins setup checks representation created packetWriter view index owner self previousLocal previousCrypto failure)
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.leaves coins setup checks representation created packetWriter view index owner self previousLocal previousCrypto failure)
    control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected

noncomputable abbrev fresh {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (stored : self.state=.Fresh control prekey kem) (phase : owner.phase=.fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner) :=
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform (n:=n) (source:=source) coins setup checks representation created) original
  letI : LocalOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.locals
    coins setup checks representation created packetWriter view index owner self previousLocal
  letI : CryptoOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.crypto
    coins setup checks representation created packetWriter view index owner self previousCrypto failure
  RegistrationNativePlatformSdkStrongBundleSteps.fresh coins setup checks representation created reservePackets index owner failure
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.fallback (n:=n) coins setup checks representation created owner) other recording containersView credential
    self view
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.getters coins setup checks representation created packetWriter view index owner self previousLocal previousCrypto failure)
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.leaves coins setup checks representation created packetWriter view index owner self previousLocal previousCrypto failure)
    control prekey kem generator
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_native (n:=n) coins setup checks representation created packetWriter view index owner self failure generator contract)
    stored phase before previous objects sourceSelected selected

theorem with_coins_source {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (stored : self.state=.FreshWithCoins control prekey oneTime kem) (phase : owner.phase=.freshWithCoins scalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner)
    (physicalLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) M)))
    (physicalChildren : ChildOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) M))) :
    let call:=withCoins previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected
    Prod.map id RegistrationNativePlatformSdkReification.persistent <$>call.step.sourceCall=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        ((RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks representation created view physicalLocal
          (RegistrationNativePlatformPublicAdapterUniformObserver.operations
            (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original)
          failure packetWriter physicalChildren generator self objects.base.objects.rng).run
          (RegistrationNativePlatformSdkReification.backend before.1)).run previous := by
  have prior:=objects.base.beacons index
  rw [selected] at prior
  obtain ⟨actual,found,related⟩:=prior
  have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
  subst actual
  have privateView : view.kxSecret oneTime.secret_key=scalar := by
    have fields:=related.phase
    simp only [AdapterPublicWrapperState.Phase,stored,phase] at fields
    exact fields.2.2.1
  have publicView:=RegistrationNativePlatformSdkStrongCarrier.one_time_public setup view containersView created credential
    (before.1,previous) objects index self control prekey oneTime kem scalar sourceSelected stored privateView
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform (n:=n) (source:=source) coins setup checks representation created) original
  let : LocalOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.locals
    coins setup checks representation created packetWriter view index owner self previousLocal
  let : CryptoOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.crypto
    coins setup checks representation created packetWriter view index owner self previousCrypto failure
  have law:=RegistrationNativePlatformPublicAdapterBundleSource.with_coins_projection coins setup checks representation created view physicalLocal
    (RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original)
    failure packetWriter physicalChildren generator self objects.base.objects.rng index owner
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.fallback (n:=n) coins setup checks representation created owner) other recording
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.getters coins setup checks representation created packetWriter view index owner self previousLocal previousCrypto failure)
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.leaves coins setup checks representation created packetWriter view index owner self previousLocal previousCrypto failure)
    control scalar prekey oneTime kem stored phase publicView before previous related selected
  have packed:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>work) law
  simpa only [withCoins,RegistrationNativePlatformSdkStrongBundleSteps.withCoins,
    RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.withCoins,RegistrationNativePlatformExtractedSdkAdaptiveBundle.withCoins,
    Functor.map_map,RegistrationNativePlatformSdkReification.persistent,Prod.map,id_eq] using packed

theorem fresh_source {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (stored : self.state=.Fresh control prekey kem) (phase : owner.phase=.fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner)
    (physicalLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) M)))
    (physicalChildren : ChildOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) M))) :
    let call:=fresh previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control prekey kem generator contract stored phase before previous objects sourceSelected selected
    Prod.map id RegistrationNativePlatformSdkReification.persistent <$>call.step.sourceCall=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        ((RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks representation created view physicalLocal
          (RegistrationNativePlatformPublicAdapterUniformObserver.operations
            (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original)
          failure packetWriter physicalChildren generator self objects.base.objects.rng).run
          (RegistrationNativePlatformSdkReification.backend before.1)).run previous := by
  have prior:=objects.base.beacons index
  rw [selected] at prior
  obtain ⟨actual,found,related⟩:=prior
  have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
  subst actual
  have law:=RegistrationNativePlatformPublicAdapterBundleFreshSource.fresh_projection coins setup checks representation created view physicalLocal failure
    packetWriter physicalChildren generator contract previousLocal self objects.base.objects.rng index owner other recording
    control prekey kem stored phase before previous related selected
  have packed:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>work) law
  simpa only [fresh,RegistrationNativePlatformSdkStrongBundleSteps.fresh,
    RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.fresh,RegistrationNativePlatformExtractedSdkAdaptiveBundle.fresh,
    Functor.map_map,RegistrationNativePlatformSdkReification.persistent,Prod.map,id_eq] using packed

theorem with_coins_objects {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (stored : self.state=.FreshWithCoins control prekey oneTime kem) (phase : owner.phase=.freshWithCoins scalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner) :
    let call:=withCoins previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected
    ∀packet : {value //value∈support call.step.sample},
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects=
      RegistrationNativePlatformExtractedSdkCarrierBundle.update objects.base.objects index
        (RegistrationNativePlatformExtractedSdkPublic.returned call packet) (call.step.sourceState packet.val) := by
  let call:=withCoins previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
    self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected
  dsimp only
  intro packet
  rcases packet with ⟨⟨⟨publication,during⟩,next⟩,supported⟩
  cases publication with
  | fail error=>
    have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨((.fail error,during),next),supported⟩
    cases actual
  | div=>
    have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨((.div,during),next),supported⟩
    cases actual
  | ok publication=>
    cases publication <;>
      have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨((.ok _,during),next),supported⟩
    all_goals
      change (RustM.ok _ : RustM (core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R))=RustM.ok _ at actual
      have same:=(RustM.ok.inj actual).symm
      unfold RegistrationNativePlatformExtractedSdkPublic.store
      rw [same]
      rfl

theorem fresh_objects {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (stored : self.state=.Fresh control prekey kem) (phase : owner.phase=.fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner) :
    let call:=fresh previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control prekey kem generator contract stored phase before previous objects sourceSelected selected
    ∀packet : {value //value∈support call.step.sample},
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects=
      RegistrationNativePlatformExtractedSdkCarrierBundle.update objects.base.objects index
        (RegistrationNativePlatformExtractedSdkPublic.returned call packet) (call.step.sourceState packet.val) := by
  let call:=fresh previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
    self view control prekey kem generator contract stored phase before previous objects sourceSelected selected
  dsimp only
  intro packet
  rcases packet with ⟨⟨⟨⟨scalar,publication⟩,during⟩,next⟩,supported⟩
  cases publication with
  | fail error=>
    have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨(((scalar,.fail error),during),next),supported⟩
    cases actual
  | div=>
    have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨(((scalar,.div),during),next),supported⟩
    cases actual
  | ok publication=>
    cases publication <;>
      have actual:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨(((scalar,.ok _),during),next),supported⟩
    all_goals
      change (RustM.ok _ : RustM (core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R))=RustM.ok _ at actual
      have same:=(RustM.ok.inj actual).symm
      unfold RegistrationNativePlatformExtractedSdkPublic.store
      rw [same]
      rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.with_coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.with_coins_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.fresh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.fresh_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.with_coins_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.with_coins_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.fresh_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource.fresh_objects
