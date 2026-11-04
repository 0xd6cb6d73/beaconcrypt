-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication
import BeaconcryptCore.Refinement.AdapterPublicBundleMaterial
/-! Fresh SDK Bundle uses one original key-generation primitive under matched source-coin observers. The source/backend projection preserves the actual realized key pair, RNG, all Rust outcomes, physical counters, shared cache and platform state, while erasing only the native signing journals. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
local notation "M"=>StateT (Backend n KemSK) (StateT P ProbComp)


open RegistrationNativePlatformPublicAdapterBundleDictionaries (locals crypto children getters leaves)
variable (previousLocal : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (previousCrypto : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (failure : ed.Error)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (previousChildren : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))


theorem material_source {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (owner : RegistrationNativeBeaconFrontend.Owner source)
    (secret : view.edSecret self.identity_key.secret_key=owner.identitySeed)
    (credential : view.mldsa self.authentication.identity=owner.mldsa)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) :
    let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
    let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
    let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
    AdapterPublicBundleMaterial.withMaterial setup.joint setup.dh self owner
      (leaves coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren self)
      scalar prekey oneTime kem rng=
      AdapterPublicBundlePublication.install self prekey oneTime kem rng <$>
        RegistrationNativePlatformPublicAdapterBundlePublication.program coins setup checks representation created writer owner.mldsa owner.identitySeed
          ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey := by
  let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
  let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
  let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
  dsimp only
  unfold AdapterPublicBundleMaterial.withMaterial
  rw [RegistrationNativePlatformPublicAdapterBundleDictionaries.outgoing_source coins setup checks representation created view
    previousLocal previousCrypto failure writer previousChildren self owner secret credential]
  unfold RegistrationNativePlatformPublicAdapterBundlePublication.program
  rw [RegistrationNativePlatformWriter.begin_interpret]
  simp only [bind_pure_comp]
  simp only [RegistrationNativePlatformPublicAdapterBundlePublication.handler]
  have encoded : (fun signed : registration.SignedInitView=>
      (ChildOperations.encodeInit (m:=RustT M) (AdapterPublicBundleBody.packet signed)).run)=
      (fun signed=>simulateQ (fun query=>StateT.lift (writer query))
        (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket signed)).run) := by
    funext signed
    change StateT.lift (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit
      (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E) (RegistrationNativePlatformWriter.initPacket signed)).run)=_
    exact (simulateQ_liftTarget (n:=M) writer _).symm
  rw [encoded]
  rfl

variable [original : CryptoOperations (RustT ProbComp)]
theorem fresh {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view setup.joint pool self owner world)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.Fresh control prekey kem) (phase : owner.phase=.fresh) :
    RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks representation created view previousLocal
      (RegistrationNativePlatformPublicAdapterUniformObserver.operations
        (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original)
      failure writer previousChildren generator self rng=
      (fun result=>AdapterPublicBundlePublication.install self prekey (contract.realize result.1 rng).1 kem
        (contract.realize result.1 rng).2 result.2) <$>
        RegistrationNativePlatformPublicAdapterBundlePublication.freshProgram coins setup checks representation created writer owner.mldsa owner.identitySeed
          ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner) owner.pin owner.mldsa.publicKey := by
  let observedCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original
  let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
  let : CryptoOperations (RustT M):=crypto setup view observedCrypto failure
  let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
  let generation:=RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_backend (n:=n)
    coins setup checks representation created view failure generator contract
  unfold RegistrationNativePlatformPublicAdapterBundleSource.call
  rw [AdapterPublicBundleMaterial.fresh_related view
    (getters coins setup checks representation created view previousLocal observedCrypto failure)
    setup.joint pool setup.dh self owner world related
    (leaves coins setup checks representation created view previousLocal observedCrypto failure writer previousChildren self)
    control prekey kem generator rng
    (RegistrationNativePlatformPublicAdapterBundleSigning.sample coins setup checks representation created PqxdhJointGapDh.sampleScalar)
    generation stored phase]
  unfold RegistrationNativePlatformPublicAdapterBundlePublication.freshProgram
  simp only [map_bind,bind_pure_comp]
  apply bind_congr
  intro scalar
  change AdapterPublicBundleMaterial.withMaterial setup.joint setup.dh self owner
    (leaves coins setup checks representation created view previousLocal observedCrypto failure writer previousChildren self)
    scalar prekey (contract.realize scalar rng).1 kem (contract.realize scalar rng).2=_
  simpa only [Functor.map_map] using material_source coins setup checks representation created view previousLocal observedCrypto failure writer previousChildren
    self (contract.realize scalar rng).2 owner related.identitySecret related.mldsa scalar prekey (contract.realize scalar rng).1 kem

local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "CutM"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)

theorem fresh_projection {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (previousNativeLocal : LocalOperations (RustT CutM))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec CutM)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec CutM)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.Fresh control prekey kem) (phase : owner.phase=.fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : P)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.1.beacons[index]?=some owner) :
    let nativeCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform (n:=n) (source:=source) coins setup checks representation created) original
    let : LocalOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.locals
      coins setup checks representation created writer view index owner self previousNativeLocal
    let : CryptoOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.crypto
      coins setup checks representation created writer view index owner self nativeCrypto failure
    let : ChildOperations (RustT CutM):=AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
    (fun result=>((result.1.1,RegistrationNativePlatformSdkReification.backend result.1.2.1),result.2)) <$>
      ((((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m:=RustT CutM) generator self rng).run).run before).run previous)=
      ((RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks representation created view previousLocal
        (RegistrationNativePlatformPublicAdapterUniformObserver.operations
          (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original)
        failure writer previousChildren generator self rng).run (RegistrationNativePlatformSdkReification.backend before.1)).run previous := by
  let nativeCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform (n:=n) (source:=source) coins setup checks representation created) original
  let : LocalOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.locals
    coins setup checks representation created writer view index owner self previousNativeLocal
  let : CryptoOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterBundleInstrumentation.crypto
    coins setup checks representation created writer view index owner self nativeCrypto failure
  let : ChildOperations (RustT CutM):=AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
  let nativeGeneration:=RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_native (n:=n)
    coins setup checks representation created writer view index owner self failure generator contract
  have sourceLaw:=(RegistrationNativePlatformExtractedSdkBundle.fresh_complete coins setup checks representation created writer index owner failure
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.fallback (n:=n) coins setup checks representation created owner) other recording self view
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.getters coins setup checks representation created writer view index owner self previousNativeLocal nativeCrypto failure)
    (RegistrationNativePlatformPublicAdapterBundleInstrumentation.leaves coins setup checks representation created writer view index owner self previousNativeLocal nativeCrypto failure)
    control prekey kem generator rng nativeGeneration stored phase before previous related selected).1
  have joint:=congrArg (fun distribution=>Prod.map (Prod.map id RegistrationNativePlatformSdkReification.backend) id <$>distribution) sourceLaw
  have physical:=congrArg (fun work=>(work.run (RegistrationNativePlatformSdkReification.backend before.1)).run previous)
    (fresh coins setup checks representation created view previousLocal failure writer previousChildren generator contract self rng owner before.1.pool
      before.1.server.world.world.1.owners[owner.worldOwner]? related control prekey kem stored phase)
  have tree:=congrArg (fun work=>work.run previous)
    (RegistrationNativePlatformPublicAdapterBundlePublication.fresh_tree_source coins setup checks representation created writer index owner before.1)
  dsimp only
  rw [physical,StateT.run_map,StateT.run_map,←tree]
  simpa only [RegistrationNativePlatformExtractedSdkBundle.freshRunner,StateT.run_map,Functor.map_map,Prod.map,id_eq,
    nativeGeneration,RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_native] using joint

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource.material_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource.material_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource.fresh_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFreshSource.fresh_projection
