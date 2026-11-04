-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDictionaries
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication
import BeaconcryptCore.Refinement.AdapterPublicBundleMaterial
/-! Direct source Bundle primitive dictionaries use the actual opaque identity and signing request on the physical backend. They keep real primitive randomness/cache/platform effects and contain no owner history or private hash-cut journal. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource
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

noncomputable def call {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R) :=
  let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
  let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
  let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
  (beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m:=RustT M) generator self rng).run

theorem with_coins {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view setup.joint pool self owner world)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.FreshWithCoins control prekey oneTime kem) (phase : owner.phase=.freshWithCoins scalar)
    (publicView : view.kxPublic oneTime.public_key=PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) :
    call coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren generator self rng=
      AdapterPublicBundlePublication.install self prekey oneTime kem rng <$>
        RegistrationNativePlatformPublicAdapterBundlePublication.program coins setup checks representation created writer owner.mldsa owner.identitySeed
          ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey := by
  let : LocalOperations (RustT M):=locals coins setup checks representation created view previousLocal
  let : CryptoOperations (RustT M):=crypto setup view previousCrypto failure
  let : ChildOperations (RustT M):=children coins setup checks representation created writer previousChildren
  unfold call
  rw [AdapterPublicBundleMaterial.with_coins_related view
    (getters coins setup checks representation created view previousLocal previousCrypto failure)
    setup.joint pool setup.dh self owner world related
    (leaves coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren self)
    control scalar prekey oneTime kem generator rng stored phase publicView]
  unfold AdapterPublicBundleMaterial.withMaterial
  rw [RegistrationNativePlatformPublicAdapterBundleDictionaries.outgoing_source coins setup checks representation created view
    previousLocal previousCrypto failure writer previousChildren self owner related.identitySecret related.mldsa]
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

local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "CutM"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)
variable [nativeLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp)))]
variable [nativeCrypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp)))]

theorem with_coins_projection {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (fallback : registration.MldsaSigningRequest→StateT Native (StateT P ProbComp) RegistrationSigningShared.SignReply)
    (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec CutM)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec CutM)
    (nativeGetters : AdapterPublicBundleMaterial.Getters (m:=CutM) view)
    (nativeLeaves : AdapterPublicBundleSourceExecution.Leaves coins setup checks representation created writer index owner failure fallback self)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.FreshWithCoins control prekey oneTime kem) (phase : owner.phase=.freshWithCoins scalar)
    (publicView : view.kxPublic oneTime.public_key=PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : P)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.1.beacons[index]?=some owner) :
    let : ChildOperations (RustT CutM):=AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
    (fun result=>((result.1.1,RegistrationNativePlatformSdkReification.backend result.1.2.1),result.2)) <$>
      ((((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m:=RustT CutM) generator self rng).run).run before).run previous)=
      ((call coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren generator self rng).run
        (RegistrationNativePlatformSdkReification.backend before.1)).run previous := by
  let : ChildOperations (RustT CutM):=AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
  have sourceLaw:=(RegistrationNativePlatformExtractedSdkBundle.with_coins_complete coins setup checks representation created writer
    index owner failure fallback other recording self view nativeGetters nativeLeaves control scalar prekey oneTime kem generator rng stored phase publicView before previous related selected).1
  have joint:=congrArg (fun distribution=>Prod.map (Prod.map id RegistrationNativePlatformSdkReification.backend) id <$>distribution) sourceLaw
  have physical:=congrArg (fun work=>(work.run (RegistrationNativePlatformSdkReification.backend before.1)).run previous)
    (with_coins coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren generator self rng owner before.1.pool
      before.1.server.world.world.1.owners[owner.worldOwner]? related control scalar prekey oneTime kem stored phase publicView)
  dsimp only
  rw [physical,StateT.run_map,StateT.run_map,←RegistrationNativePlatformPublicAdapterBundlePublication.tree_platform
    coins setup checks representation created writer index owner scalar before.1 previous]
  simpa only [RegistrationNativePlatformExtractedSdkBundle.withCoinsRunner,Functor.map_map,Prod.map,id_eq] using joint

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource.with_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource.with_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource.with_coins_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource.with_coins_projection
