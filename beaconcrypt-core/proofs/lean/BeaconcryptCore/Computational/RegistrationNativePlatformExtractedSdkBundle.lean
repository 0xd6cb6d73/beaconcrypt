-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleLifetime
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle
import BeaconcryptCore.Computational.RegistrationNativeBundleLifetime
import BeaconcryptCore.Refinement.AdapterPublicBundleReached
/-! The source binding for the complete extracted SDK Fresh and FreshWithCoins bundle calls and the literal corrected native bundle are projections of the same cryptographic and extracted-writer run. Exact returned source Self/private key/RNG and complete Native/platform poststates remain explicit; the native terminal projection accounts for its real pending phase and charged World advance. Initial source material derives readiness, and actual publication callbacks prove its preservation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle
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
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
variable (other : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

abbrev Publication := RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))
noncomputable def withCoinsRunner (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native) (previous : Platform) :
    ProbComp ((Publication × Native) × Platform) :=
  ((RegistrationNativeBundleLifetime.tree coins setup checks representation created writer index owner scalar).run before).run previous
noncomputable def freshRunner (before : Native) (previous : Platform) :
    ProbComp (((PqxdhJointGapDh.ScalarBytes × Publication) × Native) × Platform) :=
  ((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer index owner).run before).run previous
noncomputable def withCoinsSource {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R)
    (result : (Publication × Native) × Platform) :=
  ((AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1.1, result.1.2), result.2)
noncomputable def withCoinsNative (scalar : PqxdhJointGapDh.ScalarBytes) (result : (Publication × Native) × Platform) :=
  ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1),
    RegistrationNativeBundleLifecycle.after index owner scalar result.1.1 result.1.2), result.2)
noncomputable def freshSource {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R)
    (realize : PqxdhJointGapDh.ScalarBytes →R →beaconcrypt_crypto.crypto_kx.KeyPair × R)
    (result : ((PqxdhJointGapDh.ScalarBytes × Publication) × Native) × Platform) :=
  ((AdapterPublicBundlePublication.install self prekey (realize result.1.1.1 rng).1 kem (realize result.1.1.1 rng).2 result.1.1.2, result.1.2), result.2)
noncomputable def freshNative (result : ((PqxdhJointGapDh.ScalarBytes × Publication) × Native) × Platform) :=
  ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1.2),
    RegistrationNativeBundleLifecycle.after index owner result.1.1.1 result.1.1.2 result.1.2), result.2)

omit platform localOps in
theorem with_coins_complete {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves (n := n) coins setup checks representation created writer index owner failure self)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (stored : self.state = .FreshWithCoins control prekey oneTime kem) (phase : owner.phase = .freshWithCoins scalar)
    (publicView : view.kxPublic oneTime.public_key = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.1.beacons[index]? = some owner) :
    letI : ChildOperations (RustT CutM) := AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
    ((fun result => (Prod.map id Prod.fst result.1, result.2)) <$>
      ((((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT CutM) generator self rng).run).run before).run previous) =
      (fun result => ((AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1.1, result.1.2), result.2)) <$>
        withCoinsRunner coins setup checks representation created writer index owner scalar before.1 previous) ∧
    ((((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source writer index).run before.1).run previous) =
      (fun result => ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1),
        RegistrationNativeBundleLifecycle.after index owner scalar result.1.1 result.1.2), result.2)) <$>
        withCoinsRunner coins setup checks representation created writer index owner scalar before.1 previous) ∧
    ∀ result : (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × Native) × Platform,
      result ∈ support (withCoinsRunner coins setup checks representation created writer index owner scalar before.1 previous) →
      AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey oneTime kem scalar result.1.1 result.1.2 := by
  let : ChildOperations (RustT CutM) := AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
  simpa only [RegistrationNativePlatformExtractedBundle.bundle_source, withCoinsRunner, freshRunner] using
    AdapterPublicBundleLifetime.with_coins_complete coins setup checks representation created writer index owner failure other recording self view getters law
      control scalar prekey oneTime kem generator rng stored phase publicView before previous related selected

omit platform localOps in
theorem fresh_complete {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves (n := n) coins setup checks representation created writer index owner failure self)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformCutErasure.liftWorld (AdapterPublicBundleSourceExecution.sample (n := n) (source := source) coins setup checks representation created writer)))
    (stored : self.state = .Fresh control prekey kem) (phase : owner.phase = .fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.1.beacons[index]? = some owner) :
    letI : ChildOperations (RustT CutM) := AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
    ((fun result => (Prod.map id Prod.fst result.1, result.2)) <$>
      ((((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT CutM) generator self rng).run).run before).run previous) =
      (fun result => ((AdapterPublicBundlePublication.install self prekey
        (generation.realize result.1.1.1 rng).1 kem (generation.realize result.1.1.1 rng).2 result.1.1.2, result.1.2), result.2)) <$>
        freshRunner coins setup checks representation created writer index owner before.1 previous) ∧
    ((((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source writer index).run before.1).run previous) =
      (fun result => ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1.2),
        RegistrationNativeBundleLifecycle.after index owner result.1.1.1 result.1.1.2 result.1.2), result.2)) <$>
        freshRunner coins setup checks representation created writer index owner before.1 previous) ∧
    ∀ result : ((PqxdhJointGapDh.ScalarBytes × RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) × Native) × Platform,
      result ∈ support (freshRunner coins setup checks representation created writer index owner before.1 previous) →
      AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey (generation.realize result.1.1.1 rng).1 kem
        result.1.1.1 result.1.1.2 result.1.2 := by
  let : ChildOperations (RustT CutM) := AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
  simpa only [RegistrationNativePlatformExtractedBundle.bundle_source, withCoinsRunner, freshRunner] using
    AdapterPublicBundleLifetime.fresh_complete coins setup checks representation created writer index owner failure other recording self view getters law
      control prekey kem generator rng generation stored phase before previous related selected

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle.with_coins_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle.with_coins_complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle.fresh_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle.fresh_complete
