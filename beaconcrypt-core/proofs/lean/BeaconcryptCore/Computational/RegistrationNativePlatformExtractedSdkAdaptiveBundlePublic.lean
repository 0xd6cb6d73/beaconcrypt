-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleNormal
/-! Both active SDK bundle calls provide the actual returned public bytes and derived normality to the adaptive public interpreter. The concrete writer is fixed internally; all source objects, RNG and reached platform state remain on the original common runner. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic
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
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
local notation "packetWriter" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
variable (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp) RegistrationSigningShared.SignReply)
variable (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

noncomputable def withCoins {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves coins setup checks representation created packetWriter index owner failure fallback self)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (stored : self.state = .FreshWithCoins control prekey oneTime kem) (phase : owner.phase = .freshWithCoins scalar)
    (publicView : view.kxPublic oneTime.public_key = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.1.beacons[index]? = some owner)
    (Private : (Native ×Platform) →Type)
    (put : ∀(packet : (Publication ×Native) ×Platform),
      packet∈support (withCoinsRunner coins setup checks representation created packetWriter index owner scalar before.1 previous) →
      AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey oneTime kem scalar packet.1.1 packet.1.2 →
      ∀returned,AdapterPublicBundlePublication.install self prekey oneTime kem rng packet.1.1=.ok returned →
        bytes (.ok returned)=(pack (withCoinsNative index owner scalar packet)).1 →
        Private (pack (withCoinsNative index owner scalar packet)).2) :
    TotalStep Private (pack <$> ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source packetWriter index).run before.1).run previous) := by
  let selected:=RegistrationNativePlatformExtractedSdkAdaptiveBundle.withCoins coins setup checks representation created packetWriter index owner failure fallback other recording
    self view getters law control scalar prekey oneTime kem generator rng stored phase publicView before previous related selected Private put
  refine {step:=selected,observe:=fun value=>bytes (.ok value),normal:=?_,reply:=?_}
  · intro packet supported
    apply RegistrationNativePlatformBundleNormal.publication_install
    exact RegistrationNativePlatformBundleNormal.tree coins setup checks representation created reservePackets index owner scalar before.1 previous packet supported
  · intro packet supported returned resultEq
    change AdapterPublicBundlePublication.install self prekey oneTime kem rng packet.1.1=.ok returned at resultEq
    have same:=bytes_public self prekey oneTime kem rng packet.1.1
    rw [resultEq] at same
    exact same

noncomputable def fresh {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves coins setup checks representation created packetWriter index owner failure fallback self)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformCutErasure.liftWorld (AdapterPublicBundleSourceExecution.sample (n := n) (source := source) coins setup checks representation created packetWriter)))
    (stored : self.state = .Fresh control prekey kem) (phase : owner.phase = .fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.1.beacons[index]? = some owner)
    (Private : (Native ×Platform) →Type)
    (put : ∀(packet : ((PqxdhJointGapDh.ScalarBytes ×Publication) ×Native) ×Platform),
      packet∈support (freshRunner coins setup checks representation created packetWriter index owner before.1 previous) →
      AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey (generation.realize packet.1.1.1 rng).1 kem packet.1.1.1 packet.1.1.2 packet.1.2 →
      ∀returned,AdapterPublicBundlePublication.install self prekey (generation.realize packet.1.1.1 rng).1 kem (generation.realize packet.1.1.1 rng).2 packet.1.1.2=.ok returned →
        bytes (.ok returned)=(pack (freshNative index owner packet)).1 →
        Private (pack (freshNative index owner packet)).2) :
    TotalStep Private (pack <$> ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source packetWriter index).run before.1).run previous) := by
  let selected:=RegistrationNativePlatformExtractedSdkAdaptiveBundle.fresh coins setup checks representation created packetWriter index owner failure fallback other recording
    self view getters law control prekey kem generator rng generation stored phase before previous related selected Private put
  refine {step:=selected,observe:=fun value=>bytes (.ok value),normal:=?_,reply:=?_}
  · intro packet supported
    apply RegistrationNativePlatformBundleNormal.publication_install
    exact RegistrationNativePlatformBundleNormal.fresh coins setup checks representation created reservePackets index owner before.1 previous packet supported
  · intro packet supported returned resultEq
    change AdapterPublicBundlePublication.install self prekey (generation.realize packet.1.1.1 rng).1 kem (generation.realize packet.1.1.1 rng).2 packet.1.1.2=.ok returned at resultEq
    have same:=bytes_public self prekey (generation.realize packet.1.1.1 rng).1 kem (generation.realize packet.1.1.1 rng).2 packet.1.1.2
    rw [resultEq] at same
    exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.withCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.withCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.fresh
