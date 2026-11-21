-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle
/-! Active bundle calls build their complete next private carrier internally from the same actual source result. Only individual opaque-object getter, generation, signing and dictionary contracts remain explicit. The caller supplies neither a continuation carrier nor a complete callback or security law. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps
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
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
local notation "packetWriter" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
variable (other : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)

noncomputable def withCoins {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves (n := n) coins setup checks representation created packetWriter index owner failure self)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (stored : self.state = .FreshWithCoins control prekey oneTime kem) (phase : owner.phase = .freshWithCoins scalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self)
    (selected : before.1.beacons[index]? = some owner)
 :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      (pack <$> ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source packetWriter index).run before.1).run previous) := by
  have related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]? := by
    have prior:=objects.base.beacons index
    rw [selected] at prior
    obtain ⟨actual,found,material⟩ := prior
    have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
    subst actual
    exact material
  have privateView : view.kxSecret oneTime.secret_key=scalar := by
    have fields:=related.phase
    simp only [AdapterPublicWrapperState.Phase,stored,phase] at fields
    exact fields.2.2.1
  have publicView:=RegistrationNativePlatformSdkStrongCarrier.one_time_public setup view containersView created credential
    (before.1,previous) objects index self control prekey oneTime kem scalar sourceSelected stored privateView
  have ready:=RegistrationNativeBundleLifetime.with_coins_ready setup view self owner before.1 related control prekey oneTime kem scalar stored phase
  apply RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.withCoins coins setup checks representation created reservePackets index owner failure other recording
    self view getters law control scalar prekey oneTime kem generator objects.base.objects.rng stored phase publicView before previous related selected
  intro packet supported material returned resultEq publicEq
  have kept:=RegistrationNativeBundleSafety.interpreted_snapshot coins setup checks representation created packetWriter _
    (RegistrationNativeBundleSafety.publication_safe setup index owner scalar) before.1 previous packet supported
  have image:=RegistrationNativePlatformSdkServerFrame.bundle_tree coins setup checks representation created packetWriter index owner scalar before.1 previous packet supported
  have called:((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value packet.1.1),
      RegistrationNativeBundleLifecycle.after index owner scalar packet.1.1 packet.1.2),packet.2)∈support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source packetWriter index).run before.1).run previous) := by
    rw [RegistrationNativeBundleLifetime.with_coins coins setup checks representation created packetWriter index owner scalar before.1 previous selected phase ready,support_map]
    exact ⟨packet,supported,rfl⟩
  let baseAfter:=RegistrationNativePlatformExtractedSdkCarrierBundle.put coins setup checks representation created packetWriter view containersView credential
    (before.1,previous) objects.base index owner selected self sourceSelected prekey oneTime kem scalar objects.base.objects.rng packet.1.1 packet.1.2 packet.2 kept image called returned resultEq material
  exact RegistrationNativePlatformSdkStrongCarrier.publication setup view containersView created credential (before.1,previous) _ objects baseAfter
    index self sourceSelected prekey oneTime kem objects.base.objects.rng packet.1.1 returned resultEq rfl

noncomputable def fresh {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves (n := n) coins setup checks representation created packetWriter index owner failure self)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformCutErasure.liftWorld (AdapterPublicBundleSourceExecution.sample (n := n) (source := source) coins setup checks representation created packetWriter)))
    (stored : self.state = .Fresh control prekey kem) (phase : owner.phase = .fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self)
    (selected : before.1.beacons[index]? = some owner)
 :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      (pack <$> ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source packetWriter index).run before.1).run previous) := by
  have related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]? := by
    have prior:=objects.base.beacons index
    rw [selected] at prior
    obtain ⟨actual,found,material⟩ := prior
    have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
    subst actual
    exact material
  have ready:=RegistrationNativeBundleLifetime.fresh_ready setup view self owner before.1 related control prekey kem stored phase
  apply RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic.fresh coins setup checks representation created reservePackets index owner failure other recording
    self view getters law control prekey kem generator objects.base.objects.rng generation stored phase before previous related selected
  intro packet supported material returned resultEq publicEq
  have kept:=AdapterPublicBundleReached.fresh_snapshot coins setup checks representation created packetWriter index owner before.1 previous packet supported
  have image:=RegistrationNativePlatformSdkServerFrame.bundle_fresh_tree coins setup checks representation created packetWriter index owner before.1 previous packet supported
  have called:((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value packet.1.1.2),
      RegistrationNativeBundleLifecycle.after index owner packet.1.1.1 packet.1.1.2 packet.1.2),packet.2)∈support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source packetWriter index).run before.1).run previous) := by
    rw [RegistrationNativeBundleLifetime.fresh coins setup checks representation created packetWriter index owner before.1 previous selected phase ready,support_map]
    exact ⟨packet,supported,rfl⟩
  let baseAfter:=RegistrationNativePlatformExtractedSdkCarrierBundle.put coins setup checks representation created packetWriter view containersView credential
    (before.1,previous) objects.base index owner selected self sourceSelected prekey (generation.realize packet.1.1.1 objects.base.objects.rng).1 kem packet.1.1.1
    (generation.realize packet.1.1.1 objects.base.objects.rng).2 packet.1.1.2 packet.1.2 packet.2 kept image called returned resultEq material
  exact RegistrationNativePlatformSdkStrongCarrier.publication setup view containersView created credential (before.1,previous) _ objects baseAfter
    index self sourceSelected prekey (generation.realize packet.1.1.1 objects.base.objects.rng).1 kem
    (generation.realize packet.1.1.1 objects.base.objects.rng).2 packet.1.1.2 returned resultEq rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps.withCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps.withCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps.fresh
