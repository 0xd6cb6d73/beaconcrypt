-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle
open RegistrationNativePlatformExtractedSdkAdaptive (Step pack)
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
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
variable (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp) RegistrationSigningShared.SignReply)
variable (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

def bytes {R : Type} (reply : RustM (core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R)) : RustM (Option Pqxdh.Bytes) :=
  match reply with
  | .fail error=>.fail error
  | .div=>.div
  | .ok (optional,_,_)=>.ok (match optional with | .None=>none | .Some value=>some (TranscriptAuthParts.absSlice value))
omit platform localOps crypto in
theorem bytes_public {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R)
    (published : Publication) :
    bytes (AdapterPublicBundlePublication.install self prekey oneTime kem rng published)=
      RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value published) := by
  cases published with
  | fail error | div=>rfl
  | ok result=>cases result <;> rfl

noncomputable def withCoins {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves coins setup checks representation created writer index owner failure fallback self)
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
      packet∈support (withCoinsRunner coins setup checks representation created writer index owner scalar before.1 previous) →
      AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey oneTime kem scalar packet.1.1 packet.1.2 →
      ∀returned,AdapterPublicBundlePublication.install self prekey oneTime kem rng packet.1.1=.ok returned →
        bytes (.ok returned)=(pack (withCoinsNative index owner scalar packet)).1 →
        Private (pack (withCoinsNative index owner scalar packet)).2) :
    Step Private (pack <$> ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source writer index).run before.1).run previous) := by
  let : ChildOperations (RustT CutM) := AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
  have complete := RegistrationNativePlatformExtractedSdkBundle.with_coins_complete coins setup checks representation created writer index owner failure fallback other recording
    self view getters law control scalar prekey oneTime kem generator rng stored phase publicView before previous related selected
  refine {
    Packet := (Publication ×Native) ×Platform
    sample := withCoinsRunner coins setup checks representation created writer index owner scalar before.1 previous
    sourceType := core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R
    sourceReply := fun packet=>AdapterPublicBundlePublication.install self prekey oneTime kem rng packet.1.1
    sourceState := fun packet=>(packet.1.2,packet.2)
    sourceCall := (fun result=>(result.1.1,(result.1.2.1,result.2))) <$>
      ((((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m:=RustT CutM) generator self rng).run).run before).run previous)
    source_exact := ?_
    native := fun packet=>pack (withCoinsNative index owner scalar packet)
    native_exact := ?_
    store := ?_ }
  · have projected:=congrArg (fun action=>pack <$> action) complete.1
    simpa only [Functor.map_map,Prod.map,id_eq,pack] using projected.symm
  · have projected:=congrArg (fun action=>pack <$> action) complete.2.1
    simpa only [Functor.map_map,withCoinsNative,pack] using projected.symm
  · intro packet supported
    have materialResult:=complete.2.2 packet supported
    cases resultEq : AdapterPublicBundlePublication.install self prekey oneTime kem rng packet.1.1 with
    | fail error=>exact PUnit.unit
    | div=>exact PUnit.unit
    | ok returned=>
        have publicReply:=bytes_public self prekey oneTime kem rng packet.1.1
        rw [resultEq] at publicReply
        exact put packet supported materialResult returned resultEq publicReply

noncomputable def fresh {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (law : AdapterPublicBundleSourceExecution.Leaves coins setup checks representation created writer index owner failure fallback self)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformCutErasure.liftWorld (AdapterPublicBundleSourceExecution.sample (n := n) (source := source) coins setup checks representation created writer)))
    (stored : self.state = .Fresh control prekey kem) (phase : owner.phase = .fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner before.1.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.1.beacons[index]? = some owner)
    (Private : (Native ×Platform) →Type)
    (put : ∀(packet : ((PqxdhJointGapDh.ScalarBytes ×Publication) ×Native) ×Platform),
      packet∈support (freshRunner coins setup checks representation created writer index owner before.1 previous) →
      AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey (generation.realize packet.1.1.1 rng).1 kem packet.1.1.1 packet.1.1.2 packet.1.2 →
      ∀returned,AdapterPublicBundlePublication.install self prekey (generation.realize packet.1.1.1 rng).1 kem (generation.realize packet.1.1.1 rng).2 packet.1.1.2=.ok returned →
        bytes (.ok returned)=(pack (freshNative index owner packet)).1 →
        Private (pack (freshNative index owner packet)).2) :
    Step Private (pack <$> ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source writer index).run before.1).run previous) := by
  let : ChildOperations (RustT CutM) := AdapterPublicBundleSourceExecution.children coins setup checks representation created writer index owner other recording
  have complete := RegistrationNativePlatformExtractedSdkBundle.fresh_complete coins setup checks representation created writer index owner failure fallback other recording
    self view getters law control prekey kem generator rng generation stored phase before previous related selected
  refine {
    Packet := ((PqxdhJointGapDh.ScalarBytes ×Publication) ×Native) ×Platform
    sample := freshRunner coins setup checks representation created writer index owner before.1 previous
    sourceType := core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R
    sourceReply := fun packet=>AdapterPublicBundlePublication.install self prekey (generation.realize packet.1.1.1 rng).1 kem (generation.realize packet.1.1.1 rng).2 packet.1.1.2
    sourceState := fun packet=>(packet.1.2,packet.2)
    sourceCall := (fun result=>(result.1.1,(result.1.2.1,result.2))) <$>
      ((((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m:=RustT CutM) generator self rng).run).run before).run previous)
    source_exact := ?_
    native := fun packet=>pack (freshNative index owner packet)
    native_exact := ?_
    store := ?_ }
  · have projected:=congrArg (fun action=>pack <$> action) complete.1
    simpa only [Functor.map_map,Prod.map,id_eq,pack] using projected.symm
  · have projected:=congrArg (fun action=>pack <$> action) complete.2.1
    simpa only [Functor.map_map,freshNative,pack] using projected.symm
  · intro packet supported
    have materialResult:=complete.2.2 packet supported
    cases resultEq : AdapterPublicBundlePublication.install self prekey (generation.realize packet.1.1.1 rng).1 kem (generation.realize packet.1.1.1 rng).2 packet.1.1.2 with
    | fail error=>exact PUnit.unit
    | div=>exact PUnit.unit
    | ok returned=>
        have publicReply:=bytes_public self prekey (generation.realize packet.1.1.1 rng).1 kem (generation.realize packet.1.1.1 rng).2 packet.1.1.2
        rw [resultEq] at publicReply
        exact put packet supported materialResult returned resultEq publicReply

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle.withCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle.withCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle.bytes_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle.bytes_public
