-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Refinement.AdapterPublicBundlePublication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Platform R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

def OtkPublic (publicKey : PqxdhJointGapDh.ScalarBytes→Std.Array U8 32#usize)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (beacons : Nat→Option beaconcrypt_public_wrapper.beacon.Beacon) : Prop :=
  ∀index self control prekey oneTime kem,beacons index=some self →
    self.state=.FreshWithCoins control prekey oneTime kem →
    view.kxPublic oneTime.public_key=publicKey (view.kxSecret oneTime.secret_key)

structure StrongCarrier (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×Platform) where
  base : Carrier (R:=R) view views setup.joint created credential current
  otkPublic : OtkPublic (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view base.objects.beacons

variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)

noncomputable def empty (current : Native×Platform) (objects : Carrier (R:=R) view views setup.joint created credential current)
    (missing : current.1.beacons=[]) : StrongCarrier (R:=R) setup view views created credential current := by
  refine ⟨objects,?_⟩
  intro index self control prekey oneTime kem selected _stored
  have absent:=objects.beacons index
  simp only [missing,List.getElem?_nil] at absent
  rw [absent] at selected
  cases selected

noncomputable def frame (current after : Native×Platform)
    (before : StrongCarrier (R:=R) setup view views created credential current)
    (objects : Carrier (R:=R) view views setup.joint created credential after)
    (same : objects.objects.beacons=before.base.objects.beacons) : StrongCarrier (R:=R) setup view views created credential after :=
  ⟨objects,by rw [same]; exact before.otkPublic⟩

theorem one_time_public (current : Native×Platform)
    (before : StrongCarrier (R:=R) setup view views created credential current)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconFresh) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : before.base.objects.beacons index=some self)
    (stored : self.state=.FreshWithCoins control prekey oneTime kem)
    (secret : view.kxSecret oneTime.secret_key=scalar) :
    view.kxPublic oneTime.public_key=PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar) := by
  exact (before.otkPublic index self control prekey oneTime kem selected stored).trans
    (congrArg (fun value=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey value)) secret)

omit platform in
theorem update_public
    (publicKey : PqxdhJointGapDh.ScalarBytes→Std.Array U8 32#usize)
    (beacons : Nat→Option beaconcrypt_public_wrapper.beacon.Beacon)
    (prior : OtkPublic publicKey view beacons) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (selfPublic : ∀control prekey oneTime kem,self.state=.FreshWithCoins control prekey oneTime kem→
      view.kxPublic oneTime.public_key=publicKey (view.kxSecret oneTime.secret_key)) :
    OtkPublic publicKey view (Function.update beacons index (some self)) := by
  intro position current control prekey oneTime kem selected stored
  by_cases same:position=index
  · subst position
    simp only [Function.update_self,Option.some.injEq] at selected
    cases selected
    exact selfPublic control prekey oneTime kem stored
  · rw [Function.update_of_ne same] at selected
    exact prior position current control prekey oneTime kem selected stored

omit platform in
theorem publication_public (publicKey : PqxdhJointGapDh.ScalarBytes→Std.Array U8 32#usize)
    (beacons : Nat→Option beaconcrypt_public_wrapper.beacon.Beacon)
    (prior : OtkPublic publicKey view beacons) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (selected : beacons index=some self)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (rng : R) (publication : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)))
    (returned : core.option.Option (alloc.vec.Vec U8)×beaconcrypt_public_wrapper.beacon.Beacon×R)
    (actual : AdapterPublicBundlePublication.install self prekey oneTime kem rng publication=.ok returned) :
    OtkPublic publicKey view (Function.update beacons index (some returned.2.1)) := by
  apply update_public view publicKey beacons prior index returned.2.1
  cases publication with
  | fail error | div=>cases actual
  | ok publication=>cases publication with
    | Err previous=>
      cases actual
      exact fun control before ot keys stored=>prior index self control before ot keys selected stored
    | Ok finished=>
      cases actual
      intro control before ot keys stored
      cases stored

noncomputable def publication (current after : Native×Platform)
    (before : StrongCarrier (R:=R) setup view views created credential current)
    (objects : Carrier (R:=R) view views setup.joint created credential after)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (selected : before.base.objects.beacons index=some self)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (rng : R) (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)))
    (returned : core.option.Option (alloc.vec.Vec U8)×beaconcrypt_public_wrapper.beacon.Beacon×R)
    (actual : AdapterPublicBundlePublication.install self prekey oneTime kem rng published=.ok returned)
    (same : objects.objects.beacons=Function.update before.base.objects.beacons index (some returned.2.1)) :
    StrongCarrier (R:=R) setup view views created credential after := by
  refine ⟨objects,?_⟩
  rw [same]
  exact publication_public view _ before.base.objects.beacons before.otkPublic index self selected prekey oneTime kem rng published returned actual
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.one_time_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.one_time_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.update_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.update_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.publication_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.publication_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier.publication
