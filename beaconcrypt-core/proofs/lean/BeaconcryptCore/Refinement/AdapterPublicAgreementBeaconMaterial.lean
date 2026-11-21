-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! The existing full SDK/native Beacon material relation supplies the exact source RegistrationKeys views and generated indexed KEM row. The source owner is selected from its private stored objects, never from public-key equality. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial
open BeaconcryptCore.Computational
open AdapterPublicAgreementBeaconFrontend (PrivateKeys)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {KemSK : Type} {source : RegistrationNativeMldsa.Source}

def registrationKeys (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) :
    AdapterPublicAgreementFields.Keys :=
  ⟨self.identity_key.secret_key, .Some prekey.secret_key, .Some oneTime.secret_key, .Some kem.secret_key⟩

omit platform in
noncomputable def from_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (pending retained : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem) (native : owner.phase = .initSent retained scalar) :
    PrivateKeys view (registrationKeys self prekey oneTime kem) owner scalar := by
  have phase := related.phase
  unfold AdapterPublicWrapperState.Phase at phase
  rw [stored, native] at phase
  exact ⟨prekey.secret_key, oneTime.secret_key, kem.secret_key, related.identitySecret,
    rfl, phase.2.1.1, rfl, phase.2.2.1, rfl⟩

omit platform in
theorem indexed_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (pending retained : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem) (native : owner.phase = .initSent retained scalar) :
    pool.keys[owner.kemHandle]? = some (owner.kemPublic, view.kemSecret kem.secret_key) := by
  have phase := related.phase
  unfold AdapterPublicWrapperState.Phase at phase
  rw [stored, native] at phase
  exact phase.2.2.2.1.2
end BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial.from_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial.from_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial.indexed_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial.indexed_material
