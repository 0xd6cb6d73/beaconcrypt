-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial
/-! Source finish terminal material is related after actual private-pool history changes, without requiring the endpoint phase relation during the transient early-Aborted state. Immutable private credential fields are derived from the original relation and all terminal source fields are literal Core completion/rejection values. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicFinishMaterial
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Owner)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {KemSK : Type} {source : RegistrationNativeMldsa.Source}

omit platform in
theorem installed (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (originalPool finalPool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view joint originalPool self owner world)
    (completed : registration.CompletedBeacon) :
    AdapterPublicWrapperState.Beacon view joint finalPool
      {self with
        identity_key_kid := completed.binding.assigned_key_id
        state := .Established completed.control completed.binding ⟨⟨some completed.kernel⟩⟩}
      {owner with phase := .established ⟨completed.control, completed.binding, completed.application⟩}
      (some (.established ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ completed.kernel)) := by
  exact ⟨related.identityPublic, related.identitySecret, related.pin, related.serverPublic,
    rfl, rfl, rfl, completed.kernel, rfl, rfl⟩

omit platform in
theorem aborted (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (originalPool finalPool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view joint originalPool self owner world)
    (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes)
    (initial : owner.phase = .initSent pending scalar) (control : pqxdh.BeaconAborted) :
    AdapterPublicWrapperState.Beacon view joint finalPool {self with state := .Aborted control}
      {owner with phase := .aborted control} (some (.inactive .aborted)) := by
  refine ⟨related.identityPublic, related.identitySecret, related.pin, related.serverPublic, ?_, rfl, rfl⟩
  simpa only [AdapterPublicWrapperState.currentId, initial] using related.identifier

omit platform in
noncomputable def early_private (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (pending retained : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem) (native : owner.phase = .initSent retained scalar)
    (control : pqxdh.BeaconAborted) :
    AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys {self with state := .Aborted control} prekey oneTime kem)
      {owner with phase := .aborted control} scalar :=
by
  let previous := AdapterPublicAgreementBeaconMaterial.from_material view joint pool self owner world related pending retained prekey oneTime kem scalar stored native
  exact ⟨previous.prekey, previous.oneTimeKey, previous.kem, previous.identity, previous.prekeyStored, previous.prekeyView, previous.oneTimeStored, previous.oneTimeView, previous.kemStored⟩

end BeaconcryptCore.Refinement.AdapterPublicFinishMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishMaterial.installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishMaterial.installed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishMaterial.aborted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishMaterial.aborted

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishMaterial.early_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishMaterial.early_private
