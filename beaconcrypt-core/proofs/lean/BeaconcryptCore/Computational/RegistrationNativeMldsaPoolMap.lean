-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaOpaque

/-! Live native credentials restore through their actual private rows. Appending a generated row preserves every already-live owner and its complete native-state restoration. Signing receipts change no row, so their restoration is literal. These are dynamic table facts, independent of key injectivity or a whole-profile correspondence assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource Pool Live birth restore record)
variable {n : Nat} {KemSK : Type} (source : Source)

def CredentialLive (before : Pool source) (credential : Credential (handleSource source)) : Prop :=
  ∃ key, Live source before credential key

def OwnersLive (before : Pool source) (current : RegistrationNativeBeaconFrontend.State (handleSource source)) : Prop :=
  ∀ owner ∈ current, CredentialLive source before owner.mldsa

def StateLive (before : Pool source) (current : RegistrationNativeExperiment.State n KemSK (handleSource source)) : Prop :=
  OwnersLive source before current.beacons

theorem owners_empty (before : Pool source) : OwnersLive source before [] := by
  intro current absent
  cases absent

theorem owners_append (before : Pool source) (current : RegistrationNativeBeaconFrontend.State (handleSource source))
    (added : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (old : OwnersLive source before current) (fresh : CredentialLive source before added.mldsa) :
    OwnersLive source before (current ++ [added]) := by
  intro selected member
  rcases List.mem_append.mp member with earlier | last
  · exact old selected earlier
  · have same : selected = added := List.mem_singleton.mp last
    exact same ▸ fresh

theorem birth_owners (before : Pool source) (generated : Option (Credential source) × Nat)
    (current : RegistrationNativeBeaconFrontend.State (handleSource source)) (live : OwnersLive source before current) :
    OwnersLive source (birth source before generated).2 current := by
  intro selected member
  obtain ⟨key, row⟩ := live selected member
  exact ⟨key, RegistrationNativeMldsaOpaque.birth_preserves source before generated selected.mldsa key row⟩

theorem record_owners (before : Pool source) (credential : Credential (handleSource source))
    (request : beaconcrypt_core.registration.MldsaSigningRequest) (reply : RegistrationSigningShared.SignReply)
    (current : RegistrationNativeBeaconFrontend.State (handleSource source)) (live : OwnersLive source before current) :
    OwnersLive source (record source before credential request reply) current := live

theorem record_restore (fallback : Credential source) (before : Pool source) (credential : Credential (handleSource source))
    (request : beaconcrypt_core.registration.MldsaSigningRequest) (reply : RegistrationSigningShared.SignReply) :
    restore source fallback (record source before credential request reply) = restore source fallback before := rfl

theorem birth_credential_restore (fallback : Credential source) (before : Pool source)
    (generated : Option (Credential source) × Nat) (credential : Credential (handleSource source))
    (live : CredentialLive source before credential) :
    RegistrationNativeMldsaMap.credential (restore source fallback (birth source before generated).2) credential =
      RegistrationNativeMldsaMap.credential (restore source fallback before) credential := by
  obtain ⟨key, row⟩ := live
  rw [RegistrationNativeMldsaOpaque.restore_live source fallback _ credential key
    (RegistrationNativeMldsaOpaque.birth_preserves source before generated credential key row),
    RegistrationNativeMldsaOpaque.restore_live source fallback before credential key row]

theorem birth_owner_restore (fallback : Credential source) (before : Pool source)
    (generated : Option (Credential source) × Nat) (current : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (live : CredentialLive source before current.mldsa) :
    RegistrationNativeMldsaMap.owner (restore source fallback (birth source before generated).2) current =
      RegistrationNativeMldsaMap.owner (restore source fallback before) current := by
  have same := birth_credential_restore source fallback before generated current.mldsa live
  simp only [RegistrationNativeMldsaMap.owner]
  rw [same]

theorem birth_owners_restore (fallback : Credential source) (before : Pool source)
    (generated : Option (Credential source) × Nat) (current : RegistrationNativeBeaconFrontend.State (handleSource source))
    (live : OwnersLive source before current) :
    RegistrationNativeMldsaMap.owners (restore source fallback (birth source before generated).2) current =
      RegistrationNativeMldsaMap.owners (restore source fallback before) current :=
  List.map_congr_left fun selected member => birth_owner_restore source fallback before generated selected (live selected member)

theorem birth_state_restore (fallback : Credential source) (before : Pool source)
    (generated : Option (Credential source) × Nat) (current : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (live : StateLive source before current) :
    RegistrationNativeMldsaMap.nativeState (restore source fallback (birth source before generated).2) current =
      RegistrationNativeMldsaMap.nativeState (restore source fallback before) current := by
  simp only [RegistrationNativeMldsaMap.nativeState, birth_owners_restore source fallback before generated current.beacons live]

end BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.owners_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.owners_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.owners_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.owners_append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_owners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.record_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.record_owners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.record_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.record_restore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_credential_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_credential_restore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_owner_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_owner_restore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_owners_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_owners_restore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_state_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap.birth_state_restore
