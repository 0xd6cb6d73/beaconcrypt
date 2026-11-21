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

/-- Beacon owner restoration does not depend on any private ML row. -/
theorem birth_owner_restore (fallback : Credential source) (before : Pool source)
    (generated : Option (Credential source) × Nat) (current : RegistrationNativeBeaconFrontend.Owner (handleSource source)) :
    RegistrationNativeMldsaMap.owner (restore source fallback (birth source before generated).2) current =
      RegistrationNativeMldsaMap.owner (restore source fallback before) current := rfl

theorem birth_owners_restore (fallback : Credential source) (before : Pool source)
    (generated : Option (Credential source) × Nat) (current : RegistrationNativeBeaconFrontend.State (handleSource source)) :
    RegistrationNativeMldsaMap.owners (restore source fallback (birth source before generated).2) current =
      RegistrationNativeMldsaMap.owners (restore source fallback before) current := rfl

theorem birth_state_restore (fallback : Credential source) (before : Pool source)
    (generated : Option (Credential source) × Nat) (current : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
    RegistrationNativeMldsaMap.nativeState (restore source fallback (birth source before generated).2) current =
      RegistrationNativeMldsaMap.nativeState (restore source fallback before) current := rfl

end BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap

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
