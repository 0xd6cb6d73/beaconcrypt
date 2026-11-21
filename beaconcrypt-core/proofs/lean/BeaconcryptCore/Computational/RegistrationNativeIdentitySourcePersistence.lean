-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth

/-! A fresh actual indexed identity cannot retarget any earlier owned credential. The private realization of every existing public owner is stable under that generated append; no public-key injectivity or distinctness assumption is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence
open RegistrationNativeIdentityWorld (State)
open RegistrationNativeIdentitySourceBirth (born)
open RegistrationNativeIdentityRealization (seedFor owner owners Owned)
variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}

/-- Actual generated append retains each earlier credential's exact private source seed and public identity receipt. -/
theorem owns (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK)
    (value : PqxdhJointIdentity.IdentitySeed) (credential : RegistrationNativeIdentityInterface.Credential)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (owned : RegistrationNativeIdentityCallbacks.Owns joint before.identities credential seed) :
    RegistrationNativeIdentityCallbacks.Owns joint (born joint before value).identities credential seed := by
  refine ⟨?_, owned.2⟩
  simp only [born, PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp owned.1).1]
  exact owned.1

/-- The old credential reads the same private seed after a later generated birth. -/
theorem seed (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK)
    (value : PqxdhJointIdentity.IdentitySeed) (credential : RegistrationNativeIdentityInterface.Credential)
    (actual : PqxdhJointIdentity.IdentitySeed)
    (owned : RegistrationNativeIdentityCallbacks.Owns joint before.identities credential actual) :
    seedFor (born joint before value).identities credential = seedFor before.identities credential := by
  rw [RegistrationNativeIdentityRealization.seed_found _ _ actual (owns joint before value credential actual owned).1,
    RegistrationNativeIdentityRealization.seed_found _ _ actual owned.1]

/-- Private realization of every earlier source-owned public owner is unchanged by a fresh identity append. -/
theorem owners_unchanged (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK)
    (value : PqxdhJointIdentity.IdentitySeed) (current : RegistrationNativeIdentityFrontend.State source)
    (owned : Owned joint before.identities current) :
    owners (born joint before value).identities current = owners before.identities current := by
  apply List.map_congr_left
  intro selected member
  obtain ⟨actual, found⟩ := owned selected member
  change RegistrationNativeIdentityFrontend.restore (seedFor (born joint before value).identities selected.identity) selected =
    RegistrationNativeIdentityFrontend.restore (seedFor before.identities selected.identity) selected
  rw [seed joint before value selected.identity actual found]

/-- Every previously owned public credential remains source-owned after a fresh identity birth. -/
theorem owned_roster (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK)
    (value : PqxdhJointIdentity.IdentitySeed) (current : RegistrationNativeIdentityFrontend.State source)
    (owned : Owned joint before.identities current) : Owned joint (born joint before value).identities current := by
  intro selected member
  obtain ⟨actual, found⟩ := owned selected member
  exact ⟨actual, owns joint before value selected.identity actual found⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.owns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.owns
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.seed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.owners_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.owners_unchanged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.owned_roster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence.owned_roster
