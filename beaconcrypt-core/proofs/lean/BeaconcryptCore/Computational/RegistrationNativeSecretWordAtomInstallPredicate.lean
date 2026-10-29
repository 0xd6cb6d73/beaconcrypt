-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps

/-! The installation classifier is the same actual capability on Common, local and routed Word interfaces. Query routing changes only KEM exposure tags and preserves every installation query exactly once. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallPredicate
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordInterface (LocalSpec Spec liftLocal)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
variable {n : Nat} {KemSK Value : Type}

def LocalInstall (role : Role) : (LocalSpec n KemSK).Domain → Prop
  | .inr (.inl (.inr query)) => Install role query
  | _ => False
instance (role : Role) : DecidablePred (LocalInstall (n := n) (KemSK := KemSK) role) := fun query => by
  rcases query with message | (message | common) | kem
  · exact isFalse id
  · exact isFalse id
  · exact inferInstanceAs (Decidable (Install role common))
  · exact isFalse id

def GlobalInstall (role : Role) : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inr query))) => Install role query
  | _ => False
instance (role : Role) : DecidablePred (GlobalInstall (n := n) (KemSK := KemSK) role) := fun query => by
  rcases query with (message | (message | common) | kem) | record
  · exact isFalse id
  · exact isFalse id
  · exact inferInstanceAs (Decidable (Install role common))
  · exact isFalse id
  · exact isFalse id

/-- Actual local routing preserves each role's installation bill without introducing any additional installation. -/
theorem local_bound (role : Role) (selected : Bool) (work : OracleComp (LocalSpec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (LocalInstall (KemSK := KemSK) role) cap) :
    (simulateQ (liftLocal selected) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  rcases query with message | (message | common) | kem
  · simp [liftLocal, GlobalInstall, LocalInstall, isQueryBoundP_query_iff]
  · simp [liftLocal, GlobalInstall, LocalInstall, isQueryBoundP_query_iff]
  · simp [liftLocal, GlobalInstall, LocalInstall, isQueryBoundP_query_iff]
    intro counted
    rw [ite_eq_left counted]
    decide
  · rcases kem with other | (pool | key)
    · simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
        GlobalInstall, LocalInstall, isQueryBoundP_query_iff]
    · simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
        GlobalInstall, LocalInstall, isQueryBoundP_query_iff]
    · cases selected <;> simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
        GlobalInstall, LocalInstall, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallPredicate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallPredicate.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallPredicate.local_bound
