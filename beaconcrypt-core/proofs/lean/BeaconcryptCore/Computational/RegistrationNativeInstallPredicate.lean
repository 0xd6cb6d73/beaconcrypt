-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCaps

/-! The installation classifier is the same actual capability on Common, local and routed Word interfaces. Query routing changes only KEM exposure tags and preserves every installation query exactly once. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallPredicate
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePublicFrontend (Spec liftLocal)
abbrev LocalSpec (n : Nat) (KemSK : Type) := RegistrationBeaconReferenceCompiler.Spec n KemSK
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

end BeaconcryptCore.Computational.RegistrationNativeInstallPredicate
