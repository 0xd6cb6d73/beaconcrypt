-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary
import BeaconcryptCore.Computational.RegistrationNativePairedSafe

/-! Actual native public-owner creation and outgoing bundles never install either record role. The concrete trusted callback interpreter preserves the original zero-installation bill across source constructor, signing, hashing, append and failure branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedBirthPrefix
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeG3MaterializedOrdinary (TrustedInstall)
open RegistrationNativeSecretWordAtomOwnerInstallPrefix (NativeInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem step (role : Role) (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    ((RegistrationBeaconReferenceCompiler.trustedLift (n := n) (KemSK := KemSK)) query).IsQueryBoundP (NativeInstall (KemSK := KemSK) role)
      (if TrustedInstall (KemSK := KemSK) role query then 1 else 0) := by
  cases query with
  | inl effect =>
      cases effect with
      | inl coin =>
          simp [RegistrationBeaconReferenceCompiler.trustedLift,
            RegistrationBeaconReferenceCompiler.effect, NativeInstall, Install, InstallEnv, TrustedInstall, isQueryBoundP_query_iff]
      | inr capability => cases capability <;> cases role <;>
          simp [RegistrationBeaconReferenceCompiler.trustedLift,
            RegistrationBeaconReferenceCompiler.effect, NativeInstall, Install, InstallEnv, TrustedInstall, isQueryBoundP_query_iff]
  | inr kem =>
      rcases kem with other | (pool | key)
      · simp [RegistrationBeaconReferenceCompiler.trustedLift,
          RegistrationBeaconReferenceCompiler.indexed, NativeInstall, TrustedInstall, isQueryBoundP_query_iff]
      · cases pool <;>
          simp [RegistrationBeaconReferenceCompiler.trustedLift,
            RegistrationBeaconReferenceCompiler.indexed, NativeInstall, TrustedInstall,
            isQueryBoundP_query_iff]
      · simp [RegistrationBeaconReferenceCompiler.trustedLift,
          RegistrationBeaconReferenceCompiler.indexed, NativeInstall, TrustedInstall,
          isQueryBoundP_query_iff]

private theorem execute_bound (role : Role) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP (TrustedInstall (KemSK := KemSK) role) 0)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    (((RegistrationNativePublicOwners.executeLocal selected publicPrekey work).run owners).run env).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativePublicOwners.executeLocal, RegistrationNativePublicOwners.executeLocal,
    StateT.run, isQueryBoundP_map_iff]
  exact RawCtxSourceOpen.simulate_bound _ _ _ _ 0 (bounded _ _) (step role)

/-- Constructor failure paths, private birth and physical owner append contain no record installation of either role. -/
theorem create_free (role : Role) (setup : Setup base KemSK) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    (((RegistrationNativePublicOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 :=
  execute_bound role selected publicPrekey _
    (RegistrationNativeG3MaterializedOrdinary.native_create_free role setup edPin mlPin keyId) owners env

/-- Actual symbolic outgoing publication retains every signing and failure branch and makes no record installation. -/
theorem bundle_free (role : Role) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    (((RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env).IsQueryBoundP
      (NativeInstall (KemSK := KemSK) role) 0 :=
  execute_bound role selected publicPrekey _
    (RegistrationNativeG3MaterializedOrdinary.native_bundle_free role setup wire index) owners env

end BeaconcryptCore.Computational.RegistrationNativePairedBirthPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBirthPrefix.create_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBirthPrefix.create_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBirthPrefix.bundle_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBirthPrefix.bundle_free
