-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallPredicate

/-! Actual symbolic creation and outgoing bundles never install either record role. This follows from the concrete native coin/hash/append/advance callbacks and their literal open Word translation, rather than a probabilistic source projection or a reset of installation-trace metadata. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBirthInstallCaps
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeG3MaterializedOrdinary (TrustedInstall)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem step (role : Role) (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    ((RegistrationNativeSecretWordServerSource.realize RegistrationNativeSecretWordMessage.zero ∘ₛ
      RegistrationBeaconReferenceCompiler.trustedLift) query).IsQueryBoundP (LocalInstall (KemSK := KemSK) role)
      (if TrustedInstall (KemSK := KemSK) role query then 1 else 0) := by
  cases query with
  | inl effect =>
      cases effect with
      | inl coin =>
          simp [QueryImpl.compose, RegistrationBeaconReferenceCompiler.trustedLift,
            RegistrationBeaconReferenceCompiler.effect, RegistrationNativeSecretWordServerSource.realize,
            RegistrationNativeSecretWordInterface.common, LocalInstall, Install, InstallEnv, TrustedInstall, isQueryBoundP_query_iff]
      | inr capability => cases capability <;> cases role <;>
          simp [QueryImpl.compose, RegistrationBeaconReferenceCompiler.trustedLift,
            RegistrationBeaconReferenceCompiler.effect, RegistrationNativeSecretWordServerSource.realize,
            RegistrationNativeSecretWordInterface.common, LocalInstall, Install, InstallEnv, TrustedInstall, isQueryBoundP_query_iff]
  | inr kem =>
      rcases kem with other | (pool | key)
      · simp [QueryImpl.compose, RegistrationBeaconReferenceCompiler.trustedLift,
          RegistrationBeaconReferenceCompiler.indexed, RegistrationNativeSecretWordServerSource.realize,
          RegistrationNativeSecretWordInterface.localKem, LocalInstall, TrustedInstall, isQueryBoundP_query_iff]
      · cases pool <;>
          simp [QueryImpl.compose, RegistrationBeaconReferenceCompiler.trustedLift,
            RegistrationBeaconReferenceCompiler.indexed, RegistrationNativeSecretWordServerSource.realize,
            RegistrationNativeSecretWordInterface.localKem, LocalInstall, TrustedInstall,
            isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      · simp [QueryImpl.compose, RegistrationBeaconReferenceCompiler.trustedLift,
          RegistrationBeaconReferenceCompiler.indexed, RegistrationNativeSecretWordServerSource.realize,
          RegistrationNativeSecretWordInterface.localKem, LocalInstall, TrustedInstall,
          isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem execute_bound (role : Role) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP (TrustedInstall (KemSK := KemSK) role) 0)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordOwners.executeLocal selected publicPrekey work).run owners).run env).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordOwners.executeLocal, RegistrationNativePublicOwners.executeLocal,
    StateT.run, simulateQ_map, isQueryBoundP_map_iff]
  rw [← QueryImpl.simulateQ_compose]
  exact RawCtxSourceOpen.simulate_bound _ _ _ _ 0 (bounded _ _) (step role)

/-- Constructor failure paths, private birth and physical owner append contain no record installation of either role. -/
theorem create_free (role : Role) (setup : Setup base KemSK) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 :=
  execute_bound role selected publicPrekey _
    (RegistrationNativeG3MaterializedOrdinary.native_create_free role setup edPin mlPin keyId) owners env

/-- Actual symbolic outgoing publication retains every signing and failure branch and makes no record installation. -/
theorem bundle_free (role : Role) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 :=
  execute_bound role selected publicPrekey _
    (RegistrationNativeG3MaterializedOrdinary.native_bundle_free role setup wire index) owners env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBirthInstallCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBirthInstallCaps.create_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBirthInstallCaps.create_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBirthInstallCaps.bundle_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBirthInstallCaps.bundle_free
