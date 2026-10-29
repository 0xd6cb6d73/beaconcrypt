-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial

/-! Ordinary-owner local DH translation affects only root preparation. Its already returned supplied reference enters the same concrete first-open/material service. The full material source equation therefore preserves the actual owner, application, environment, World effects and all terminal failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryMaterial
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (input BeaconReady)
open RegistrationNativeSecretWordCheckedOrdinary (original symbolic)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

/-- Ordinary root materialization forwards the entire already-prepared material service without changing any returned reference. -/
theorem paired (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    (original (n := n) setup localScalar inside candidate seed scalar ∘ₛ RegistrationBeaconReferenceFinish.service) ∘ₛ
      RegistrationNativeSecretWordServerMaterial.realize candidate =
      symbolic setup localScalar inside candidate seed scalar ∘ₛ RegistrationNativeSecretWordInterface.paired := by
  funext query
  cases query with
  | inl message =>
      simp only [QueryImpl.compose, RegistrationNativeSecretWordServerMaterial.realize,
        simulateQ_spec_query, RegistrationBeaconReferenceFinish.service, original, symbolic,
        RegistrationNativePublicOwners.ordinary, RegistrationNativeSecretWordOwners.ordinary,
        RegistrationNativeSecretWordChecked.native, RegistrationNativeSecretWordServerSource.realize,
        simulateQ_spec_query, RegistrationNativeSecretWordInterface.demand, RegistrationNativeSecretWordInterface.paired,
        RegistrationNativeSecretWordChecked.implementation]
      exact RegistrationNativeSecretWordCheckedInput.material_literal_eval setup.source inside setup.joint setup.dh seed scalar candidate message
  | inr query => rfl

/-- The actual ordinary Beacon material continuation preserves its full owner/environment poststate on every first-open, admission or installation outcome. -/
theorem complete (setup : Setup base KemSK) (localScalar : ScalarBytes)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (hkdf : FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner before : SelectedOwner mlSource)
    (ready : BeaconReady) (env : EnvState Auxiliary) :
    simulateQ (original (n := n) setup localScalar inside candidate seed scalar)
      (((RegistrationBeaconReferenceFinish.complete hkdf owner (ready.eval candidate)).run before).run env) =
      simulateQ (symbolic setup localScalar inside candidate seed scalar)
        (((RegistrationNativeSecretWordBeaconCompiler.complete hkdf owner ready).run before).run env) := by
  rw [← RegistrationNativeSecretWordBeaconMaterial.complete_source candidate hkdf owner before ready env,
    QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    paired, QueryImpl.simulateQ_compose]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryMaterial.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryMaterial.paired
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryMaterial.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryMaterial.complete
