-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial

/-! Checked Beacon completion restores the entire native consumed kernel, owner phase, application reply and current environment. Only its private prepared descriptor is evaluated; native record opening, World insertion and failure callbacks remain actual. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial
open RegistrationNativeSecretWordMessage (input BeaconReady)
open RegistrationNativeSecretWordChecked (native implementation)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK Auxiliary : Type}

/-- Every actual paired callback agrees after evaluating the sole material address. -/
theorem paired (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    (native (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar) ∘ₛ
      RegistrationBeaconReferenceFinish.service) ∘ₛ RegistrationNativeSecretWordServerMaterial.realize candidate =
      implementation source inside candidate (input joint dh seed scalar) ∘ₛ RegistrationNativeSecretWordInterface.paired := by
  funext query
  cases query with
  | inl message =>
      simp only [QueryImpl.compose, RegistrationNativeSecretWordServerMaterial.realize,
        simulateQ_spec_query, RegistrationBeaconReferenceFinish.service, native,
        RegistrationNativeSecretWordServerSource.realize, simulateQ_spec_query,
        RegistrationNativeSecretWordInterface.demand, RegistrationNativeSecretWordInterface.paired,
        implementation]
      exact RegistrationNativeSecretWordCheckedInput.material_literal_eval source inside joint dh seed scalar candidate message
  | inr query => rfl

/-- The complete actual native Beacon material continuation keeps its full owner/environment poststate on every failure and success. -/
theorem complete (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (hkdf : FixedHkdfSha512NoSaltSource) {mlSource : RegistrationNativeMldsa.Source}
    (owner before : SelectedOwner mlSource) (ready : BeaconReady) (env : EnvState Auxiliary) :
    simulateQ (native (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar))
      (((RegistrationBeaconReferenceFinish.complete hkdf owner (ready.eval candidate)).run before).run env) =
      simulateQ (implementation source inside candidate (input joint dh seed scalar))
        (((RegistrationNativeSecretWordBeaconCompiler.complete hkdf owner ready).run before).run env) := by
  rw [← RegistrationNativeSecretWordBeaconMaterial.complete_source candidate hkdf owner before ready env,
    QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose, paired, QueryImpl.simulateQ_compose]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial.paired
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial.complete
