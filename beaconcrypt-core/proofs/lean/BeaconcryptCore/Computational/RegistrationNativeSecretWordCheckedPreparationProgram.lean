-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation

/-! These equations insert the actual local query embeddings into the checked capability source laws. They retain the concrete optional checks and avoid replacing any callback by an assumed source interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordChecked (native implementation)
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK Reader E : Type}

private theorem old_embedding (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    native (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar) ∘ₛ
      RegistrationBeaconReferenceCompiler.prepare =
      RegistrationNativeSecretWordCheckedPreparation.original source inside candidate joint dh seed scalar := by
  funext message
  rfl

private theorem new_embedding (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    implementation (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar) ∘ₛ
      RegistrationNativeSecretWordInterface.prepare =
      RegistrationNativeSecretWordChecked.preparation candidate (input joint dh seed scalar) := by
  funext message
  simp only [QueryImpl.compose, RegistrationNativeSecretWordInterface.prepare,
    simulateQ_spec_query, implementation]

/-- The complete original Server prepare program restores from the evaluated opaque-word capability. -/
theorem server (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PeerEncoding) :
    simulateQ (native (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar))
      (simulateQ RegistrationBeaconReferenceCompiler.prepare
        (RegistrationServerReferenceRoot.client binding (RegistrationNativeSecretWordServerCollect.eval candidate collected))) =
      RegistrationNativeSecretWordServerRoot.restore candidate <$>
        simulateQ (implementation source inside candidate (input joint dh seed scalar))
          (simulateQ RegistrationNativeSecretWordInterface.prepare
            (RegistrationNativeSecretWordServerRoot.client binding collected)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, old_embedding, new_embedding]
  exact RegistrationNativeSecretWordCheckedPreparation.server source inside candidate joint dh seed scalar binding collected

/-- The actual arbitrary-pin Beacon prepare program restores without discarding any metadata or optional refusal. -/
theorem beacon (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse) :
    simulateQ (native (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar))
      (simulateQ RegistrationBeaconReferenceCompiler.prepare
        (RegistrationBeaconReferenceRoot.client authenticated (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending))) =
      RegistrationNativeSecretWordBeaconRoot.restore candidate <$>
        simulateQ (implementation source inside candidate (input joint dh seed scalar))
          (simulateQ RegistrationNativeSecretWordInterface.prepare
            (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, old_embedding, new_embedding]
  exact RegistrationNativeSecretWordCheckedPreparation.beacon source inside candidate joint dh seed scalar authenticated pending

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram.beacon
