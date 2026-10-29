-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput

/-! Concrete checked preparation restores both actual root capabilities after mathematical word evaluation. The proof uses the real optional DH check and successful echo, rather than an inverse assumption on arbitrary returned descriptor names. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation
open RegistrationNativeSecretWordMessage (Message input eval literal)
open RegistrationNativeSecretWordChecked (Spec preparation native)
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK Reader E : Type}

def original (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl RegistrationServerReferenceRoot.PrepareSpec (OracleComp (Spec n KemSK)) :=
  fun message => simulateQ (native source inside candidate (input joint dh seed scalar))
    (RegistrationBeaconReferenceCompiler.prepare message)

/-- Evaluating a queried descriptor preserves the actual optional check and returns the original symbolic name on success. -/
theorem annotation (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    original (n := n) (KemSK := KemSK) source inside candidate joint dh seed scalar ∘ₛ
      RegistrationNativeSecretWordServerRoot.annotation candidate =
      preparation candidate (input joint dh seed scalar) := by
  funext message
  simp only [QueryImpl.compose, RegistrationNativeSecretWordServerRoot.annotation,
    simulateQ_map, simulateQ_spec_query, original, RegistrationBeaconReferenceCompiler.prepare,
    native, QueryImpl.compose, simulateQ_spec_query, RegistrationNativeSecretWordServerSource.realize,
    RegistrationNativeSecretWordInterface.prepare, RegistrationNativeSecretWordChecked.implementation,
    preparation, RegistrationNativeSecretWordMessage.eval_literal,
    simulateQ_map, simulateQ_spec_query, map_bind, map_pure]
  congr 1
  funext _
  have same := RegistrationNativeSecretWordCheckedInput.valid_literal_eval joint dh seed scalar candidate message
  cases left : input joint dh seed scalar (literal (eval candidate message)) <;>
    cases right : input joint dh seed scalar message <;> simp_all

private theorem echo (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    original (n := n) (KemSK := KemSK) source inside candidate joint dh seed scalar ∘ₛ
      RegistrationNativeSecretWordServerRoot.nativeEcho =
      original source inside candidate joint dh seed scalar := by
  funext message
  simp only [QueryImpl.compose, RegistrationNativeSecretWordServerRoot.nativeEcho,
    simulateQ_map, simulateQ_spec_query, original, RegistrationBeaconReferenceCompiler.prepare,
    native, QueryImpl.compose, simulateQ_spec_query, RegistrationNativeSecretWordServerSource.realize,
    RegistrationNativeSecretWordInterface.prepare, RegistrationNativeSecretWordChecked.implementation,
    preparation, RegistrationNativeSecretWordMessage.eval_literal,
    simulateQ_map, simulateQ_spec_query, map_bind, map_pure]
  congr 1
  funext _
  cases input joint dh seed scalar (literal message) <;> rfl

/-- The complete actual Server capability is restored by the concrete checked optional input, including local refusal. -/
theorem server (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PeerEncoding) :
    simulateQ (original (n := n) (KemSK := KemSK) source inside candidate joint dh seed scalar)
      (RegistrationServerReferenceRoot.client binding (RegistrationNativeSecretWordServerCollect.eval candidate collected)) =
      RegistrationNativeSecretWordServerRoot.restore candidate <$>
        simulateQ (preparation candidate (input joint dh seed scalar))
          (RegistrationNativeSecretWordServerRoot.client binding collected) := by
  have result := congrArg
    (simulateQ (original (n := n) (KemSK := KemSK) source inside candidate joint dh seed scalar))
    (RegistrationNativeSecretWordServerRoot.client_source candidate binding collected)
  simp only [simulateQ_map, ← QueryImpl.simulateQ_compose, annotation, echo] at result
  exact result.symm

/-- The complete arbitrary-pin Beacon capability is restored without equating its configured pin to the protected Server identity. -/
theorem beacon (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse) :
    simulateQ (original (n := n) (KemSK := KemSK) source inside candidate joint dh seed scalar)
      (RegistrationBeaconReferenceRoot.client authenticated (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending)) =
      RegistrationNativeSecretWordBeaconRoot.restore candidate <$>
        simulateQ (preparation candidate (input joint dh seed scalar))
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending) := by
  have result := congrArg
    (simulateQ (original (n := n) (KemSK := KemSK) source inside candidate joint dh seed scalar))
    (RegistrationNativeSecretWordBeaconRoot.client_source candidate authenticated pending)
  have annotated : RegistrationNativeSecretWordBeaconRoot.annotation candidate =
      RegistrationNativeSecretWordServerRoot.annotation candidate := rfl
  have echoed : RegistrationNativeSecretWordBeaconRoot.nativeEcho =
      RegistrationNativeSecretWordServerRoot.nativeEcho := rfl
  simp only [simulateQ_map, annotated, echoed, ← QueryImpl.simulateQ_compose, annotation, echo] at result
  exact result.symm

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation.annotation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation.annotation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation.beacon
