-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect

/-! Successful decapsulation of the original selected challenge in the actual lowered Beacon callback returns the atom, with no phase or live-pool premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAtom
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl lower_run)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual Beacon callback consumes the selected current handle and the same challenge ciphertext, so its successful reply is the atom. -/
theorem getter (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : Auxiliary n KemSK) (word : Word)
    (handle : owner.kemHandle = selected)
    (supported : (some word, after) ∈ support
      ((RegistrationNativeSecretWordTargetOwnerCollect.compiler setup wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge) outer
        owner oneTime authenticated (.decapsulate (PqxdhAcceptedRegistration.ciphertextArray challenge) ())).run before)) : word = Word.atom := by
  simp only [RegistrationNativeSecretWordTargetOwnerCollect.compiler] at supported
  rw [lower_run] at supported
  simp only [RegistrationNativeSecretWordBeaconCompiler.prefixImpl, StateT.run, simulateQ_map,
    RegistrationNativeSecretWordInterface.localKem, simulateQ_spec_query, state_map_apply, Functor.map_map, support_map] at supported
  obtain ⟨⟨reply, privateState⟩, called, equal⟩ := supported
  have sameReply : reply = some word := congrArg Prod.fst equal
  apply RegistrationNativeSecretWordTargetOwnerGetter.getter_selected setup wire route sign input inside selected pairs publicKey challenge
    outer before.2 privateState word
  rw [sameReply] at called
  simp only [localImpl, QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal,
    RegistrationNativeSecretWordInterface.routedKem, RegistrationNativeSecretWordInterface.route,
    simulateQ_spec_query] at called
  rw [handle, (PqxdhPhase2InputBytes.ciphertext_roundtrip (PqxdhAcceptedRegistration.ciphertextArray challenge) challenge).2] at called
  exact called
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAtom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAtom.getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAtom.getter
