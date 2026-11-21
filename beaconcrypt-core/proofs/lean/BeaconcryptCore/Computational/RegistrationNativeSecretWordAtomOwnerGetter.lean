-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCollector
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom

/-! A Beacon atom is returned by the same retained owner's indexed private handle. The ordinary-owner translator affects only root preparation, so both selected and ordinary incoming collectors use this exact decapsulation request and reached provider pool. No owner-index or protected-root identification is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open RegistrationNativeSecretWordInterface (LocalSpec liftLocal localKem)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def withScalar (setup : Setup base KemSK)
    (implementation : QueryImpl (LocalSpec n KemSK) (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (LocalSpec n KemSK) (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp) :=
  match scalar with
  | none => implementation
  | some scalar => implementation ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup scalar

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer false

/-- The actual private source returns an atom only for the selected current handle and the exact early challenge ciphertext. -/
theorem getter_word (handle : Nat) (ciphertext : MlKem768Ciphertext)
    (before after : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : (some Word.atom, after) ∈ support
      ((implementation (.inl (.inr (.inr (.inr (.inl (.decapsulate handle ciphertext))))))).run before)) :
    handle = selected ∧ ciphertext = challenge ∧ ∃ pair, before.kem.1.keys[handle]? = some pair := by
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
  obtain ⟨answer, reached, returned⟩ := native
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
  have reply : answer.1 = some Word.atom := congrArg Prod.fst returned
  have called : (some Word.atom, answer.2) ∈ support ((provider (.inr (.inl (.decapsulate handle ciphertext)))).run before.kem) := by
    convert actual using 1
    exact Prod.ext reply.symm rfl
  exact RegistrationNativeSecretWordKemEarlyAtom.decapsulate setup.baseImpl setup.kem selected pairs publicKey
    challenge ciphertext handle before.kem answer.2 called

private theorem pure_apply {State Value : Type} {m : Type → Type} [Monad m] (value : Value) (before : State) :
    (pure value : StateT State m Value) before = pure (value, before) := rfl

private theorem map_apply {State Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT State m Value) (before : State) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem getter_run (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (before : Auxiliary n KemSK) :
    (lower (withScalar setup localImplementation scalar)
      (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated (.decapsulate ciphertext ()))).run before =
      (fun result => (result.1, ({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.decapsulate (.Some ciphertext)) }, result.2))) <$>
        (implementation (.inl (.inr (.inr (.inr (.inl (.decapsulate owner.kemHandle
          (PqxdhPhase2InputBytes.ciphertext ciphertext)))))))).run before.2 := by
  rw [RegistrationNativeSecretWordTargetServerExecution.lower_run]
  cases scalar <;>
    simp only [RegistrationNativeSecretWordBeaconCompiler.prefixImpl, StateT.run, simulateQ_map, map_apply,
      withScalar, localImpl, QueryImpl.compose, localKem, simulateQ_spec_query,
      RegistrationNativeSecretWordOwners.ordinary, liftLocal, RegistrationNativeSecretWordInterface.route,
      RegistrationNativeSecretWordInterface.routedKem, Functor.map_map, Prod.map_def, id_eq]
  all_goals rfl

/-- The actual lowered optional getter retains the same owner's operand and current private-pool witness on both owner paths. -/
theorem getter_atom (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (before after : Auxiliary n KemSK)
    (supported : (some Word.atom, after) ∈ support
      ((lower (withScalar setup localImplementation scalar)
        (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated (.decapsulate ciphertext ()))).run before)) :
    owner.kemHandle = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge ∧
      ∃ pair, before.2.kem.1.keys[owner.kemHandle]? = some pair := by
  rw [getter_run] at supported
  rw [support_map] at supported
  obtain ⟨result, called, returned⟩ := supported
  rcases result with ⟨replyValue, last⟩
  have reply : replyValue = some Word.atom := congrArg Prod.fst returned
  subst replyValue
  exact getter_word setup wire route sign input inside selected pairs publicKey challenge outer
    owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext) before.2 last called

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter.getter_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter.getter_word
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter.getter_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerGetter.getter_atom
