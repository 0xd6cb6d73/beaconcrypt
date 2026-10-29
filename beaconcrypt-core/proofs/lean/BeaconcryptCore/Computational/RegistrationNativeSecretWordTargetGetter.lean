-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication

/-! The matching first selected getter returns the same challenge ciphertext and opaque atom inside the actual lowered Server callback. The independent ignored32-byte draw, request log and complete reached environment/private state remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetGetter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal localKem)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem pq_key (key : MlKem768PublicKey) :
    RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray key) = key := by
  change RegistrationRootInput.pqKey (RegistrationNativeBeaconFrontend.pqArray key) = key
  exact RegistrationNativeBeaconPublication.pq_key key

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer true

/-- The actual selected source getter at its absent marker returns precisely this challenge ciphertext and atom. -/
theorem getter_word (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (initial : before.kem.2 = none)
    (result : (MlKem768Ciphertext × Word) × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support
      ((implementation (.inl (.inr (.inr (.inr (.inr publicKey)))))).run before)) :
    result.1 = (challenge, Word.atom) := by
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
  obtain ⟨answer, reached, equal⟩ := native
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
  simp only [RegistrationNativeSecretWordKemEarly.early, StateT.run, initial, ite_true, pure_bind,
    mem_support_bind_iff, mem_support_pure_iff] at actual
  obtain ⟨_dummy, _sampled, returned⟩ := actual
  cases returned
  cases equal
  rfl

private theorem getter_run (checks : Checks) (before : Auxiliary n KemSK) :
    (lower localImplementation (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate publicKey))).run before =
      if checks.kemKey publicKey then
        (fun result => (some (PqxdhAcceptedRegistration.ciphertextArray result.1.1, result.1.2),
          ({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray publicKey))) }, result.2))) <$>
          (implementation (.inl (.inr (.inr (.inr (.inr publicKey)))))).run before.2
      else pure (none,
        ({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray publicKey))) }, before.2)) := by
  rw [RegistrationNativeSecretWordTargetServerExecution.lower_run]
  simp only [RegistrationNativeSecretWordServerCompiler.prefixImpl, StateT.run, pq_key]
  by_cases valid : checks.kemKey publicKey = true
  · simp only [valid, ite_true, simulateQ_map, map_apply, localImpl, QueryImpl.compose,
      localKem, simulateQ_spec_query, liftLocal, RegistrationNativeSecretWordInterface.route,
      RegistrationNativeSecretWordInterface.routedKem, ite_true, Functor.map_map, Prod.map_def, id_eq]
    rw [pq_key]
    rfl
  · simp only [valid, Bool.false_eq_true, ite_false, simulateQ_pure, pure_apply, map_pure]

/-- The actual optional Server callback keeps its request log and can return only the matching challenge/atom pair at this first getter. -/
theorem getter_atom (checks : Checks) (before : Auxiliary n KemSK) (initial : before.2.kem.2 = none)
    (after : Auxiliary n KemSK) (pair : PqxdhBeaconPhase2Preparation.Ciphertext × Word)
    (supported : (some pair, after) ∈ support
      ((lower localImplementation (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate publicKey))).run before)) :
    pair = (PqxdhAcceptedRegistration.ciphertextArray challenge, Word.atom) := by
  rw [getter_run] at supported
  split at supported
  · rw [support_map] at supported
    obtain ⟨result, called, equal⟩ := supported
    have reply := getter_word setup wire route sign input inside selected pairs publicKey challenge outer before.2 initial result called
    have option := congrArg Prod.fst equal
    simp only [reply, Option.some.injEq] at option
    exact option.symm
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetGetter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetGetter.getter_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetGetter.getter_word
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetGetter.getter_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetGetter.getter_atom
