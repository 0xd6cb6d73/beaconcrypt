-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter

/-! Ordinary Server calls use the actual public encapsulation branch. Their supported successful collectors cannot contain the selected atom, independently of authentication pins, parsed ordinals, current pool contents or protected-root membership. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer
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
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer false

/-- The actual ordinary public getter cannot return an opaque atom, whatever its current pool and selected-getter marker. -/
theorem getter_word (key : MlKem768PublicKey) (before after : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (pair : MlKem768Ciphertext × Word)
    (supported : (pair, after) ∈ support
      ((implementation (.inl (.inr (.inr (.inl (.inr key)))))).run before)) :
    pair.2 ≠ Word.atom := by
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
  obtain ⟨answer, reached, equal⟩ := native
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
  intro atom
  have reply : answer.1.2 = Word.atom := (congrArg (fun result => result.1.2) equal).trans atom
  have pairEq : answer.1 = (answer.1.1, Word.atom) := Prod.ext rfl reply
  have called : ((answer.1.1, Word.atom), answer.2) ∈ support
      ((provider (.inl (.inr key))).run before.kem) := by
    rw [← pairEq]
    exact actual
  exact RegistrationNativeSecretWordKemEarlyAtom.public_getter setup.baseImpl setup.kem selected pairs publicKey key
    challenge answer.1.1 before.kem answer.2 called

private theorem getter_run (checks : Checks) (key : MlKem768PublicKey) (before : Auxiliary n KemSK) :
    (lower localImplementation (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate key))).run before =
      if checks.kemKey key then
        (fun result => (some (PqxdhAcceptedRegistration.ciphertextArray result.1.1, result.1.2),
          ({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray key))) }, result.2))) <$>
          (implementation (.inl (.inr (.inr (.inl (.inr key)))))).run before.2
      else pure (none,
        ({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray key))) }, before.2)) := by
  rw [RegistrationNativeSecretWordTargetServerExecution.lower_run]
  simp only [RegistrationNativeSecretWordServerCompiler.prefixImpl, StateT.run, pq_key]
  by_cases valid : checks.kemKey key = true
  · simp only [valid, ite_true, simulateQ_map, map_apply, localImpl, QueryImpl.compose,
      localKem, simulateQ_spec_query, liftLocal, RegistrationNativeSecretWordInterface.route,
      RegistrationNativeSecretWordInterface.routedKem, Bool.false_eq_true, ite_false, Functor.map_map, Prod.map_def, id_eq]
    rw [pq_key]
    rfl
  · simp only [valid, Bool.false_eq_true, ite_false, simulateQ_pure, pure_apply, map_pure]

/-- The exact optional callback of an ordinary Server collector keeps a literal KEM reply. -/
theorem getter_not_atom (checks : Checks) (key : MlKem768PublicKey) (before after : Auxiliary n KemSK)
    (pair : PqxdhBeaconPhase2Preparation.Ciphertext × Word)
    (supported : (some pair, after) ∈ support
      ((lower localImplementation (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate key))).run before)) :
    pair.2 ≠ Word.atom := by
  rw [getter_run] at supported
  split at supported
  · rw [support_map] at supported
    obtain ⟨result, called, equal⟩ := supported
    have literal := getter_word setup wire route sign input inside selected pairs publicKey challenge outer key before.2 result.2 result.1 called
    have option := congrArg Prod.fst equal
    simp only [Option.some.injEq] at option
    rw [← option]
    exact literal
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordInterpreter.handler RegistrationNativeSecretWordServerCompiler.collect
  RegistrationAuthenticationCompiler.program

/-- Every actual successful ordinary Server collection has a non-atom suffix from its same actual public getter. -/
theorem collect_not_atom (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before after : Auxiliary n KemSK)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (supported : (some collected, after) ∈ support
      ((lower localImplementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before)) :
    collected.kem ≠ Word.atom := by
  have equation : lower localImplementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated) =
      simulateQ (fun query => lower localImplementation (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks query))
        (RegistrationNativeSecretWordServerCollect.collect (RegistrationRootInput.verified packet authenticated)) := by
    rw [RegistrationNativeSecretWordServerCompiler.collect, RegistrationNativeSecretWordTargetServerExecution.lower_program]
  rw [equation] at supported
  obtain ⟨ephemeral, first, second, pair, _earlier, getter, _later, _verified, _ciphertext, word⟩ :=
    RegistrationNativeSecretWordTargetCollector.collect_receipt
      (fun query => lower localImplementation (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks query))
      (RegistrationRootInput.verified packet authenticated) before after collected supported
  have literal := getter_not_atom setup wire route sign input inside selected pairs publicKey challenge outer checks
    (RegistrationRootInput.verified packet authenticated).keys.pqKey first second pair getter
  intro atom
  exact literal (word.symm.trans atom)

/-- An ordinary successful accept retains its own literal collector descriptor in the actual returned session. -/
theorem accept_retained_not_atom (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (beforeServer afterServer : RegistrationNativeSecretWordMessage.ServerState)
    (before after : Auxiliary n KemSK) (handle : Nat)
    (supported : ((.ok (some handle), afterServer), after) ∈ support
      ((lower localImplementation ((RegistrationNativeSecretWordServerCompiler.accept setup checks verify packet).run beforeServer)).run before)) :
    ∃ ready, afterServer.sessions[handle]? = some (some ready) ∧ ready.reference.kem ≠ Word.atom := by
  obtain ⟨_events, authenticated, _afterAuthentication, ready, collected, middle, _authenticatedAt, stored, collectedAt, _rooted, echo⟩ :=
    RegistrationNativeSecretWordLiveServerOriginOuter.accept setup wire route sign input inside provider outer false checks verify packet
      beforeServer afterServer before after handle supported
  have literal := collect_not_atom setup wire route sign input inside selected pairs publicKey challenge outer checks
    packet authenticated _ middle collected collectedAt
  refine ⟨ready, stored, ?_⟩
  rw [echo]
  exact literal

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.getter_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.getter_word
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.getter_not_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.getter_not_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.collect_not_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.collect_not_atom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.accept_retained_not_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer.accept_retained_not_atom
