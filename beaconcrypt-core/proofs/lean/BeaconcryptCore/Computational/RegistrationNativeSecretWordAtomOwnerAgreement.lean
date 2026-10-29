-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerPreparation
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerRoot

/-! Successful actual incoming agreement retains the KEM suffix of the same reached collection through selected or ordinary root preparation. An atom therefore identifies its actual owner's selected private handle, including early finishes before the Server getter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAgreement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open RegistrationNativeSecretWordAtomOwnerGetter (withScalar)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_lift_apply {State Value : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m Value) (before : State) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {State Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT State m Value) (before : State) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem state_pure_apply {State Value : Type} {m : Type → Type} [Monad m]
    (value : Value) (before : State) : (pure value : StateT State m Value) before = pure (value, before) := rfl

private theorem agreement_run (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : Auxiliary n KemSK) :
    (lower implementation (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)).run before = (do
      let collected ← (lower implementation (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated)).run before
      match collected.1 with
      | none => pure (.ok none, collected.2)
      | some pending =>
          (fun result => (result.1, (collected.2.1, result.2))) <$>
            (simulateQ implementation (simulateQ RegistrationNativeSecretWordInterface.prepare
              (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run collected.2.2) := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement, RegistrationNativeSecretWordTargetServerExecution.lower_bind,
    StateT.run_bind]
  apply bind_congr
  rintro ⟨collected, env, context⟩
  cases collected <;>
    simp only [lower, StateT.run, state_pure_apply, state_lift_apply, state_map_apply, simulateQ_pure, simulateQ_map,
      map_pure, Functor.map_map, Prod.map_def, id_eq]

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordInterpreter.handler RegistrationNativeSecretWordBeaconCompiler.collect
  RegistrationNativeSecretWordBeaconCompiler.agreement RegistrationNativeSecretWordAtomOwnerGetter.withScalar
  RegistrationNativeSecretWordTargetServerExecution.lower RegistrationNativeSecretWordTargetServerExecution.localImpl

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer false

/-- An actual Ready atom comes from its same successful incoming collection and therefore its same retained private handle. -/
theorem agreement_handle (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (ready : BeaconReady) (before after : Auxiliary n KemSK) (atom : ready.reference.kem = Word.atom)
    (supported : (.ok (some ready), after) ∈ support
      ((lower (withScalar setup localImplementation scalar)
        (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)).run before)) :
    owner.kemHandle = selected := by
  rw [agreement_run, mem_support_bind_iff] at supported
  obtain ⟨collected, collectedAt, supported⟩ := supported
  cases formed : collected.1 with
  | none => simp only [formed, mem_support_pure_iff] at supported; cases supported
  | some pending =>
      simp only [formed, support_map] at supported
      obtain ⟨reached, rooted, equal⟩ := supported
      have sameValue := congrArg Prod.fst equal
      have sameState := congrArg (fun result => result.2.2) equal
      have pairEqual : reached = (.ok (some ready), after.2) := Prod.ext sameValue sameState
      rw [pairEqual] at rooted
      have sameKem := RegistrationNativeSecretWordAtomOwnerRoot.client_kem setup wire route sign input inside provider outer
        scalar authenticated pending ready collected.2.2 after.2 rooted
      have actual : (some pending, collected.2) ∈ support
          ((lower (withScalar setup localImplementation scalar)
            (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated)).run before) := by
        simpa only [← formed, Prod.mk.eta] using collectedAt
      exact (RegistrationNativeSecretWordAtomOwnerPreparation.collect_handle setup wire route sign input inside selected pairs
        publicKey challenge outer owner oneTime authenticated scalar before collected.2 pending (sameKem.symm.trans atom) actual).1

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAgreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAgreement.agreement_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAgreement.agreement_handle
