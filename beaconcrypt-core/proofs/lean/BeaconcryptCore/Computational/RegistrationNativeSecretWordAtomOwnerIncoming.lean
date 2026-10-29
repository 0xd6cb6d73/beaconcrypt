-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAgreement
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCredit

/-! Actual incoming preparation consumes its retained owner before parsing. A returned atom Ready identifies that same owner's selected indexed handle and successful terminal-move gate. The local owner index follows only from the derived current roster alignment, never from an assumed index equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerIncoming
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open RegistrationNativeSecretWordAtomOwnerGetter (withScalar)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_lift_apply {State Value : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m Value) (before : State) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {State Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT State m Value) (before : State) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

attribute [local irreducible] RegistrationResponseExecutor.begin
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordInterpreter.handler
  RegistrationNativeSecretWordBeaconCompiler.collect RegistrationNativeSecretWordBeaconCompiler.agreement
  RegistrationNativeSecretWordAtomOwnerGetter.withScalar RegistrationNativeSecretWordTargetServerExecution.lower
  RegistrationNativeSecretWordTargetServerExecution.localImpl

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer false

/-- The actual same-owner incoming atom receipt includes successful terminal consumption before optional admission. -/
theorem preparation_handle (scalar : Option PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket)
    (owner afterOwner : SelectedOwner source) (ready : BeaconReady) (before after : Auxiliary n KemSK)
    (atom : ready.reference.kem = Word.atom)
    (supported : ((.ok (some ready), afterOwner), after) ∈ support
      ((lower (withScalar setup localImplementation scalar)
        ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner)).run before)) :
    owner.kemHandle = selected ∧ RegistrationNativeSecretWordOwnerCredit.canFinish owner.phase = true := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finishPreparation, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [phase, lower, StateT.run] at supported
      cases supported
  | initSent pending oneTime =>
      simp only [phase] at supported
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, lower, StateT.run] at supported
          cases supported
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc,
            RegistrationNativeSecretWordTargetServerExecution.lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨accepted, _checked, supported⟩ := supported
          cases checked : accepted.1 with
          | fail error | div =>
              simp only [checked, lower, StateT.run] at supported
              cases supported
          | ok reply => cases reply with
            | Err error =>
                simp only [checked, lower, StateT.run] at supported
                cases supported
            | Ok authenticated =>
                simp only [checked, lower, StateT.run, state_lift_apply, state_map_apply, simulateQ_map,
                  Functor.map_map, support_map] at supported
                obtain ⟨reached, possible, equal⟩ := supported
                have actual : (.ok (some ready), after) ∈ support
                    ((lower (withScalar setup localImplementation scalar)
                      (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)).run accepted.2) := by
                  simp only [lower, StateT.run, support_map]
                  refine ⟨reached, possible, ?_⟩
                  exact Prod.ext (congrArg (fun result => result.1.1) equal) (congrArg (fun result => result.2) equal)
                exact ⟨RegistrationNativeSecretWordAtomOwnerAgreement.agreement_handle setup wire route sign input inside
                  selected pairs publicKey challenge outer owner oneTime authenticated scalar ready accepted.2 after atom actual,
                  by simp only [RegistrationNativeSecretWordOwnerCredit.canFinish, moved]⟩

/-- For an aligned actual call entry, an incoming atom belongs to the selected local owner and spends precisely its terminal gate. -/
theorem preparation_owner (owners : RegistrationNativePublicOwners.State source)
    (keys : List (MlKem768PublicKey × KemSK)) (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned owners keys)
    (found : owners[index]? = some owner) (packet : Option registration.ResponsePacket)
    (afterOwner : SelectedOwner source) (ready : BeaconReady) (before after : Auxiliary n KemSK)
    (atom : ready.reference.kem = Word.atom)
    (supported : ((.ok (some ready), afterOwner), after) ∈ support
      ((lower (withScalar setup localImplementation owner.scalar)
        ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner.view)).run before)) :
    index = selected ∧ RegistrationNativeSecretWordOwnerCredit.canFinish owner.view.phase = true := by
  have actual := preparation_handle setup wire route sign input inside selected pairs publicKey challenge outer
    owner.scalar packet owner.view afterOwner ready before after atom supported
  exact ⟨RegistrationNativeSecretWordAtomOwnerPreparation.owner_index selected owners keys index owner aligned found actual.1, actual.2⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerIncoming
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerIncoming.preparation_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerIncoming.preparation_handle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerIncoming.preparation_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerIncoming.preparation_owner
