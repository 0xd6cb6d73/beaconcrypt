-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPathState

/-! The actual successful selected-owner typed finish is its same scalar-free owner controller under the actual local Word interpreter. Current scalar mask and private-key alignment derive the owner handle rather than supplying it as an independent provenance assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericTypedFinish
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordGenericLower (lower)
variable {n : Nat} {ι KemSK Private : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

noncomputable def typed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State source × Private) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ implementation ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before.1)).run before.2

/-- The literal successful typed finish yields the actual selected owner, current handle and same closed finish execution. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : Option registration.ResponsePacket) (application : Pqxdh.Bytes) (before after : (State source × Private))
    (canonical : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.1.beacons)
    (handles : ∀ owner, before.1.beacons[selectedOwner]? = some owner → owner.view.kemHandle = selectedOwner)
    (supported : (.ok (some application), after) ∈ support
      ((typed setup checks wire sign implementation selectedOwner selectedAccept publicPrekey
        (.inr (.finish selectedOwner packet))).run before)) :
    ∃ owner afterOwner afterEnv afterPrivate,
      before.1.beacons[selectedOwner]? = some owner ∧ owner.scalar = none ∧ owner.view.kemHandle = selectedOwner ∧ afterPrivate = after.2 ∧
      ((.ok (some application), afterOwner), (afterEnv, afterPrivate)) ∈ support
        ((lower (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false)
          ((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner.view)).run (before.1.environment, before.2)) := by
  change (_, _) ∈ support ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ implementation ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.finish selectedOwner packet))).run before.1)).run before.2) at supported
  simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.beacon,
    StateT.run, simulateQ_map, state_map_apply, Functor.map_map, support_map] at supported
  obtain ⟨finished, called, equal⟩ := supported
  cases found : before.1.beacons[selectedOwner]? with
  | none =>
      simp only [RegistrationNativeSecretWordOwners.finish, found,
        simulateQ_pure, ] at called
      cases called
      cases equal
  | some owner =>
      have mask := canonical selectedOwner owner found
      simp only [RegistrationNativePublicOwnerMask.At, ite_true] at mask
      have handle := handles owner found
      simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, mask.1,
        simulateQ_map, state_map_apply, support_map] at called
      obtain ⟨reached, possible, returned⟩ := called
      have successful : reached.1.1.1 = .ok (some application) :=
        (congrArg (fun result => result.1.1.1) returned).trans (congrArg Prod.fst equal)
      refine ⟨owner, reached.1.1.2, reached.1.2, reached.2, rfl, mask.1, handle, ?_, ?_⟩
      · exact (congrArg (fun result => result.2) returned).trans (congrArg (fun result => result.2.2) equal)
      · simp only [lower, StateT.run, support_map]
        refine ⟨reached, ?_, ?_⟩
        · simpa only [QueryImpl.simulateQ_compose] using possible
        · exact Prod.ext (Prod.ext successful rfl) rfl
end BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericTypedFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericTypedFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericTypedFinish.finish
