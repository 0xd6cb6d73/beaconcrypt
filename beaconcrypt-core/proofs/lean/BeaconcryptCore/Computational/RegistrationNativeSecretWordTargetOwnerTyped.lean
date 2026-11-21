-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPathState

/-! The actual successful selected-owner typed finish is its same scalar-free owner controller under the actual local Word interpreter. Current scalar mask and private-key alignment derive the owner handle rather than supplying it as an independent provenance assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetServerExecution (lower localImpl)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The literal successful typed finish yields the actual selected owner, current handle and same closed finish execution. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : Option registration.ResponsePacket) (application : Pqxdh.Bytes) (before after : State n KemSK source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.1.beacons)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.beacons before.2.kem.1.keys)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
        (.inr (.finish selectedOwner packet))).run before)) :
    ∃ owner afterOwner afterEnv afterPrivate,
      before.1.beacons[selectedOwner]? = some owner ∧ owner.scalar = none ∧ owner.view.kemHandle = selectedOwner ∧
      ((.ok (some application), afterOwner), (afterEnv, afterPrivate)) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer false)
          ((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner.view)).run (before.1.environment, before.2)) := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run] at supported
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
      obtain ⟨pair, _privateAt, handle, _public⟩ := RegistrationNativeSecretWordTargetAlignment.owner _ _ aligned selectedOwner owner found
      simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, mask.1,
        simulateQ_map, state_map_apply, support_map] at called
      obtain ⟨reached, possible, returned⟩ := called
      have successful : reached.1.1.1 = .ok (some application) :=
        (congrArg (fun result => result.1.1.1) returned).trans (congrArg Prod.fst equal)
      refine ⟨owner, reached.1.1.2, reached.1.2, reached.2, rfl, mask.1, handle, ?_⟩
      simp only [lower, StateT.run, support_map]
      refine ⟨reached, ?_, ?_⟩
      · simpa only [QueryImpl.simulateQ_compose, localImpl] using possible
      · exact Prod.ext (Prod.ext successful rfl) rfl
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTyped.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTyped.finish
