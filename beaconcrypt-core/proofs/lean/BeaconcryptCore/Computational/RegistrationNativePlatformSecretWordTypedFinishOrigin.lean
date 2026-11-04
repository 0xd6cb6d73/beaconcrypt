-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask

/-! A successful current selected-owner callback exposes its exact scalar-free corrected finish under an arbitrary common private interpreter. The selected mask and owner-handle field are explicit local representation facts; later source-path consumers derive them from the initialized source invariants. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTypedFinishOrigin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordGenericLower (lower)
variable {n : Nat} {ι KemSK Private Platform : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The literal successful typed finish yields the actual selected owner, current handle and same closed finish execution. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : Option registration.ResponsePacket) (application : Pqxdh.Bytes) (before after : ((State source × Platform) × Private))
    (canonical : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.1.1.beacons)
    (handles : ∀ owner, before.1.1.beacons[selectedOwner]? = some owner → owner.view.kemHandle = selectedOwner)
    (supported : (.ok (some application), after) ∈ support
      ((fun value => (value.1.1, (value.1.2, value.2))) <$>
        (simulateQ implementation ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) setup wire source selectedOwner packet).run before.1)).run before.2)) :
    ∃ owner afterOwner afterEnv afterPrivate,
      before.1.1.beacons[selectedOwner]? = some owner ∧ owner.scalar = none ∧ owner.view.kemHandle = selectedOwner ∧ afterPrivate = after.2 ∧
      ((.ok (some application), afterOwner), (afterEnv, afterPrivate)) ∈ support
        ((lower (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false)
          ((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner.view)).run (before.1.1.environment, before.2)) := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish, StateT.run, support_map] at supported
  obtain ⟨reached, possible, returned⟩ := supported
  cases found : before.1.1.beacons[selectedOwner]? with
  | none =>
      simp only [found, simulateQ_pure] at possible
      cases possible
      cases returned
  | some owner =>
      have mask := canonical selectedOwner owner found
      simp only [RegistrationNativePublicOwnerMask.At, ite_true] at mask
      have handle := handles owner found
      simp only [found, mask.1, simulateQ_map, state_map_apply, support_map] at possible
      obtain ⟨localResult, called, equal⟩ := possible
      cases equal
      have successful : localResult.1.1.1 = .ok (some application) :=
        congrArg Prod.fst returned
      refine ⟨owner, localResult.1.1.2, localResult.1.2, localResult.2, rfl, mask.1, handle, ?_, ?_⟩
      · exact congrArg (fun result => result.2.2) returned
      · simp only [lower, StateT.run, support_map]
        refine ⟨localResult, ?_, ?_⟩
        · simpa only [QueryImpl.simulateQ_compose] using called
        · exact Prod.ext (Prod.ext successful rfl) rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTypedFinishOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTypedFinishOrigin.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTypedFinishOrigin.finish
