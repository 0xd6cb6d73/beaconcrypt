-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTyped
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPreparationPin

/-! A successful actual selected-owner finish exposes the same complete-stage Ready with its challenge atom and protected first-DH slice. Current owner mask, key alignment, configured pin and pending-pin coherence are explicit local invariants discharged by the original complete source. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinishProtected
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeSecretWordMessage (BeaconReady)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetServerExecution (lower localImpl)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordKemEarly.early
  RegistrationNativeSecretWordTargetServerExecution.localImpl

/-- The same actual successful complete stage installs a protected atom reference supplied by its own original owner preparation. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (packet : registration.ResponsePacket) (application : Pqxdh.Bytes) (before after : State n KemSK source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selectedOwner (setup.dh.publicKey scalar) before.1.beacons)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.beacons before.2.kem.1.keys)
    (pins : ∀ current, before.1.beacons[selectedOwner]? = some current →
      absBytes current.view.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (coherent : ∀ current, before.1.beacons[selectedOwner]? = some current →
      ∀ pending oneTime, current.view.phase = .initSent pending oneTime →
        pending.control.expected_server_binding = current.view.pin.binding)
    (ciphertext : packet.public.kem_cipher_text = PqxdhAcceptedRegistration.ciphertextArray challenge)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge)
        outer selectedOwner selectedAccept (setup.dh.publicKey scalar) (.inr (.finish selectedOwner (some packet)))).run before)) :
    ∃ current : RegistrationNativePublicOwners.Owner source,
    ∃ afterOwner : RegistrationBeaconReferenceCompiler.SelectedOwner source,
    ∃ preparedOwner : RegistrationBeaconReferenceCompiler.SelectedOwner source,
    ∃ ready : BeaconReady, ∃ middle : RegistrationNativeSecretWordTargetServerExecution.Auxiliary n KemSK,
    ∃ afterEnv afterPrivate,
      before.1.beacons[selectedOwner]? = some current ∧
      ready.reference.kem = Word.atom ∧
      (∃ key, RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar ready.reference = some key) ∧
      (∀ key, RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar ready.reference = some key →
        RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head = true) ∧
      ((.ok (some application), afterOwner), (afterEnv, afterPrivate)) ∈ support
        ((lower (localImpl setup wire route sign
          (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge) outer false)
          ((RegistrationNativeSecretWordBeaconCompiler.complete setup.source current.view ready).run preparedOwner)).run middle) := by
  let input := RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
  let inside := RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
  let provider := RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge
  let implementation := localImpl (n := n) setup wire route sign input inside provider outer false
  obtain ⟨current, afterOwner, afterEnv, afterPrivate, found, _scalar, handle, finished⟩ :=
    RegistrationNativeSecretWordTargetOwnerTyped.finish setup checks wire route sign input inside provider outer selectedOwner selectedAccept (setup.dh.publicKey scalar)
      (some packet) application before after canonical aligned supported
  obtain ⟨ready, preparedOwner, middle, prepared, completed⟩ :=
    RegistrationNativeSecretWordTargetOwnerFinish.finish implementation setup source (some packet) current.view afterOwner application
      (before.1.environment, before.2) (afterEnv, afterPrivate) finished
  have protection :=  RegistrationNativeSecretWordTargetOwnerPreparationPin.prepared setup wire route sign seed scalar selectedOwner pairs publicKey challenge outer source
    packet current.view preparedOwner ready (before.1.environment, before.2) middle handle ciphertext (coherent current found) (pins current found) prepared
  exact ⟨current, afterOwner, preparedOwner, ready, middle, afterEnv, afterPrivate, found, protection.1, protection.2.1, protection.2.2, completed⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinishProtected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinishProtected.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinishProtected.finish
