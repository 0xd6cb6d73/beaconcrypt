-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrigin
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuthSource

/-! Actual selected-owner terminal preparation derives its protected atom Ready from the original mandatory authentication, ordered current-handle decapsulation and exact source root echo. The current configured pin and actual pending-pin invariant replace any independent packet identity input. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPreparationPin
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordMessage (BeaconReady)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationNativeSecretWordKemEarly.early
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordTargetServerExecution.localImpl

/-- The actual successful selected-owner preparation carries its same atom root in the protected first-DH slice. -/
theorem prepared (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp) (source : RegistrationNativeMldsa.Source)
    (packet : registration.ResponsePacket) (owner afterOwner : SelectedOwner source) (ready : BeaconReady)
    (before after : Auxiliary n KemSK)
    (handle : owner.kemHandle = selected)
    (ciphertext : packet.public.kem_cipher_text = PqxdhAcceptedRegistration.ciphertextArray challenge)
    (pendingPin : ∀ pending oneTime, owner.phase = .initSent pending oneTime →
      pending.control.expected_server_binding = owner.pin.binding)
    (pin : absBytes owner.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (supported : ((.ok (some ready), afterOwner), after) ∈ support
      ((lower (localImpl setup wire route sign (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge) outer false)
        ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source (some packet)).run owner)).run before)) :
    ready.reference.kem = Word.atom ∧
      (∃ key, RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar ready.reference = some key) ∧
      ∀ key, RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar ready.reference = some key →
        RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head = true := by
  let input := RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
  let inside := RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
  let provider := RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
  let implementation := localImpl (n := n) setup wire route sign input inside provider outer false
  obtain ⟨pending, oneTime, aborted, authenticated, middle, phase, _moved, checked, agreed⟩ :=
    RegistrationNativeSecretWordTargetOwnerOrigin.preparation implementation setup source (some packet) owner afterOwner ready before after supported
  obtain ⟨supplied, suppliedEq, _digest, _completed, _completedRun, authenticatedEq⟩ :=
    RegistrationNativeSecretWordTargetOwnerAuthSource.packet implementation setup source pending (some packet) authenticated before middle checked
  have packetEq : packet = supplied := Option.some.inj suppliedEq
  subst supplied
  obtain ⟨collected, reached, called, rooted, _env⟩ :=
    RegistrationNativeSecretWordTargetOwnerOrigin.agreement implementation setup owner oneTime authenticated ready middle after agreed
  have fields := RegistrationNativeSecretWordTargetOwnerCollectedAtom.collect setup wire route sign input inside selected pairs publicKey challenge outer
    owner oneTime authenticated middle reached collected handle (by rw [authenticatedEq]; exact ciphertext) called
  have collectedPin := (PqxdhPhase2DhMetadata.admitted_fields (completedBinding := authenticated.binding) authenticated.control
    collected.collected.plain collected.metadata fields.2.2.2.2.2).1
  rw [authenticatedEq] at collectedPin
  rw [pendingPin pending oneTime phase] at collectedPin
  have selectedPin := RegistrationNativeSecretWordTargetOwnerProtected.converted_pin setup seed
    collected.collected.plain.server collected.collected.plain.serverConverted
    (collectedPin.symm.trans pin) fields.2.2.2.2.1
  have root := RegistrationNativeSecretWordTargetOwnerRoot.root setup wire route sign input inside provider outer authenticated collected ready reached.2 after.2 rooted
  refine ⟨?_, root.2, ?_⟩
  · rw [root.1]
    exact fields.1
  · intro key realized
    rw [root.1] at realized
    exact RegistrationNativeSecretWordTargetOwnerProtected.beacon_inside setup seed scalar RegistrationNativeSecretWordMessage.zero collected selectedPin key realized
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPreparationPin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPreparationPin.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPreparationPin.prepared
