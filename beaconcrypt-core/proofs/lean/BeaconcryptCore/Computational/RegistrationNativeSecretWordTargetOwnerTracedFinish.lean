-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedTyped
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPreparationPin
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix

/-! The actual same monitored typed owner callback reaches its own protected atom Ready and contributes exactly that descriptor to the final original chronology. Its internal preparation and completion cuts are taken before erasing the trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTracedFinish
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetTracedSource (State)
open RegistrationNativeSecretWordInstallOrdinals (messages)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordKemEarly.early RegistrationNativeSecretWordTargetServerExecution.localImpl

/-- Actual monitored owner success has one same-role protected atom installation, at its original callback's own chronology. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (packet : registration.ResponsePacket) (application : Pqxdh.Bytes) (before after : State n KemSK source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selectedOwner (setup.dh.publicKey scalar) before.1.1.beacons)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons before.2.kem.1.keys)
    (pins : ∀ current, before.1.1.beacons[selectedOwner]? = some current →
      absBytes current.view.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (coherent : ∀ current, before.1.1.beacons[selectedOwner]? = some current →
      ∀ pending oneTime, current.view.phase = .initSent pending oneTime →
        pending.control.expected_server_binding = current.view.pin.binding)
    (ciphertext : packet.public.kem_cipher_text = PqxdhAcceptedRegistration.ciphertextArray challenge)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeSecretWordTargetTracedSource.typed setup checks wire route sign
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge)
        outer selectedOwner selectedAccept (setup.dh.publicKey scalar) (.inr (.finish selectedOwner (some packet)))).run before)) :
    ∃ ready : RegistrationNativeSecretWordMessage.BeaconReady,
      ready.reference.kem = RegistrationNativeSecretWord.Word.atom ∧
      (∃ key, RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar ready.reference = some key) ∧
      (∀ key, RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar ready.reference = some key →
        RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head = true) ∧
      ∀ role, messages role after.1.2.events = messages role before.1.2.events ++
        if role = .beacon then [ready.reference] else [] := by
  let input := RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
  let inside := RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
  let provider := RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge
  let implementation := RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
  let combined := RegistrationNativeSecretWordTracedPrivate.combined implementation
  have mapped := Set.mem_image_of_mem (Prod.map id RegistrationNativeSecretWordTracedTyped.associate) supported
  rw [← support_map, RegistrationNativeSecretWordTracedTyped.typed_source] at mapped
  obtain ⟨owner, afterOwner, afterEnv, afterPrivate, found, _scalar, handle, privateEq, finished⟩ :=
    RegistrationNativeSecretWordGenericTypedFinish.finish setup checks wire sign combined selectedOwner selectedAccept (setup.dh.publicKey scalar)
      (some packet) application (RegistrationNativeSecretWordTracedTyped.associate before) (RegistrationNativeSecretWordTracedTyped.associate after)
      canonical (fun current found => (RegistrationNativeSecretWordTargetAlignment.owner _ _ aligned selectedOwner current found).choose_spec.2.1) mapped
  rw [privateEq] at finished
  obtain ⟨ready, preparedOwner, middle, prepared, completed⟩ :=
    RegistrationNativeSecretWordGenericFinish.finish (combined ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false)
      setup source (some packet) owner.view afterOwner application (before.1.1.environment, (before.1.2, before.2))
      (afterEnv, (after.1.2, after.2)) finished
  have erased := Set.mem_image_of_mem (Prod.map id (Prod.map id Prod.snd)) prepared
  rw [← support_map, RegistrationNativeSecretWordTracedPrivate.lower] at erased
  have ordinary : ((.ok (some ready), preparedOwner), (middle.1, middle.2.2)) ∈ support
      ((RegistrationNativeSecretWordTargetServerExecution.lower
        (RegistrationNativeSecretWordTargetServerExecution.localImpl setup wire route sign input inside provider outer false)
        ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source (some packet)).run owner.view)).run (before.1.1.environment, before.2)) := by
    simpa only [RegistrationNativeSecretWordTargetServerExecution.lower,
      RegistrationNativeSecretWordGenericLower.lower, RegistrationNativeSecretWordTargetServerExecution.localImpl,
      StateT.run, Prod.map_def, id_eq] using erased
  have protection := RegistrationNativeSecretWordTargetOwnerPreparationPin.prepared setup wire route sign seed scalar selectedOwner pairs publicKey challenge outer source
    packet owner.view preparedOwner ready (before.1.1.environment, before.2) (middle.1, middle.2.2) handle ciphertext
    (coherent owner found) (pins owner found) ordinary
  refine ⟨ready, protection.1, protection.2.1, protection.2.2, ?_⟩
  intro role
  have priorTrace := RegistrationNativeSecretWordTracedPrivate.lower_open_support implementation
    ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source (some packet)).run owner.view)
    before.1.1.environment before.1.2 before.2 _ prepared
  have prefixFree := RegistrationNativeSecretWordInstallTrace.free role _
    (RegistrationNativeSecretWordAtomInstallPredicate.local_bound role false _ 0
      (RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free role setup source (some packet) owner.view before.1.1.environment))
    before.1.2 _ priorTrace
  have final := RegistrationNativeSecretWordTracedPrivate.lower_open_support implementation
    ((RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner.view ready).run preparedOwner)
    middle.1 middle.2.1 middle.2.2 _ completed
  have bill := RegistrationNativeSecretWordInstallBeaconComplete.complete role setup.source owner.view preparedOwner ready middle.1 middle.2.1
    (((.ok (some application), afterOwner), afterEnv), after.1.2)
    (by simpa only [RegistrationNativeSecretWordBeaconCompiler.complete, StateT.run, RegistrationNativeSecretWordInstallBeaconComplete.compile] using final)
    application rfl
  exact bill.trans (congrArg (fun events => events ++ if role = .beacon then [ready.reference] else []) prefixFree)
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTracedFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTracedFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerTracedFinish.finish
