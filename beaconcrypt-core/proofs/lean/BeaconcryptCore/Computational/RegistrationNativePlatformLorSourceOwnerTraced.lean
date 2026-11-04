-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPrepared
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerTracedFinish
/-! The actual same monitored selected-owner callback reaches its own protected atom Ready and appends that descriptor at its own installation, with arbitrary persistent source/private state retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerTraced
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordInstallOrdinals (messages)
variable {n : Nat} {I KemSK Platform Private : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "combined" => RegistrationNativeSecretWordTracedPrivate.combined implementation
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformSecretWordOrdinary.State source Platform × (RegistrationNativeSecretWordFrontendTrace.State × Private)
include contract

theorem finish (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
    (before after : State source Platform Private)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) before.1.1.beacons)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons (kem before.2.2).1.keys)
    (pins : ∀ current,before.1.1.beacons[selected]?=some current →
      absBytes current.view.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (coherent : ∀ current,before.1.1.beacons[selected]?=some current →
      ∀ pending oneTime,current.view.phase=.initSent pending oneTime → pending.control.expected_server_binding=current.view.pin.binding)
    (ciphertext : packet.public.kem_cipher_text=PqxdhAcceptedRegistration.ciphertextArray challenge)
    (supported : (.ok (some application),after) ∈ support
      ((fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ combined ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) setup wire source selected (some packet)).run before.1)).run before.2)) :
    ∃ ready : RegistrationNativeSecretWordMessage.BeaconReady,
      ready.reference.kem=Word.atom ∧ (∃ key,nativeInput ready.reference=some key) ∧
      (∀ key,nativeInput ready.reference=some key →
        RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head=true) ∧
      ∀ role,messages role after.2.1.events=messages role before.2.1.events ++ if role=.beacon then [ready.reference] else [] := by
  obtain ⟨owner,afterOwner,afterEnv,afterPrivate,found,_scalar,handle,privateEq,finished⟩ :=
    RegistrationNativePlatformSecretWordTypedFinishOrigin.finish setup wire combined selected (setup.dh.publicKey scalar)
      (some packet) application before after canonical
      (fun current found => (RegistrationNativeSecretWordTargetAlignment.owner _ _ aligned selected current found).choose_spec.2.1) supported
  rw [privateEq] at finished
  obtain ⟨ready,preparedOwner,middle,prepared,completed⟩ :=
    RegistrationNativePlatformSecretWordFinishOrigin.finish (combined ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false)
      setup wire source (some packet) owner.view afterOwner application (before.1.1.environment,before.2) (afterEnv,after.2) finished
  have tracedContract : RegistrationNativePlatformLorSourceKem.Contract combined (fun current => kem current.2) nativeInput
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge) :=
    RegistrationNativePlatformLorSourceKemTrace.contract implementation kem nativeInput _ contract
  have protection := RegistrationNativePlatformLorSourceOwnerPrepared.prepared setup seed scalar selected pairs publicKey challenge
    combined (fun current => kem current.2) tracedContract source packet owner.view preparedOwner ready
    (before.1.1.environment,before.2) middle handle ciphertext (coherent owner found) (pins owner found) prepared
  refine ⟨ready,protection.1,protection.2.1,protection.2.2,?_⟩
  intro role
  have priorTrace := RegistrationNativeSecretWordTracedPrivate.lower_open_support implementation
    ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source (some packet)).run owner.view)
    before.1.1.environment before.2.1 before.2.2 _ prepared
  have prefixFree := RegistrationNativeSecretWordInstallTrace.free role _
    (RegistrationNativeSecretWordAtomInstallPredicate.local_bound role false _ 0
      (RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free role setup source (some packet) owner.view before.1.1.environment))
    before.2.1 _ priorTrace
  have final := RegistrationNativeSecretWordTracedPrivate.lower_open_support implementation
    ((RegistrationNativePlatformSecretWordFinish.complete setup.source wire.frameWrite owner.view ready).run preparedOwner)
    middle.1 middle.2.1 middle.2.2 _ completed
  have bill := RegistrationNativePlatformSecretWordInstallBeaconComplete.complete_all role setup none setup.source wire.frameWrite owner.view preparedOwner ready middle.1 middle.2.1
    (((.ok (some application),afterOwner),afterEnv),after.2.1)
    (by simpa only [RegistrationNativePlatformSecretWordInstallBeaconComplete.compile,RegistrationNativeSecretWordAtomOwnerSource.routing,StateT.run] using final)
  have success : RegistrationNativeInstallBeaconComplete.present (.ok (some application))=true := rfl
  simp only [success,and_true] at bill
  exact bill.trans (congrArg (fun events => events ++ if role=.beacon then [ready.reference] else []) prefixFree)
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerTraced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerTraced.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerTraced.finish
