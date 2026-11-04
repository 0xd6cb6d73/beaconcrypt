-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected
/-! Actual selected-owner preparation derives its challenge atom and protected first-DH prefix from the same source authentication, collector, configured pin and prepare echo. The private interpreter may contain arbitrary persistent physical record state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPrepared
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordMessage (BeaconReady)
open RegistrationNativeSecretWordGenericLower (Auxiliary lower)
variable {n : Nat} {I KemSK Private : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "localImpl" => implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
variable (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem
  (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
include contract

theorem prepared (source : RegistrationNativeMldsa.Source) (packet : registration.ResponsePacket)
    (owner afterOwner : SelectedOwner source) (ready : BeaconReady) (before after : Auxiliary Private)
    (handle : owner.kemHandle=selected)
    (ciphertext : packet.public.kem_cipher_text=PqxdhAcceptedRegistration.ciphertextArray challenge)
    (pendingPin : ∀ pending oneTime, owner.phase=.initSent pending oneTime →
      pending.control.expected_server_binding=owner.pin.binding)
    (pin : absBytes owner.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (supported : ((.ok (some ready),afterOwner),after) ∈ support
      ((lower localImpl ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source (some packet)).run owner)).run before)) :
    ready.reference.kem=Word.atom ∧ (∃ key,nativeInput ready.reference=some key) ∧
      ∀ key,nativeInput ready.reference=some key →
        RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head=true := by
  obtain ⟨pending,oneTime,aborted,authenticated,middle,phase,_moved,checked,agreed⟩ :=
    RegistrationNativePlatformLorSourceOwnerControl.preparation localImpl setup source (some packet) owner afterOwner ready before after supported
  obtain ⟨supplied,suppliedEq,authenticatedEq⟩ :=
    RegistrationNativePlatformLorSourceOwnerControl.packet localImpl setup source pending (some packet) authenticated before middle checked
  have packetEq : packet=supplied := Option.some.inj suppliedEq
  subst supplied
  obtain ⟨collected,reached,called,rooted,_env⟩ :=
    RegistrationNativePlatformLorSourceOwnerControl.agreement localImpl setup owner oneTime authenticated ready middle after agreed
  have fields := RegistrationNativePlatformLorSourceOwnerCollect.collect_atom setup implementation owner oneTime authenticated
    selected pairs publicKey challenge kem nativeInput contract middle reached collected handle (by rw [authenticatedEq];exact ciphertext) called
  have collectedPin := (PqxdhPhase2DhMetadata.admitted_fields authenticated.pending.control
    collected.collected.plain collected.metadata fields.2.2.2.2.2).1
  rw [authenticatedEq] at collectedPin
  rw [pendingPin pending oneTime phase] at collectedPin
  have selectedPin := RegistrationNativeSecretWordTargetOwnerProtected.converted_pin setup seed
    collected.collected.plain.server collected.collected.plain.serverConverted
    (collectedPin.symm.trans pin) fields.2.2.2.2.1
  have root := RegistrationNativePlatformLorSourceOwnerKem.root_fields setup selected pairs publicKey challenge implementation kem nativeInput contract
    authenticated collected ready reached.2 after.2 rooted
  refine ⟨?_,root.2,?_⟩
  · rw [root.1]
    exact fields.1
  · intro key realized
    rw [root.1] at realized
    exact RegistrationNativeSecretWordTargetOwnerProtected.beacon_inside setup seed scalar RegistrationNativeSecretWordMessage.zero collected selectedPin key realized
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPrepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPrepared.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPrepared.prepared
