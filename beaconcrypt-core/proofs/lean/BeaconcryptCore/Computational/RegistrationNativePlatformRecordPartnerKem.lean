-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom

/-! Opaque atoms identify their actual selected private row or first getter through individual source KEM receipts. These inverse leaves retain arbitrary persistent source state and assert no protocol-partner or whole-callback conclusion. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativePlatformLorSourceKem (Contract)
variable {n : Nat} {I KemSK Private : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))

include contract in
/-- An actual opaque atom decapsulation identifies the selected current private handle and the literal challenge ciphertext. -/
theorem decapsulate (handle : Nat) (ciphertext : MlKem768Ciphertext) (before after : Private)
    (supported : (some Word.atom,after) ∈ support
      ((implementation (.inl (.inr (.inr (.inr (.inl (.decapsulate handle ciphertext))))))).run before)) :
    handle=selected ∧ ciphertext=challenge ∧ ∃ pair,(kem before).1.keys[handle]?=some pair := by
  exact RegistrationNativeSecretWordKemEarlyAtom.decapsulate setup.baseImpl setup.kem selected pairs publicKey challenge
    ciphertext handle (kem before) (kem after)
    (contract.routed (.inr (.inl (.decapsulate handle ciphertext))) before (some Word.atom,after) supported)

include contract in
/-- An exposed-getter atom comes from its genuine first matching challenge reply in that same reached private state. -/
theorem getter (key : MlKem768PublicKey) (ciphertext : MlKem768Ciphertext) (before after : Private)
    (supported : ((ciphertext,Word.atom),after) ∈ support
      ((implementation (.inl (.inr (.inr (.inr (.inr key)))))).run before)) :
    (kem before).2=none ∧ key=publicKey ∧ ciphertext=challenge := by
  exact RegistrationNativeSecretWordKemEarlyAtom.getter setup.baseImpl setup.kem selected pairs publicKey key challenge
    ciphertext (kem before) (kem after)
    (contract.routed (.inr (.inr key)) before ((ciphertext,Word.atom),after) supported)

include contract in
/-- The actual ordinary public encapsulation branch cannot return the protected opaque atom. -/
theorem public_getter (key : MlKem768PublicKey) (ciphertext : MlKem768Ciphertext) (before after : Private) :
    ((ciphertext,Word.atom),after) ∉ support
      ((implementation (.inl (.inr (.inr (.inl (.inr key)))))).run before) := by
  intro supported
  exact RegistrationNativeSecretWordKemEarlyAtom.public_getter setup.baseImpl setup.kem selected pairs publicKey key challenge
    ciphertext (kem before) (kem after)
    (contract.routed (.inl (.inr key)) before ((ciphertext,Word.atom),after) supported)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem.decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem.decapsulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem.getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem.getter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem.public_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem.public_getter
