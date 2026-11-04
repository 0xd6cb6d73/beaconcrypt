-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhJointIdentity

/-! Executable recognition extracts any valid target-message Ed signature from a finite public byte string. A canonical source signature need not be unique: a different valid signature is equally useful to the ordinary weak-EUF reduction. No challenged seed or private cache is an input to this scanner. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition
open PqxdhEd25519EufCma (Ed25519PublicKey Ed25519Signature)

/-- Every checked offset has one exact 64-byte signature window. -/
def atOffset (input : Pqxdh.Bytes) (offset : Nat) : Option Ed25519Signature :=
  let window := (input.drop offset).take 64
  if width : window.length = 64 then some ⟨window, width⟩ else none

def candidates (input : Pqxdh.Bytes) : List Ed25519Signature :=
  (List.range (input.length + 1)).filterMap (atOffset input)

/-- An actual source signature occurring anywhere in the raw input is among the finite executable candidates. -/
theorem at_template (leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature) :
    atOffset (leading ++ signature.toList ++ trailing) leading.length = some signature := by
  unfold atOffset
  simp only [List.append_assoc, List.drop_left]
  have exactWindow : (signature.toList ++ trailing).take 64 = signature.toList := by
    exact List.take_left' signature.toList_length
  simp only [exactWindow, signature.toList_length, dite_true]
  rfl

theorem template_member (leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature) :
    signature ∈ candidates (leading ++ signature.toList ++ trailing) := by
  apply List.mem_filterMap.mpr
  refine ⟨leading.length, List.mem_range.mpr ?_, at_template leading trailing signature⟩
  simp only [List.length_append, signature.toList_length]
  omega

/-- This recognizer needs only the public verifier, target public key/message and the current finite input bytes. -/
def recognize (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message input : Pqxdh.Bytes) : Option Ed25519Signature :=
  (candidates input).find? (verify publicKey message)

/-- Any returned signature is valid on the selected target message, even if it differs from the canonical source signature. -/
theorem valid (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message input : Pqxdh.Bytes) (signature : Ed25519Signature)
    (found : recognize verify publicKey message input = some signature) :
    verify publicKey message signature = true := List.find?_some found

/-- A valid signature embedded in the actual raw hash address is always recognized by executable scanning. -/
theorem template_recognized (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature)
    (verified : verify publicKey message signature = true) :
    (recognize verify publicKey message (leading ++ signature.toList ++ trailing)).isSome = true :=
  List.find?_isSome.mpr ⟨signature, template_member leading trailing signature, verified⟩

/-- Before recognition, a public query cannot equal the private source address containing the selected valid signature. -/
theorem no_hit (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message leading trailing input : Pqxdh.Bytes) (signature : Ed25519Signature)
    (verified : verify publicKey message signature = true)
    (unrecognized : recognize verify publicKey message input = none) :
    input ≠ leading ++ signature.toList ++ trailing := by
  intro same
  subst input
  have present := template_recognized verify publicKey message leading trailing signature verified
  rw [unrecognized] at present
  contradiction

/-- Recognition plus the reduction's actual target-message freshness is the ordinary primitive winning predicate, with no signature-uniqueness premise. -/
theorem weak_euf (primitives : PqxdhJointIdentity.Primitives) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (message input : Pqxdh.Bytes) (signature : Ed25519Signature) (history : PqxdhJointIdentity.History)
    (found : recognize primitives.verify publicIdentity.ed25519 message input = some signature)
    (fresh : message ∉ PqxdhJointIdentity.signedMessages history) :
    PqxdhJointIdentity.wins primitives publicIdentity ⟨message, signature⟩ history = true := by
  simp only [PqxdhJointIdentity.wins, valid _ _ _ _ _ found, fresh, decide_false, Bool.not_false, Bool.and_self]

end BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.at_template' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.at_template
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.template_member' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.template_member
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.valid
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.template_recognized' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.template_recognized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.no_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.no_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.weak_euf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition.weak_euf
