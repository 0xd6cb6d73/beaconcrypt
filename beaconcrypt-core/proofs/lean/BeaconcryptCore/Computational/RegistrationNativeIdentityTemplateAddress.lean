-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress
open PqxdhEd25519EufCma (Ed25519Signature Ed25519PublicKey)
open RegistrationNativeIdentityPublicHashTemplate (parts)
abbrev Frame := Pqxdh.Bytes × Pqxdh.Bytes
abbrev Key := Pqxdh.Bytes ⊕ Frame

def realize (signature : Ed25519Signature) : Key → Pqxdh.Bytes
  | .inl bytes => bytes
  | .inr frame => frame.1 ++ signature.toList ++ frame.2

noncomputable def abstract (signature : Ed25519Signature) (bytes : Pqxdh.Bytes) : Key := by
  classical
  exact if (parts bytes).1.length = 2188 ∧ bytes = realize signature (.inr (parts bytes)) then
    .inr (parts bytes) else .inl bytes

/-- Every physical address is reconstructed exactly after private abstraction; no width or recognition premise is needed. -/
theorem realize_abstract (signature : Ed25519Signature) (bytes : Pqxdh.Bytes) :
    realize signature (abstract signature bytes) = bytes := by
  unfold abstract
  split
  · exact ‹(parts bytes).1.length = 2188 ∧ bytes = realize signature (.inr (parts bytes))›.2.symm
  · rfl

/-- An admitted hidden source template retains its exact public framing, independently of the signature value. -/
theorem abstract_hidden (signature : Ed25519Signature) (frame : Frame) (width : frame.1.length = 2188) :
    abstract signature (realize signature (.inr frame)) = .inr frame := by
  have extracted := RegistrationNativeIdentityPublicHashTemplate.extracted frame.1 frame.2 signature width
  simp only [abstract,realize,extracted,width,true_and,ite_true]

/-- Equal realized admitted hidden addresses have identical public framing; no signature uniqueness or key injectivity is used. -/
theorem hidden_injective (signature : Ed25519Signature) (left right : Frame)
    (leftWidth : left.1.length = 2188) (rightWidth : right.1.length = 2188)
    (same : realize signature (.inr left) = realize signature (.inr right)) : left = right := by
  have first := abstract_hidden signature left leftWidth
  have second := abstract_hidden signature right rightWidth
  have keys := first.symm.trans ((congrArg (abstract signature) same).trans second)
  exact Sum.inr.inj keys


/-- An unrecognized public input stays in its public branch under private abstraction. Recognition uses ordinary verification of the target message. -/
theorem abstract_public (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (bytes : Pqxdh.Bytes)
    (unrecognized : RegistrationNativeIdentityRecognition.recognize verify publicKey message bytes = none) :
    abstract signature (realize signature (.inl bytes)) = .inl bytes := by
  change abstract signature bytes = .inl bytes
  unfold abstract
  split
  · rename_i selected
    exact False.elim (RegistrationNativeIdentityRecognition.no_hit verify publicKey message
      (parts bytes).1 (parts bytes).2 bytes signature valid unrecognized selected.2)
  · rfl

def Admitted (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) : Key → Prop
  | .inl bytes => RegistrationNativeIdentityRecognition.recognize verify publicKey message bytes = none
  | .inr frame => frame.1.length = 2188

/-- Both admitted public inputs and actual width-correct templates have an exact left inverse under the same private signature. -/
theorem abstract_admitted (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (key : Key) (admitted : Admitted verify publicKey message key) :
    abstract signature (realize signature key) = key := by
  cases key with
  | inl bytes => exact abstract_public verify publicKey message signature valid bytes admitted
  | inr frame => exact abstract_hidden signature frame admitted

/-- Public and hidden symbolic keys are jointly injective on admitted queries up to the public ordinary-EUF recognition stop. -/
theorem admitted_injective (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (left right : Key)
    (leftAdmitted : Admitted verify publicKey message left) (rightAdmitted : Admitted verify publicKey message right)
    (same : realize signature left = realize signature right) : left = right := by
  exact (abstract_admitted verify publicKey message signature valid left leftAdmitted).symm.trans
    ((congrArg (abstract signature) same).trans (abstract_admitted verify publicKey message signature valid right rightAdmitted))

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.realize_abstract' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.realize_abstract

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.abstract_hidden' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.abstract_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.hidden_injective' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.hidden_injective

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.abstract_public' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.abstract_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.abstract_admitted' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.abstract_admitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.admitted_injective' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress.admitted_injective
