-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordChecked

/-! Replacing an opaque word by its mathematical literal realization changes no optional DH computation or input head. This gives concrete checked preparation and material equations across the actual descriptor evaluation, including private literal-input aliases. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message input eval literal)
open RegistrationNativeSecretWordChecked (Spec preparation material)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK Value : Type}

def reword (candidate : PqxdhKemIndCca.MlKemSharedSecret) (key : Key) : Key :=
  ⟨key.head, .literal (key.word.eval candidate)⟩

/-- Optional native DHs and the whole160-byte head ignore only the KEM word field. -/
theorem input_word (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (word : Word) :
    input joint dh seed scalar { message with kem := word } =
      (input joint dh seed scalar message).map (fun key => ⟨key.head, word⟩) := by
  have first : RegistrationNativeRelatedFamily.firstValue joint dh seed scalar
        (eval RegistrationNativeSecretWordMessage.zero { message with kem := word }) =
      RegistrationNativeRelatedFamily.firstValue joint dh seed scalar
        (eval RegistrationNativeSecretWordMessage.zero message) := by
    cases shape : message.third <;> simp only [eval, RegistrationNativeRelatedFamily.firstValue, shape]
  simp only [input, first, Option.bind_eq_bind, Option.pure_def, Option.map_bind]
  congr 1
  funext first
  simp only [Function.comp_apply, Option.map_bind, Option.map_some]

/-- Literal realization preserves the actual root descriptor's optional success and rewrites precisely its last32-byte coordinate. -/
theorem input_literal_eval (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) :
    input joint dh seed scalar (literal (eval candidate message)) =
      (input joint dh seed scalar message).map (reword candidate) := by
  have first : RegistrationNativeRelatedFamily.firstValue joint dh seed scalar
        (eval RegistrationNativeSecretWordMessage.zero (literal (eval candidate message))) =
      RegistrationNativeRelatedFamily.firstValue joint dh seed scalar
        (eval RegistrationNativeSecretWordMessage.zero message) := by
    cases shape : message.third <;> simp only [eval, literal, RegistrationNativeRelatedFamily.firstValue, shape]
  simp only [input, first, Option.bind_eq_bind, Option.pure_def, Option.map_bind]
  congr 1
  funext first
  simp only [Function.comp_apply, Option.map_bind, Option.map_some, literal, eval, reword]

/-- Both actual checked preparation paths make the same optional decision. -/
theorem valid_literal_eval (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) :
    (input joint dh seed scalar (literal (eval candidate message))).isSome =
      (input joint dh seed scalar message).isSome := by
  rw [input_literal_eval, Option.isSome_map]

/-- The actual protected table address and the off-protected native schedule are unchanged after literal realization. -/
theorem native_material (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) (key : Key) :
    RegistrationNativeSecretWordServiceSource.nativeMaterial source inside candidate (reword candidate key) =
      RegistrationNativeSecretWordServiceSource.nativeMaterial source inside candidate key := by
  rfl

/-- Checked demand restores the same actual material computation even when the retained word is an atom. -/
theorem material_literal_eval (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) :
    material (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar) (literal (eval candidate message)) =
      material source inside candidate (input joint dh seed scalar) message := by
  simp only [material, input_literal_eval, RegistrationNativeSecretWordMessage.eval_literal]
  congr 1
  funext _
  cases found : input joint dh seed scalar message with
  | none => rfl
  | some key => simp only [Option.map_some, native_material]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.input_word' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.input_word
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.input_literal_eval' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.input_literal_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.valid_literal_eval' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.valid_literal_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.native_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.native_material
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.material_literal_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput.material_literal_eval
