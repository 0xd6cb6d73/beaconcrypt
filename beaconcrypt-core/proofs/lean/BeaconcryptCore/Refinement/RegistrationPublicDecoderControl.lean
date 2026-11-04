-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCodecControlNormalization
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.RegistrationValidatorExtraction.FunsExternal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPublicDecoderControl
variable {A B : Type} {m : Type → Type} [Monad m]
def emptyPattern (rest : List A) : Bool := match rest with
  | [] => true
  | _ :: _ => false

theorem empty_rest (rest : Slice A) :
    core.slice.Slice.is_empty rest = .ok (emptyPattern rest.val) := by
  rcases rest with ⟨rest, bound⟩
  cases rest <;> simp [core.slice.Slice.is_empty, core.slice.Slice.len, rust_primitives.slice.slice_length, emptyPattern]
  scalar_tac

theorem bind_scrutinee (work : m A) (next : A → m B) :
    (do let parsed ← work; next parsed) = (work >>= next) := rfl

theorem complete [LawfulMonad m] (rest : Slice A) (yes no : m B) :
    (if emptyPattern rest.val then yes else no) =
      (if rest.val = [] then yes else no) := by
  rcases rest with ⟨rest, bound⟩
  cases rest <;> rfl
private theorem copy_array (value : Array U8 6#usize) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      6#usize core.U8.Insts.CoreMarkerCopy (Std.Array.to_slice value) = .ok (.Ok value) := by
  obtain ⟨result, actual, facts⟩ := RegistrationInputs.copied_slice_exact 6#usize (Std.Array.to_slice value)
  cases result with
  | Err error => exact False.elim (facts (by simpa only [Std.Array.to_slice] using value.property))
  | Ok copied =>
      have same : copied = value := Subtype.ext facts.1
      simpa only [same] using actual

theorem preflight_array (input start : Slice U8) (fields : Array U8 6#usize) :
    beaconcrypt_parse.registration_validator_primitive.preflightSlice input start (Std.Array.to_slice fields) =
      beaconcrypt_parse.preflight input start fields := by
  unfold beaconcrypt_parse.registration_validator_primitive.preflightSlice
  rw [copy_array]
  rfl
end BeaconcryptCore.Refinement.RegistrationPublicDecoderControl

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.empty_rest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.empty_rest

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.bind_scrutinee' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.bind_scrutinee

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.complete

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.preflight_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderControl.preflight_array
