-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSerializerFields
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact source split/callback/writeback stages used to compose the actual eight-field serializer. Stage construction retains the actual split and serializer equations plus the entire returned slice. Generic local callback facts are discharged by the actual field serializers; no complete codec law is assumed. -/
namespace BeaconcryptCore.Refinement.RegistrationSerializerStages
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical RegistrationSerializerFields
open RegistrationSerializerReachableSource

abbrev Work := Slice U8 → RustM (Usize × Slice U8)

structure Stage (work : Work) (before : Slice U8) (offset count : Usize) (payload : List U8) where
  front : Slice U8
  tail : Slice U8
  changed : Slice U8
  back : Slice U8 × Slice U8 → Slice U8
  splitSource : core.slice.Slice.split_at_mut before offset = .ok ((front, tail), back)
  runSource : work tail = .ok (count, changed)
  sameLength : (back (front, changed)).length = before.length
  bytes : (back (front, changed)).val =
    before.val.take offset.val ++ payload ++ before.val.drop (offset.val + count.val)

def Stage.after {work : Work} {before : Slice U8} {offset count : Usize} {payload : List U8}
    (stage : Stage work before offset count payload) : Slice U8 := stage.back (stage.front, stage.changed)

theorem stage (work : Work) (before : Slice U8) (offset count : Usize) (payload : List U8)
    (room : offset.val + count.val ≤ before.length)
    (run : ∀ tail, count.val ≤ tail.length → ∃ changed,
      work tail = .ok (count, changed) ∧ changed.length = tail.length ∧
      changed.val = payload ++ tail.val.drop count.val) :
    Nonempty (Stage work before offset count payload) := by
  obtain ⟨front, tail, back, splitSource, frontLength, tailLength, frontBytes, tailBytes, backLaw⟩ :=
    RegistrationByteCopy.split_mut_success before offset (by omega)
  obtain ⟨changed, actual, changedLength, changedBytes⟩ := run tail (by omega)
  have returned := backLaw front changed frontLength (by rw [changedLength]; exact tailLength)
  refine ⟨⟨front, tail, changed, back, splitSource, actual, returned.2, ?_⟩⟩
  rw [returned.1, frontBytes, changedBytes, tailBytes, List.drop_drop]
  simp only [List.append_assoc]

theorem uint_stage (other : OtherBranches) (before : Slice U8) (offset : Usize) (value : U64)
    (room : offset.val + (writtenCount value).val ≤ before.length) :
    Nonempty (Stage (@transport.serialize_uint (operations other) value) before offset (writtenCount value)
      (encodedBytes cbor_major_type_uint64 value)) := by
  apply stage _ _ _ _ _ room
  intro tail fit
  exact serialize_uint other tail value fit

theorem bytes_stage (other : OtherBranches) (before input : Slice U8) (offset : Usize)
    (room : offset.val + (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ before.length) :
    Nonempty (Stage (@transport.serialize_bstr (operations other) input) before offset (byteCount input)
      (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 input.len) ++ input.val)) := by
  have countValue := byte_count_value before input (by omega)
  apply stage _ _ _ _ _ (by rw [countValue]; omega)
  intro tail fit
  exact serialize_bstr other tail input (by rw [countValue] at fit; exact fit)

theorem add_usize (left right result : Usize) (value : left.val + right.val = result.val) :
    core.num.Usize.wrapping_add left right = .ok result := by
  change RustM.ok (Usize.wrapping_add left right) = _
  congr 1
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq, value, UScalar.size_def, Nat.mod_eq_of_lt result.hBounds]

theorem index_mut_singleton {S : Type} (value : S) :
    Array.index_mut_usize (Array.repeat 1#usize value) 0#usize =
      .ok (value, fun updated => Array.repeat 1#usize updated) := rfl

end BeaconcryptCore.Refinement.RegistrationSerializerStages

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerStages.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerStages.stage

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerStages.uint_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerStages.uint_stage

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerStages.bytes_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerStages.bytes_stage

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerStages.add_usize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerStages.add_usize

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerStages.index_mut_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerStages.index_mut_singleton
