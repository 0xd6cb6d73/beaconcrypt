-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationArrayReadback
import BeaconcryptCore.Refinement.RegistrationStringReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual serialized-array iterator steps compose source skip, bounded splitting, original cbor_read and exact mutable singleton writeback. Canonical unsigned integers and byte strings reconstruct their original value or borrowed payload, with source-derived size and decremented source iterator count. Empty, length and truncation facts are the actual source operations. -/
namespace BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderCanonicalRead RegistrationHeaderJump RegistrationFlatHeader
open RegistrationCodecArraySingleton RegistrationFlatSkip

abbrev Iterator := bcExtractedToken63626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f726177

def slot {A : Type} (value : A) : Slice A := ⟨[value], by simp; scalar_tac⟩
def iterator (bytes : Slice U8) (count : U64) : Iterator := .CBOR_Raw_Iterator_Serialized { s := bytes, len := count }

theorem index_slot {A : Type} (value : A) : Slice.index_usize (slot value) 0#usize = .ok value := rfl
theorem update_slot {A : Type} (before after : A) : Slice.update (slot before) 0#usize after = .ok (slot after) := rfl

theorem sub_u64 (left right : U64) : core.num.U64.wrapping_sub left right = .ok (U64.wrapping_sub left right) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem step (input : Slice U8) (count : U64) (offset : Usize) (front tail : Slice U8) (raw : cbor_raw)
    (skipped : jump_raw_data_item input 0#usize = .ok offset)
    (splitInput : core.slice.Slice.split_at input offset = .ok (front, tail))
    (readFront : cbor_read front = .ok raw) :
    extraction_iterator_next_value (iterator input count) =
      .ok (raw, iterator tail (U64.wrapping_sub count 1#u64)) := by
  simp only [extraction_iterator_next_value, show Array.repeat 1#usize = @pack Iterator from rfl,
    Array.to_slice_mut, lift, bind_tc_ok, uncurry]
  have toSlice : Array.to_slice (pack (iterator input count)) = slot (iterator input count) := rfl
  have copyBack (before after : Iterator) : Array.from_slice (pack before) (slot after) = pack after := rfl
  rw [toSlice]
  simp only [cbordetver.cbor_det_array_iterator_next, cbor_array_iterator_next, index_slot,
    iterator, cbor_serialized_array_iterator_next, skipped, bind_tc_ok, splitInput, uncurry,
    readFront, sub_u64, update_slot, copyBack, index_pack]

set_option backward.isDefEq.respectTransparency false in
theorem read_uint (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    ∃ size, cbor_read input = .ok (.CBOR_Case_Int (cbor_int.mk cbor_major_type_uint64 size value)) := by
  obtain ⟨size, source⟩ := RegistrationConstructorGuards.mk_raw_exists value
  refine ⟨size, ?_⟩
  rw [RegistrationHeaderCanonicalRead.read_uint input value rest contents]
  simp only [cbordetver.cbor_det_mk_int64,
    cbordetver.cbor_det_int_kind.Insts.CoreCmpPartialEqcbor_det_int_kind.eq, source, bind_tc_ok, decide_true, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem read_bytes (input payload : Slice U8)
    (contents : input.val = encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) :
    ∃ size, cbor_read input = .ok (.CBOR_Case_String (cbor_string.mk cbor_major_type_byte_string size payload)) := by
  obtain ⟨size, source, _⟩ := RegistrationStringFactory.factory_exists payload
  have result := RegistrationStringReadback.read_factory input payload contents
  rw [source] at result
  refine ⟨size, ?_⟩
  cases actual : cbor_read input with
  | ok raw =>
    simp only [actual, bind_tc_ok, ok.injEq,
      cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177.Some.injEq] at result
    rw [result]
  | fail error => simp [actual] at result
  | div => simp [actual] at result

set_option backward.isDefEq.respectTransparency false in
theorem next_uint (input : Slice U8) (count value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    ∃ size tail, tail.val = rest ∧
      extraction_iterator_next_value (iterator input count) =
        .ok (.CBOR_Case_Int (cbor_int.mk cbor_major_type_uint64 size value),
          iterator tail (U64.wrapping_sub count 1#u64)) := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_prefix input (writtenCount value)
    (encodedBytes cbor_major_type_uint64 value) rest contents (encoded_length _ value).symm
  obtain ⟨size, readFront⟩ := read_uint front value [] (by simpa using frontBytes)
  exact ⟨size, tail, tailBytes, step input count _ front tail _ (RegistrationFlatSkip.uint input value rest contents) splitInput readFront⟩

set_option backward.isDefEq.respectTransparency false in
theorem next_bytes (input payload : Slice U8) (count : U64) (rest : List U8)
    (contents : input.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest) :
    ∃ size tail, tail.val = rest ∧
      extraction_iterator_next_value (iterator input count) =
        .ok (.CBOR_Case_String (cbor_string.mk cbor_major_type_byte_string size payload),
          iterator tail (U64.wrapping_sub count 1#u64)) := by
  have fit : (writtenCount (UScalar.cast .U64 payload.len)).val + payload.length ≤ input.length := by
    have lengths := congrArg List.length contents
    simp only [List.length_append, encoded_length] at lengths
    change input.length = (writtenCount (UScalar.cast .U64 payload.len)).val + payload.length + rest.length at lengths
    omega
  have sizeValue := RegistrationSerializerFields.byte_count_value input payload fit
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_prefix input
    (RegistrationSerializerFields.byteCount payload)
    (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val)
    rest contents (by rw [sizeValue, List.length_append, encoded_length])
  obtain ⟨size, readFront⟩ := read_bytes front payload frontBytes
  exact ⟨size, tail, tailBytes, step input count _ front tail _ (RegistrationFlatSkip.bytes input payload rest contents) splitInput readFront⟩

theorem is_empty (input : Slice U8) (count : U64) :
    cbordetver.cbor_det_array_iterator_is_empty (iterator input count) = .ok (decide (count = 0#u64)) := rfl

theorem length (input : Slice U8) (count : U64) :
    cbordetver.cbor_det_array_iterator_length (iterator input count) = .ok count := rfl

theorem truncate (input : Slice U8) (before after : U64) :
    cbordetver.cbor_det_array_iterator_truncate (iterator input before) after = .ok (iterator input after) := rfl

end BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.index_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.index_slot

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.update_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.update_slot

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.sub_u64' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.sub_u64

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.step

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.read_uint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.read_uint

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.read_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.read_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.next_uint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.next_uint

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.next_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.next_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.is_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.is_empty

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.length

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.truncate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback.truncate
