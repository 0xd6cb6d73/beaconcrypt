-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSchemaViews
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Source byte prefixes determine a single actual iterator transition uniformly for every U64 iterator count. Original schema controllers may reread an item through a truncated iterator; these source-derived transitions preserve its value, borrowed payload and exact returned state across those count changes. -/
namespace BeaconcryptCore.Refinement.RegistrationSchemaTransitions
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderJump RegistrationSchemaIteratorReadback RegistrationSchemaViews

structure Transition (input : Slice U8) (raw : cbor_raw) where
  tail : Slice U8
  source : ∀ count, extraction_iterator_next_value (iterator input count) =
    .ok (raw, iterator tail (U64.wrapping_sub count 1#u64))

set_option backward.isDefEq.respectTransparency false in
theorem uint_transition (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    ∃ size, ∃ work : Transition input (uint size value), work.tail.val = rest := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_prefix input (writtenCount value)
    (encodedBytes cbor_major_type_uint64 value) rest contents (encoded_length _ value).symm
  obtain ⟨size, readFront⟩ := read_uint front value [] (by simpa using frontBytes)
  let work : Transition input (uint size value) := {
    tail := tail
    source := fun count => step input count _ front tail _
      (RegistrationFlatSkip.uint input value rest contents) splitInput readFront }
  exact ⟨size, work, tailBytes⟩

set_option backward.isDefEq.respectTransparency false in
theorem bytes_transition (input payload : Slice U8) (rest : List U8)
    (contents : input.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest) :
    ∃ size, ∃ work : Transition input (bytes size payload), work.tail.val = rest := by
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
  let work : Transition input (bytes size payload) := {
    tail := tail
    source := fun count => step input count _ front tail _
      (RegistrationFlatSkip.bytes input payload rest contents) splitInput readFront }
  exact ⟨size, work, tailBytes⟩
end BeaconcryptCore.Refinement.RegistrationSchemaTransitions

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaTransitions.uint_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaTransitions.uint_transition

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaTransitions.bytes_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaTransitions.bytes_transition
