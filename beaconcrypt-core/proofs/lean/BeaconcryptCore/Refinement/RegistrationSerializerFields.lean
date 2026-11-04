-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSerializerReachableSource
import BeaconcryptCore.Refinement.RegistrationCodecArraySingleton
import BeaconcryptCore.Refinement.RegistrationArraySourceBytes
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact source cbor_size singleton-array copyback and original public field serializer composition. The source factory, all-capacity sizer, bounded split, original shallow body and full slice writeback derive field bytes, suffix and length with no desired codec-law premise. Actual generated field helpers reduce to the public byte-string field serializer when their original bound checks pass. -/
namespace BeaconcryptCore.Refinement.RegistrationSerializerFields
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical RegistrationHeaderSize
open RegistrationSerializerReachableSource

theorem array_cell (value : Usize) :
    (Array.to_slice_mut (Array.repeat 1#usize value)).fst = cell value := rfl

theorem array_back (before after : Usize) :
    (Array.to_slice_mut (Array.repeat 1#usize before)).snd (cell after) = Array.repeat 1#usize after := rfl

variable [ops : RegistrationSerializerPrimitive.Operations]

theorem size_success (value : cbor_raw) (capacity remaining : Usize)
    (sized : ops.sizeRaw value (cell capacity) = .ok (true, cell remaining)) :
    cbor_size value capacity = .ok (Usize.wrapping_sub capacity remaining) := by
  unfold cbor_size
  simp only [Array.to_slice_mut, lift, bind_tc_ok]
  change (do
    let (success, state) ← ops.sizeRaw value (cell capacity)
    if success then do
      let leftover ← Array.index_usize ((Array.to_slice_mut (Array.repeat 1#usize capacity)).snd state) 0#usize
      core.num.Usize.wrapping_sub capacity leftover
    else .ok 0#usize) = _
  rw [sized]
  simp only [bind_tc_ok, ↓reduceIte, array_back]
  rfl

theorem size_failed (value : cbor_raw) (capacity : Usize) (state : Slice Usize)
    (sized : ops.sizeRaw value (cell capacity) = .ok (false, state)) :
    cbor_size value capacity = .ok 0#usize := by
  unfold cbor_size
  simp only [Array.to_slice_mut, lift, bind_tc_ok]
  change (do
    let (success, state) ← ops.sizeRaw value (cell capacity)
    if success then do
      let leftover ← Array.index_usize ((Array.to_slice_mut (Array.repeat 1#usize capacity)).snd state) 0#usize
      core.num.Usize.wrapping_sub capacity leftover
    else .ok 0#usize) = _
  rw [sized]
  rfl

omit ops in
theorem uint_measure (other : OtherBranches) (capacity : Usize) (value : U64) (raw : cbor_raw)
    (factory : cbordetver.cbor_det_mk_int64 .UInt64 value = .ok raw)
    (fit : (writtenCount value).val ≤ capacity.val) :
    @cbor_size (operations other) raw capacity = .ok (writtenCount value) := by
  let _ : RegistrationSerializerPrimitive.Operations := operations other
  have sized := RegistrationShallowSize.int_sufficient capacity value fit
  rw [← uint_size_source other capacity value] at sized
  unfold RegistrationSerializerReachableSource.sizeUInt at sized
  rw [factory] at sized
  simp only [bind_tc_ok] at sized
  have actual := size_success raw capacity (remainingCapacity capacity value) sized
  have remaining := remaining_value capacity value fit
  have subtract : Usize.wrapping_sub capacity (remainingCapacity capacity value) = writtenCount value := by
    apply UScalar.eq_of_val_eq
    rw [sub_value _ _ (by scalar_tac), remaining]
    omega
  rwa [subtract] at actual

omit ops in
theorem bytes_measure (other : OtherBranches) (capacity : Usize) (input : Slice U8) (raw : cbor_raw)
    (factory : extraction_mk_byte_string input = .ok (.Some raw))
    (fit : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ capacity.val) :
    @cbor_size (operations other) raw capacity = .ok
      (Usize.wrapping_add (writtenCount (UScalar.cast .U64 input.len)) input.len) := by
  let _ : RegistrationSerializerPrimitive.Operations := operations other
  have sized := RegistrationShallowSize.string_sufficient capacity input fit
  rw [← bytes_size_source other capacity input] at sized
  unfold RegistrationSerializerReachableSource.sizeBytes at sized
  rw [byte_factory, factory] at sized
  simp only [bind_tc_ok] at sized
  have actual := size_success raw capacity _ sized
  have remaining := RegistrationShallowSize.string_remaining_value capacity input fit
  have sumValue : (Usize.wrapping_add (writtenCount (UScalar.cast .U64 input.len)) input.len).val =
      (writtenCount (UScalar.cast .U64 input.len)).val + input.length := by
    rw [Usize.wrapping_add_val_eq, Slice.len_val, UScalar.size_def]
    apply Nat.mod_eq_of_lt
    have bound := capacity.hBounds
    omega
  have subtract : Usize.wrapping_sub capacity (Usize.wrapping_sub
      (remainingCapacity capacity (UScalar.cast .U64 input.len)) input.len) =
      Usize.wrapping_add (writtenCount (UScalar.cast .U64 input.len)) input.len := by
    apply UScalar.eq_of_val_eq
    rw [sub_value _ _ (by scalar_tac), remaining, sumValue]
    omega
  rwa [subtract] at actual

omit ops in
theorem header_positive (value : U64) : 0#usize < writtenCount value := by
  unfold writtenCount
  split_ifs <;> scalar_tac

omit ops in
theorem uint_serialize_raw (other : OtherBranches) (out : Slice U8) (value : U64) (raw : cbor_raw)
    (factory : cbordetver.cbor_det_mk_int64 .UInt64 value = .ok raw)
    (fit : (writtenCount value).val ≤ out.length) :
    ∃ after, @cbordetver.cbor_det_serialize (operations other) raw out =
        .ok (.Some (writtenCount value), after) ∧
      after.length = out.length ∧
      after.val = encodedBytes cbor_major_type_uint64 value ++ out.val.drop (writtenCount value).val := by
  let _ : RegistrationSerializerPrimitive.Operations := operations other
  obtain ⟨front, tail, back, splitSource, frontLength, tailLength, frontBytes, tailBytes, backLaw⟩ :=
    RegistrationByteCopy.split_mut_success out (writtenCount value) fit
  have measured := uint_measure other out.len value raw factory (by simpa only [Slice.len_val] using fit)
  have serialized := RegistrationShallowUInt.source_serialize front value (by change (writtenCount value).val ≤ front.length; omega)
  rw [← uint_serialize_source other front value] at serialized
  unfold RegistrationSerializerReachableSource.serializeUInt at serialized
  rw [factory] at serialized
  simp only [bind_tc_ok] at serialized
  have resultLength := written_length front cbor_major_type_uint64 value
  have resultBytes := written_bytes front cbor_major_type_uint64 value (by change (writtenCount value).val ≤ front.length; omega)
  have updated := backLaw (written front cbor_major_type_uint64 value) tail
    (resultLength.trans frontLength) tailLength
  refine ⟨back (written front cbor_major_type_uint64 value, tail), ?_, updated.2, ?_⟩
  · unfold cbordetver.cbor_det_serialize
    simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
    rw [measured]
    simp only [bind_tc_ok, header_positive, ↓reduceIte]
    rw [splitSource]
    simp only [bind_tc_ok, uncurry, cbor_serialize, registration_serializer_primitive.serializeRaw]
    rw [serialized]
    rfl
  · rw [updated.1, resultBytes, tailBytes]
    have empty : front.val.drop (writtenCount value).val = [] := by
      have length : front.val.length = (writtenCount value).val := frontLength
      rw [← length, List.drop_length]
    rw [empty, List.append_nil]

def byteCount (input : Slice U8) : Usize :=
  Usize.wrapping_add (writtenCount (UScalar.cast .U64 input.len)) input.len

omit ops in
theorem byte_count_value (out input : Slice U8)
    (fit : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ out.length) :
    (byteCount input).val = (writtenCount (UScalar.cast .U64 input.len)).val + input.length := by
  exact RegistrationShallowString.cursor_value out input fit

omit ops in
theorem bytes_serialize_raw (other : OtherBranches) (out input : Slice U8) (raw : cbor_raw)
    (factory : extraction_mk_byte_string input = .ok (.Some raw))
    (fit : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ out.length) :
    ∃ after, @cbordetver.cbor_det_serialize (operations other) raw out =
        .ok (.Some (byteCount input), after) ∧
      after.length = out.length ∧
      after.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 input.len) ++ input.val) ++
        out.val.drop (byteCount input).val := by
  let _ : RegistrationSerializerPrimitive.Operations := operations other
  have countValue := byte_count_value out input fit
  obtain ⟨front, tail, back, splitSource, frontLength, tailLength, frontBytes, tailBytes, backLaw⟩ :=
    RegistrationByteCopy.split_mut_success out (byteCount input) (by rw [countValue]; exact fit)
  have measured := bytes_measure other out.len input raw factory (by simpa only [Slice.len_val] using fit)
  change cbor_size raw out.len = .ok (byteCount input) at measured
  have frontFit : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ front.length := by
    rw [frontLength, countValue]
  obtain ⟨changed, serialized, resultLength, resultBytes, cursorValue⟩ :=
    RegistrationShallowString.codec front input frontFit
  rw [← bytes_serialize_source other front input] at serialized
  unfold RegistrationSerializerReachableSource.serializeBytes at serialized
  rw [byte_factory, factory] at serialized
  simp only [bind_tc_ok] at serialized
  have updated := backLaw changed tail (resultLength.trans frontLength) tailLength
  refine ⟨back (changed, tail), ?_, updated.2, ?_⟩
  · unfold cbordetver.cbor_det_serialize
    simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
    rw [measured]
    have positive : 0#usize < byteCount input := by
      have headerPositive := header_positive (UScalar.cast .U64 input.len)
      scalar_tac
    change (if byteCount input > 0#usize then _ else _) = _
    simp only [positive, ↓reduceIte]
    rw [splitSource]
    simp only [bind_tc_ok, uncurry, cbor_serialize, registration_serializer_primitive.serializeRaw]
    rw [serialized]
    rfl
  · rw [updated.1, resultBytes, tailBytes]
    have empty : front.val.drop ((writtenCount (UScalar.cast .U64 input.len)).val + input.length) = [] := by
      have length : front.val.length = (writtenCount (UScalar.cast .U64 input.len)).val + input.length :=
        frontLength.trans countValue
      rw [← length, List.drop_length]
    rw [empty, List.append_nil]

omit ops in
theorem usize_cast (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  change value.val < 18446744073709551616
  have bound := value.hBounds
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [UScalarTy.numBits, bits] at bound <;> omega

omit ops in
theorem usize_lte_u64 (value : Usize) (bound : U64) :
    sizet_lte_u64 value bound = .ok (decide (value.val ≤ bound.val)) := by
  have small := RegistrationStringFactory.fourth_bound value
  have notLarge : ¬RegistrationStringFactory.quotient (RegistrationStringFactory.quotient
      (RegistrationStringFactory.quotient (RegistrationStringFactory.quotient value))) >= 16#usize := by scalar_tac
  simp only [sizet_lte_u64, RegistrationStringFactory.divide, bind_tc_ok, notLarge, ↓reduceIte, lift]
  change RustM.ok (decide ((UScalar.cast .U64 value).val ≤ bound.val)) = _
  rw [usize_cast]

omit ops in
theorem u64_lte_usize (bound : U64) (value : Usize) :
    u64_lte_sizet bound value = .ok (decide (bound.val ≤ value.val)) := by
  have small := RegistrationStringFactory.fourth_bound value
  have notLarge : ¬RegistrationStringFactory.quotient (RegistrationStringFactory.quotient
      (RegistrationStringFactory.quotient (RegistrationStringFactory.quotient value))) >= 16#usize := by scalar_tac
  simp only [u64_lte_sizet, RegistrationStringFactory.divide, bind_tc_ok, notLarge, ↓reduceIte, lift]
  change RustM.ok (decide (bound.val ≤ (UScalar.cast .U64 value).val)) = _
  rw [usize_cast]

omit ops in
theorem serialize_uint (other : OtherBranches) (out : Slice U8) (value : U64)
    (fit : (writtenCount value).val ≤ out.length) :
    ∃ after, @transport.serialize_uint (operations other) value out = .ok (writtenCount value, after) ∧
      after.length = out.length ∧
      after.val = encodedBytes cbor_major_type_uint64 value ++ out.val.drop (writtenCount value).val := by
  obtain ⟨size, factory⟩ := RegistrationConstructorGuards.mk_uint value
  obtain ⟨after, serialized, sameLength, bytes⟩ := uint_serialize_raw other out value _ factory fit
  refine ⟨after, ?_, sameLength, bytes⟩
  unfold transport.serialize_uint
  simp only [transport.evercddl_uint_left, bind_tc_ok]
  rw [factory]
  simp only [bind_tc_ok]
  rw [serialized]
  rfl

omit ops in
theorem serialize_bstr (other : OtherBranches) (out input : Slice U8)
    (fit : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ out.length) :
    ∃ after, @transport.serialize_bstr (operations other) input out = .ok (byteCount input, after) ∧
      after.length = out.length ∧
      after.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 input.len) ++ input.val) ++
        out.val.drop (byteCount input).val := by
  obtain ⟨size, factory, _⟩ := RegistrationStringFactory.factory_exists input
  obtain ⟨after, serialized, sameLength, bytes⟩ := bytes_serialize_raw other out input _ factory fit
  refine ⟨after, ?_, sameLength, bytes⟩
  have bound : input.len.val ≤ (18446744073709551615#u64).val := by
    have lengthFits := usize_cast input.len
    have bounded := (UScalar.cast .U64 input.len).hBounds
    rw [lengthFits] at bounded
    change input.len.val ≤ 18446744073709551615
    change input.len.val < 18446744073709551616 at bounded
    omega
  unfold transport.serialize_bstr
  simp only [transport.bstr_left, bind_tc_ok, core.slice.Slice.len,
    rust_primitives.slice.slice_length, usize_lte_u64, bound, decide_true, ↓reduceIte]
  change (do let raw ← extraction_mk_byte_string input; _) = _
  rw [factory]
  simp only [bind_tc_ok]
  rw [serialized]
  rfl

theorem initkex_field_0 (input out : Slice U8) :
    transport.extraction_serialize_initkex_size_0 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_initkex_size_0, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem initkex_field_1 (input out : Slice U8) :
    transport.extraction_serialize_initkex_size_1 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_initkex_size_1, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem initkex_field_2 (input out : Slice U8) :
    transport.extraction_serialize_initkex_size_2 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_initkex_size_2, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem initkex_field_3 (input out : Slice U8) :
    transport.extraction_serialize_initkex_size_3 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_initkex_size_3, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem initkex_field_4 (input out : Slice U8) :
    transport.extraction_serialize_initkex_size_4 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_initkex_size_4, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem initkex_field_5 (input out : Slice U8) :
    transport.extraction_serialize_initkex_size_5 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_initkex_size_5, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem kexresponse_field_0 (input out : Slice U8) :
    transport.extraction_serialize_kexresponse_size_0 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_kexresponse_size_0, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem kexresponse_field_1 (input out : Slice U8) :
    transport.extraction_serialize_kexresponse_size_1 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_kexresponse_size_1, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem kexresponse_field_2 (input out : Slice U8) :
    transport.extraction_serialize_kexresponse_size_2 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_kexresponse_size_2, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

theorem kexresponse_field_3 (input out : Slice U8) :
    transport.extraction_serialize_kexresponse_size_3 input out true true =
      transport.serialize_bstr input out := by
  simp only [transport.extraction_serialize_kexresponse_size_3, transport.serialize_bstr,
    transport.bstr_left, bind_tc_ok, cbor_major_type_byte_string, ↓reduceIte]

end BeaconcryptCore.Refinement.RegistrationSerializerFields

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.array_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.array_cell

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.array_back' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.array_back

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.size_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.size_success

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.size_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.size_failed

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.uint_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.uint_measure

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.bytes_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.bytes_measure

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.header_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.header_positive

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.uint_serialize_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.uint_serialize_raw

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.byte_count_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.byte_count_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.bytes_serialize_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.bytes_serialize_raw

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.usize_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.usize_cast

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.usize_lte_u64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.usize_lte_u64

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.u64_lte_usize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.u64_lte_usize

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.serialize_uint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.serialize_uint

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.serialize_bstr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.serialize_bstr

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_0

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_1

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_2

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_3

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_4

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.initkex_field_5

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_0

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_1

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_2

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFields.kexresponse_field_3
