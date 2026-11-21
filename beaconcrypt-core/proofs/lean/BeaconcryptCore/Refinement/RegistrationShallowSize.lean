-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderSize
import BeaconcryptCore.Refinement.RegistrationStringFactory
import BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The actual UInt64 factory and prepared original ByteString factory compose with the original extracted shallow sizers. All capacities preserve exact source failure counter states. Success is equivalent to the actual header and payload fitting, and remaining capacity is nonwrapping. Generic public dispatch and complete codec closure remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationShallowSize
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical RegistrationHeaderSize

def sourceInt (capacity : Usize) (value : U64) : RustM (Bool × Slice Usize) := do
  let raw ← cbordetver.cbor_det_mk_int64 .UInt64 value
  match raw with
  | .CBOR_Case_Int integer => extraction_size_shallow_int integer (cell capacity)
  | _ => .fail .panic

set_option backward.isDefEq.respectTransparency false in
theorem source_int (capacity : Usize) (value : U64) :
    sourceInt capacity value = .ok (charge capacity (argumentCount value)) := by
  obtain ⟨size, raw⟩ := RegistrationConstructorGuards.mk_raw_exists value
  have argument : raw_uint64_as_argument cbor_major_type_uint64 { size := size, value := value } =
      .ok (normalHeader cbor_major_type_uint64 value) := by
    have result := source_normal cbor_major_type_uint64 value
    unfold sourceHeader at result
    rw [raw] at result
    simpa only [bind_tc_ok] using result
  unfold sourceInt
  simp only [cbordetver.cbor_det_mk_int64,
    cbordetver.cbor_det_int_kind.Insts.CoreCmpPartialEqcbor_det_int_kind.eq]
  rw [raw]
  simp
  unfold extraction_size_shallow_int cbor_raw_with_perm_get_header_d cbor_raw_get_header_d
  dsimp only
  rw [argument]
  simp only [bind_tc_ok]
  rw [normal_size]
  simp [RegistrationHeaderCanonicalRead.normal_major, cbor_major_type_uint64,
    cbor_major_type_byte_string, cbor_major_type_text_string, cbor_major_type_array,
    cbor_major_type_map, cbor_major_type_tagged, uncurry]
  cases result : charge capacity (argumentCount value) with
  | mk success out => cases success <;> rfl

/-- The source skips the payload charge after any failed header charge. -/
def chargePayload (headerResult : Bool × Slice Usize) (length : Usize) : RustM (Bool × Slice Usize) :=
  if headerResult.fst then do
    let available ← Slice.index_usize headerResult.snd 0#usize
    if available < length then .ok (false, headerResult.snd)
    else do
      let remaining ← core.num.Usize.wrapping_sub available length
      let updated ← Slice.update headerResult.snd 0#usize remaining
      .ok (true, updated)
  else .ok (false, headerResult.snd)

def sourceString (capacity : Usize) (input : Slice U8) : RustM (Bool × Slice Usize) := do
  let raw ← extraction_mk_byte_string input
  match raw with
  | .Some (.CBOR_Case_String string) => extraction_size_shallow_string string (cell capacity)
  | _ => .fail .panic

set_option backward.isDefEq.respectTransparency false in
theorem source_string (capacity : Usize) (input : Slice U8) :
    sourceString capacity input =
      chargePayload (charge capacity (argumentCount (UScalar.cast .U64 input.len))) input.len := by
  obtain ⟨size, factory, raw⟩ := RegistrationStringFactory.factory_exists input
  have argument : raw_uint64_as_argument cbor_major_type_byte_string
      (raw_uint64.mk size (UScalar.cast .U64 input.len)) =
      .ok (normalHeader cbor_major_type_byte_string (UScalar.cast .U64 input.len)) := by
    have result := source_normal cbor_major_type_byte_string (UScalar.cast .U64 input.len)
    unfold sourceHeader at result
    rw [raw] at result
    simpa only [bind_tc_ok] using result
  unfold sourceString
  rw [factory]
  simp only [bind_tc_ok]
  unfold extraction_size_shallow_string cbor_raw_with_perm_get_header_d cbor_raw_get_header_d
  dsimp only
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok, lift]
  rw [argument]
  simp only [bind_tc_ok]
  rw [normal_size]
  simp [RegistrationHeaderCanonicalRead.normal_major, uncurry, chargePayload]

theorem payload_sufficient (capacity length : Usize) (fit : length.val ≤ capacity.val) :
    chargePayload (true, cell capacity) length =
      .ok (true, cell (Usize.wrapping_sub capacity length)) := by
  have capacityFits : ¬capacity < length := by scalar_tac
  simp only [chargePayload, ↓reduceIte, index_cell, bind_tc_ok, capacityFits,
    core.num.Usize.wrapping_sub, update_cell]
  rfl

theorem int_sufficient (capacity : Usize) (value : U64)
    (fit : (writtenCount value).val ≤ capacity.val) :
    sourceInt capacity value = .ok (true, cell (remainingCapacity capacity value)) := by
  rw [source_int, charge_sufficient capacity (argumentCount value) (by
    rw [← count_value]
    exact fit)]
  rfl

theorem string_sufficient (capacity : Usize) (input : Slice U8)
    (fit : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ capacity.val) :
    sourceString capacity input = .ok (true, cell (Usize.wrapping_sub
      (remainingCapacity capacity (UScalar.cast .U64 input.len)) input.len)) := by
  have headerFit : (writtenCount (UScalar.cast .U64 input.len)).val ≤ capacity.val := by omega
  have remaining := remaining_value capacity (UScalar.cast .U64 input.len) headerFit
  unfold remainingCapacity at remaining
  rw [source_string, charge_sufficient capacity _ (by
    rw [← count_value]
    exact headerFit)]
  exact payload_sufficient _ input.len (by rw [Slice.len_val]; omega)

theorem payload_cell (capacity length : Usize) :
    chargePayload (true, cell capacity) length =
      if capacity < length then .ok (false, cell capacity)
      else .ok (true, cell (Usize.wrapping_sub capacity length)) := by
  simp only [chargePayload, ↓reduceIte, index_cell, bind_tc_ok]
  split_ifs
  · rfl
  · rfl

theorem payload_failed (result : Bool × Slice Usize) (length : Usize)
    (failed : result.fst = false) : chargePayload result length = .ok result := by
  rcases result with ⟨success, state⟩
  change success = false at failed
  subst success
  rfl

theorem int_success_iff (capacity : Usize) (value : U64) :
    (do let (success, _) ← sourceInt capacity value; pure success) =
      .ok (decide ((writtenCount value).val ≤ capacity.val)) := by
  have result := normal_success_iff cbor_major_type_uint64 value capacity
  rw [normal_size] at result
  rwa [source_int]

theorem string_remaining_value (capacity : Usize) (input : Slice U8)
    (fit : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ capacity.val) :
    (Usize.wrapping_sub (remainingCapacity capacity (UScalar.cast .U64 input.len)) input.len).val =
      capacity.val - ((writtenCount (UScalar.cast .U64 input.len)).val + input.length) := by
  have headerFit : (writtenCount (UScalar.cast .U64 input.len)).val ≤ capacity.val := by omega
  have afterHeader := remaining_value capacity (UScalar.cast .U64 input.len) headerFit
  have afterPayload := sub_value (remainingCapacity capacity (UScalar.cast .U64 input.len)) input.len
    (by rw [Slice.len_val]; omega)
  rw [afterPayload, afterHeader, Slice.len_val]
  omega

theorem string_success_iff (capacity : Usize) (input : Slice U8) :
    (do let (success, _) ← sourceString capacity input; pure success) =
      .ok (decide ((writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ capacity.val)) := by
  rw [source_string]
  by_cases headerFit : (writtenCount (UScalar.cast .U64 input.len)).val ≤ capacity.val
  · have afterHeader := remaining_value capacity (UScalar.cast .U64 input.len) headerFit
    unfold remainingCapacity at afterHeader
    rw [charge_sufficient capacity _ (by rw [← count_value]; exact headerFit), payload_cell]
    by_cases fits : Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize)
        (argumentCount (UScalar.cast .U64 input.len)) < input.len
    · have tooSmall : ¬(writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ capacity.val := by
        have : (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize)
          (argumentCount (UScalar.cast .U64 input.len))).val < input.len.val := by scalar_tac
        rw [Slice.len_val] at this
        omega
      simp only [fits, ↓reduceIte, bind_tc_ok, tooSmall, decide_false]
      rfl
    · have enough : (writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ capacity.val := by
        have : input.len.val ≤ (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize)
          (argumentCount (UScalar.cast .U64 input.len))).val := by scalar_tac
        rw [Slice.len_val] at this
        omega
      simp only [fits, ↓reduceIte, bind_tc_ok, enough, decide_true]
      rfl
  · have failed := charge_necessary capacity (argumentCount (UScalar.cast .U64 input.len))
      (by rw [← count_value]; exact headerFit)
    rw [payload_failed _ input.len failed]
    simp only [bind_tc_ok, failed]
    have tooSmall : ¬(writtenCount (UScalar.cast .U64 input.len)).val + input.length ≤ capacity.val := by omega
    simp only [tooSmall, decide_false]
    rfl

end BeaconcryptCore.Refinement.RegistrationShallowSize

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.source_int' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.source_int

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.source_string' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.source_string

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.payload_sufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.payload_sufficient

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.int_sufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.int_sufficient

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.string_sufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.string_sufficient

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.payload_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.payload_cell

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.payload_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.payload_failed

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.int_success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.int_success_iff

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.string_remaining_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.string_remaining_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowSize.string_success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowSize.string_success_iff
