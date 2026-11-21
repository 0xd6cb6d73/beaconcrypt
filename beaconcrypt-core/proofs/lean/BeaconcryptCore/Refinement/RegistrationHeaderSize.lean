-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderCanonical
import BeaconcryptCore.Refinement.RegistrationSliceLength
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact all-capacity semantics of the original header sizing code. The proof retains the mutated one-cell counter when the argument cannot fit after its initial-byte charge. Canonical source widths give an exact success condition and nonwrapping remaining capacity. This private sizing theorem does not establish complete public codec closure. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderSize
open beaconcrypt_parse.cbordetveraux RegistrationHeaderCanonical

def cell (capacity : Usize) : Slice Usize := ⟨[capacity], by simp; scalar_tac⟩
theorem cell_length (capacity : Usize) : (cell capacity).length = 1 := rfl
theorem index_cell (capacity : Usize) : Slice.index_usize (cell capacity) 0#usize = .ok capacity := rfl
theorem update_cell (before after : Usize) :
    Slice.update (cell before) 0#usize after = .ok (cell after) := rfl
theorem index_mut_cell (capacity : Usize) :
    Slice.index_mut_usize (cell capacity) 0#usize = .ok (capacity, cell) := rfl

theorem sub_value (left right : Usize) (bound : right.val ≤ left.val) :
    (Usize.wrapping_sub left right).val = left.val - right.val := by
  rw [Usize.wrapping_sub_val_eq, UScalar.size_def]
  have limit := left.hBounds
  have rearrange : left.val + (2 ^ UScalarTy.Usize.numBits - right.val) =
      (left.val - right.val) + 2 ^ UScalarTy.Usize.numBits := by omega
  rw [rearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem wrapping_sub (left right : Usize) :
    core.num.Usize.wrapping_sub left right = .ok (Usize.wrapping_sub left right) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem short (major additional : U8) (argument : long_argument) (capacity : Usize)
    (bound : additional.val < 24) :
    size_header (header.mk (initial_byte_t.mk major additional) argument) (cell capacity) =
      if capacity < 1#usize then .ok (false, cell capacity)
      else .ok (true, cell (Usize.wrapping_sub capacity 1#usize)) := by
  have not24 : additional ≠ 24#u8 := by scalar_tac
  have not25 : additional ≠ 25#u8 := by scalar_tac
  have not26 : additional ≠ 26#u8 := by scalar_tac
  have not27 : additional ≠ 27#u8 := by scalar_tac
  simp only [size_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    index_cell, wrapping_sub, index_mut_cell, bind_tc_ok,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits,
    not24, not25, not26, not27, ↓reduceIte]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem long1 (major : U8) (argument : long_argument) (capacity : Usize) :
    size_header (header.mk (initial_byte_t.mk major 24#u8) argument) (cell capacity) =
      if capacity < 1#usize then .ok (false, cell capacity)
      else
        if Usize.wrapping_sub capacity 1#usize < 1#usize
        then .ok (false, cell (Usize.wrapping_sub capacity 1#usize))
        else .ok (true, cell (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize) 1#usize)) := by
  simp only [size_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    index_cell, wrapping_sub, index_mut_cell, bind_tc_ok,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits,
    ]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem long2 (major : U8) (argument : long_argument) (capacity : Usize) :
    size_header (header.mk (initial_byte_t.mk major 25#u8) argument) (cell capacity) =
      if capacity < 1#usize then .ok (false, cell capacity)
      else
        if Usize.wrapping_sub capacity 1#usize < 2#usize
        then .ok (false, cell (Usize.wrapping_sub capacity 1#usize))
        else .ok (true, cell (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize) 2#usize)) := by
  simp only [size_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    index_cell, wrapping_sub, index_mut_cell, bind_tc_ok,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits,
    ]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem long4 (major : U8) (argument : long_argument) (capacity : Usize) :
    size_header (header.mk (initial_byte_t.mk major 26#u8) argument) (cell capacity) =
      if capacity < 1#usize then .ok (false, cell capacity)
      else
        if Usize.wrapping_sub capacity 1#usize < 4#usize
        then .ok (false, cell (Usize.wrapping_sub capacity 1#usize))
        else .ok (true, cell (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize) 4#usize)) := by
  simp only [size_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    index_cell, wrapping_sub, index_mut_cell, bind_tc_ok,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits,
    ]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem long8 (major : U8) (argument : long_argument) (capacity : Usize) :
    size_header (header.mk (initial_byte_t.mk major 27#u8) argument) (cell capacity) =
      if capacity < 1#usize then .ok (false, cell capacity)
      else
        if Usize.wrapping_sub capacity 1#usize < 8#usize
        then .ok (false, cell (Usize.wrapping_sub capacity 1#usize))
        else .ok (true, cell (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize) 8#usize)) := by
  simp only [size_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    index_cell, wrapping_sub, index_mut_cell, bind_tc_ok,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits,
    ]
  rfl

def argumentCount (value : U64) : Usize :=
  if value.val < 24 then 0#usize else if value.val < 256 then 1#usize
  else if value.val < 65536 then 2#usize else if value.val < 4294967296 then 4#usize
  else 8#usize

/-- The actual counter retains the initial-byte charge if its argument does not fit. -/
def charge (capacity extra : Usize) : Bool × Slice Usize :=
  if capacity < 1#usize then (false, cell capacity)
  else if Usize.wrapping_sub capacity 1#usize < extra
  then (false, cell (Usize.wrapping_sub capacity 1#usize))
  else (true, cell (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize) extra))

theorem zero_charge (capacity : Usize) :
    charge capacity 0#usize =
      if capacity < 1#usize then (false, cell capacity)
      else (true, cell (Usize.wrapping_sub capacity 1#usize)) := by
  have noUnderflow (value : Usize) : ¬value < 0#usize := by scalar_tac
  have zeroSubtract (value : Usize) : Usize.wrapping_sub value 0#usize = value := by
    apply UScalar.eq_of_val_eq
    rw [sub_value _ _ (by scalar_tac)]
    rfl
  simp only [charge, noUnderflow, zeroSubtract, ↓reduceIte]

theorem normal_size (major : U8) (value : U64) (capacity : Usize) :
    size_header (normalHeader major value) (cell capacity) =
      .ok (charge capacity (argumentCount value)) := by
  unfold normalHeader argumentCount
  split_ifs with small byte word16 word32
  · rw [short major _ _ capacity (by
        rw [cast_value .U8 value (by scalar_tac)]
        exact small), zero_charge]
    split_ifs <;> rfl
  · rw [long1]
    unfold charge
    split_ifs <;> rfl
  · rw [long2]
    unfold charge
    split_ifs <;> rfl
  · rw [long4]
    unfold charge
    split_ifs <;> rfl
  · rw [long8]
    unfold charge
    split_ifs <;> rfl

theorem count_value (value : U64) :
    (writtenCount value).val = 1 + (argumentCount value).val := by
  unfold writtenCount argumentCount
  split_ifs <;> rfl

theorem charge_sufficient (capacity extra : Usize) (fit : 1 + extra.val ≤ capacity.val) :
    charge capacity extra =
      (true, cell (Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize) extra)) := by
  have initial : ¬capacity < 1#usize := by scalar_tac
  have subValue := sub_value capacity 1#usize (by scalar_tac)
  have argument : ¬Usize.wrapping_sub capacity 1#usize < extra := by scalar_tac
  simp only [charge, initial, argument, ↓reduceIte]

theorem charge_necessary (capacity extra : Usize) (fit : ¬1 + extra.val ≤ capacity.val) :
    (charge capacity extra).fst = false := by
  unfold charge
  split_ifs with initial argument
  · rfl
  · rfl
  · have subValue := sub_value capacity 1#usize (by scalar_tac)
    have contradiction : False := by scalar_tac
    exact contradiction.elim

theorem canonical (major : U8) (value : U64) (capacity : Usize) :
    (do let header ← sourceHeader major value; size_header header (cell capacity)) =
      .ok (charge capacity (argumentCount value)) := by
  rw [source_normal]
  simp only [bind_tc_ok, normal_size]

def remainingCapacity (capacity : Usize) (value : U64) : Usize :=
  Usize.wrapping_sub (Usize.wrapping_sub capacity 1#usize) (argumentCount value)

theorem remaining_value (capacity : Usize) (value : U64)
    (fit : (writtenCount value).val ≤ capacity.val) :
    (remainingCapacity capacity value).val = capacity.val - (writtenCount value).val := by
  have count := count_value value
  have initial := sub_value capacity 1#usize (by scalar_tac)
  have next := sub_value (Usize.wrapping_sub capacity 1#usize) (argumentCount value) (by scalar_tac)
  unfold remainingCapacity
  rw [next, initial]
  have one : (1#usize).val = 1 := by scalar_tac
  rw [one]
  omega

theorem normal_sufficient (major : U8) (value : U64) (capacity : Usize)
    (fit : (writtenCount value).val ≤ capacity.val) :
    size_header (normalHeader major value) (cell capacity) =
      .ok (true, cell (remainingCapacity capacity value)) := by
  rw [normal_size, charge_sufficient capacity (argumentCount value) (by
    rw [← count_value]
    exact fit)]
  rfl

theorem normal_success_iff (major : U8) (value : U64) (capacity : Usize) :
    (do let (success, _) ← size_header (normalHeader major value) (cell capacity)
        pure success) = .ok (decide ((writtenCount value).val ≤ capacity.val)) := by
  rw [normal_size]
  simp only [bind_tc_ok]
  by_cases fit : (writtenCount value).val ≤ capacity.val
  · rw [charge_sufficient capacity (argumentCount value) (by
      rw [← count_value]
      exact fit)]
    simp only [fit, decide_true]
    rfl
  · have failed := charge_necessary capacity (argumentCount value) (by
      rw [← count_value]
      exact fit)
    change RustM.ok (charge capacity (argumentCount value)).fst = _
    rw [failed]
    simp only [fit, decide_false]

end BeaconcryptCore.Refinement.RegistrationHeaderSize

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.cell_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.cell_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.index_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.index_cell

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.update_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.update_cell

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.index_mut_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.index_mut_cell

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.sub_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.sub_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.short

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.long1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.long1

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.long2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.long2

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.long4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.long4

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.long8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.long8

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.zero_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.zero_charge

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.normal_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.normal_size

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.count_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.count_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.charge_sufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.charge_sufficient

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.charge_necessary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.charge_necessary

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.canonical

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.remaining_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.remaining_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.normal_sufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.normal_sufficient

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderSize.normal_success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderSize.normal_success_iff
