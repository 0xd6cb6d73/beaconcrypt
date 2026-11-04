-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationPrimitiveExtraction.Funs

set_option autoImplicit false
set_option warningAsError true

/-! Exact source constructor and header-tag facts. These guards justify selecting
shallow Int/String branches; they are not complete public byte-codec laws. -/

namespace BeaconcryptCore.Refinement.RegistrationConstructorGuards
open Aeneas.Std
open beaconcrypt_parse
open cbordetveraux

theorem mk_raw_value (value : U64) :
    (do let raw ← mk_raw_uint64 value; pure raw.value) = (RustM.ok value) := by
  simp only [mk_raw_uint64, max_simple_value_additional_info, lift, bind_tc_ok]
  repeat' first | split | rfl

theorem mk_raw_exists (value : U64) :
    ∃ size, mk_raw_uint64 value = .ok { size := size, value := value } := by
  simp only [mk_raw_uint64, max_simple_value_additional_info, lift, bind_tc_ok]
  repeat' first | split | exact ⟨_, rfl⟩

theorem argument_major (major : U8) (value : raw_uint64) :
    (do let header ← raw_uint64_as_argument major value; pure header.fst.major_type) =
      RustM.ok major := by
  simp only [raw_uint64_as_argument, lift, bind_tc_ok]
  repeat' first | split | rfl

theorem mk_uint (value : U64) :
    ∃ size, cbordetver.cbor_det_mk_int64 .UInt64 value =
      .ok (.CBOR_Case_Int {
        cbor_int_type := cbor_major_type_uint64
        cbor_int_size := size
        cbor_int_value := value }) := by
  obtain ⟨size, hsize⟩ := mk_raw_exists value
  refine ⟨size, ?_⟩
  simp only [cbordetver.cbor_det_mk_int64,
    cbordetver.cbor_det_int_kind.Insts.CoreCmpPartialEqcbor_det_int_kind.eq]
  change (do let raw ← mk_raw_uint64 value; pure (cbor_raw.CBOR_Case_Int
    { cbor_int_type := cbor_major_type_uint64, cbor_int_size := raw.size, cbor_int_value := raw.value })) = _
  rw [hsize]
  rfl

theorem int_not_deep (value : cbor_int) :
    compute_deep (.CBOR_Case_Int value) = .ok false := rfl

theorem string_not_deep (value : cbor_string) :
    compute_deep (.CBOR_Case_String value) = .ok false := rfl

/-- The original deep/shallow guard, with both effectful branches left arbitrary. -/
def dispatch {A : Type} (value : cbor_raw)
    (deep shallow : Unit → RustM A) : RustM A := do
  let isDeep ← compute_deep value
  if isDeep then deep () else shallow ()

theorem int_dispatch {A : Type} (value : cbor_int)
    (deep shallow : Unit → RustM A) :
    dispatch (.CBOR_Case_Int value) deep shallow = shallow () := rfl

theorem string_dispatch {A : Type} (value : cbor_string)
    (deep shallow : Unit → RustM A) :
    dispatch (.CBOR_Case_String value) deep shallow = shallow () := rfl

end BeaconcryptCore.Refinement.RegistrationConstructorGuards

/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.mk_raw_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.mk_raw_value
/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.mk_raw_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.mk_raw_exists
/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.argument_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.argument_major
/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.mk_uint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.mk_uint
/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.int_not_deep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.int_not_deep
/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.string_not_deep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.string_not_deep
/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.int_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.int_dispatch
/-- info: 'BeaconcryptCore.Refinement.RegistrationConstructorGuards.string_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationConstructorGuards.string_dispatch
