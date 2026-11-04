-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationArrayExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Source array-index eta correspondence with actual pure standard slice
length and wrapping arithmetic. The original expression retains both length
reads; the extracted scalar helper is compared on the same current slice.
No arbitrary-effect caching, rotation or complete codec law is assumed. -/
namespace BeaconcryptCore.Refinement.RegistrationArrayIndex
open beaconcrypt_parse.cbordetveraux

theorem slice_len (input : Slice U8) : core.slice.Slice.len input = .ok input.len := rfl

theorem wrapping_sub (left right : Usize) :
    core.num.Usize.wrapping_sub left right = .ok (Usize.wrapping_sub left right) := rfl

theorem wrapping_add (left right : Usize) :
    core.num.Usize.wrapping_add left right = .ok (Usize.wrapping_add left right) := rfl

/-- Exact original generated index expression, retaining both slice-length reads. -/
def originalIndex (input : Slice U8) (index offset : Usize) : RustM Usize := do
  let relative ← core.num.Usize.wrapping_sub index 0#usize
  let length ← core.slice.Slice.len input
  let remaining ← core.num.Usize.wrapping_sub length offset
  if relative >= remaining then
    let repeatedLength ← core.slice.Slice.len input
    let repeatedRemaining ← core.num.Usize.wrapping_sub repeatedLength offset
    core.num.Usize.wrapping_sub index repeatedRemaining
  else
    let shift ← core.num.Usize.wrapping_sub offset 0#usize
    core.num.Usize.wrapping_add index shift

theorem index_eta (input : Slice U8) (index offset : Usize) :
    originalIndex input index offset = (do
      let length ← core.slice.Slice.len input
      extraction_rotation_index_1 index length offset) := by
  simp only [originalIndex, extraction_rotation_index_1, slice_len,
    wrapping_sub, wrapping_add, bind_tc_ok]

end BeaconcryptCore.Refinement.RegistrationArrayIndex

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayIndex.slice_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayIndex.slice_len
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayIndex.wrapping_sub' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayIndex.wrapping_sub
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayIndex.wrapping_add' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayIndex.wrapping_add
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayIndex.index_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayIndex.index_eta
