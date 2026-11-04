-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInputs

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

/-! The seal dispatcher's literal sixteen-byte tag adaptation uses the actual standard-library slice-to-array conversion. The existing source reconstruction proof follows the exact indexing closure and `array_from_fn`; its specialization recovers the same array, while a different slice length takes the actual error branch. No primitive, parser or codec law is assumed. -/

namespace BeaconcryptCore.Refinement.AdapterSealTag

theorem try_from_array (tag : Array U8 16#usize) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      16#usize core.U8.Insts.CoreMarkerCopy (Array.to_slice tag) = .ok (.Ok tag) := by
  obtain ⟨result, run, exactBytes⟩ := RegistrationInputs.copied_slice_exact 16#usize (Array.to_slice tag)
  cases result with
  | Ok output =>
    have same : output = tag := Subtype.ext exactBytes.1
    simpa only [same] using run
  | Err error =>
    exact False.elim (exactBytes tag.property)

theorem wrong_length (bytes : Slice U8) (different : bytes.length ≠ 16) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      16#usize core.U8.Insts.CoreMarkerCopy bytes = .ok (.Err ()) := by
  simp [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
    rust_primitives.slice.slice_length, UScalar.eq_equiv, different]

end BeaconcryptCore.Refinement.AdapterSealTag

/-- info: 'BeaconcryptCore.Refinement.AdapterSealTag.try_from_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealTag.try_from_array

/-- info: 'BeaconcryptCore.Refinement.AdapterSealTag.wrong_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealTag.wrong_length
