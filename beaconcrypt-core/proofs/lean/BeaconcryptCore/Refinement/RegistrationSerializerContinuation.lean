-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSerializerFields
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationSerializerContinuation
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical RegistrationSerializerFields
open RegistrationSerializerReachableSource

variable [ops : RegistrationSerializerPrimitive.Operations]
theorem uint_continuation {A : Type} (value : U64) (out : Slice U8)
    (next : Usize → Slice U8 → RustM A) :
    (do
      let raw ← cbordetver.cbor_det_mk_int64 .UInt64 value
      let (result, changed) ← cbordetver.cbor_det_serialize raw out
      let count ← match result with
        | .None => .ok 0#usize
        | .Some count => .ok count
      next count changed) =
    (do let (count, changed) ← transport.serialize_uint value out; next count changed) := by
  unfold transport.serialize_uint
  simp only [transport.evercddl_uint_left, bind_tc_ok, bind_assoc]
  congr 1
  funext raw
  congr 1
  funext result
  rcases result with ⟨size, changed⟩
  cases size <;> rfl

end BeaconcryptCore.Refinement.RegistrationSerializerContinuation

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerContinuation.uint_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerContinuation.uint_continuation
