-- SPDX-License-Identifier: 0BSD
import CoreModels

/-! The selected standard `Option::as_deref` operation is missing from the pinned CoreModels cohort. Its interface borrows the present value, applies that value's actual Deref operation once, and preserves None. It neither copies nor allocates the opened byte buffer. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace CoreModels
def core.option.Option.as_deref {Self Target : Type}
    (deref : core.ops.deref.Deref Self Target) (value : core.option.Option Self) :
    RustM (core.option.Option Target) := do
  match value with
  | .None => ok .None
  | .Some value =>
    let borrowed ← deref.deref value
    ok (.Some borrowed)
end CoreModels

namespace BeaconcryptCore.Refinement.AdapterOptionDeref

theorem absent {Self Target : Type} (deref : core.ops.deref.Deref Self Target) :
    core.option.Option.as_deref deref .None = ok .None := rfl

theorem byte_vector (value : core.option.Option (alloc.vec.Vec U8)) :
    core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) value =
      ok value := by
  cases value <;> rfl

end BeaconcryptCore.Refinement.AdapterOptionDeref

/-- info: 'BeaconcryptCore.Refinement.AdapterOptionDeref.absent' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterOptionDeref.absent
/-- info: 'BeaconcryptCore.Refinement.AdapterOptionDeref.byte_vector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterOptionDeref.byte_vector
