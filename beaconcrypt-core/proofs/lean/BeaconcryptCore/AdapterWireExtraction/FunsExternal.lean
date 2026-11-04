-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterWireExtraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterWirePrimitive
/-- Explicit specialized mutable-argument backward result omitted by the generic CoreModels FnOnce signature. This is a type interface, with no serialization law. -/
structure Serializer (T : Type) where
  call_once : T → Slice U8 → RustM (Usize × Slice U8)
/-- The selected std reservation leaf retains its ordinary error branch and returned vector. Allocator state is supplied by the request interpreter. -/
class Operations where
  ReserveError : Type
  reserve : alloc.vec.Vec U8 → Usize → RustM (core.result.Result Unit ReserveError × alloc.vec.Vec U8)
end BeaconcryptCore.Refinement.AdapterWirePrimitive
namespace CoreModels
/-- Explicit std model missing from this pinned CoreModels revision. Only the selected byte-vector reservation is modeled. -/
def alloc.vec.Vec.try_reserve_exact [operations : BeaconcryptCore.Refinement.AdapterWirePrimitive.Operations]
    (before : alloc.vec.Vec U8) (capacity : Usize) :
    RustM (core.result.Result Unit operations.ReserveError × alloc.vec.Vec U8) :=
  operations.reserve before capacity
end CoreModels
