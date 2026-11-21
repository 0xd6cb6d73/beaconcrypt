-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterSealJoinRequestExtraction
import BeaconcryptCore.AdapterSealJoinExtraction.Funs

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

/-! The reserve-only request lift specializes definitionally to the exact extracted fixed-two helper. The allocator's error and returned vector remain literal; no allocation success, joined-byte or source-codec premise is assumed. -/

namespace BeaconcryptCore.Refinement.AdapterSealJoinSpecialization
open AdapterSealJoinRequestMonad

@[instance_reducible] def rustOperations [allocator : AdapterWirePrimitive.Operations] :
    Operations allocator.ReserveError RustM where
  reserve := alloc.vec.Vec.try_reserve_exact

theorem rust_specializes [allocator : AdapterWirePrimitive.Operations]
    (parts : Array (Slice U8) 2#usize) :
    @AdapterSealJoinRequestExtraction.join allocator.ReserveError RustM _ _ rustOperations parts =
      beaconcrypt_seal_join.ratchet._proof_join_seal_two parts := rfl

end BeaconcryptCore.Refinement.AdapterSealJoinSpecialization

/-- info: 'BeaconcryptCore.Refinement.AdapterSealJoinSpecialization.rust_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealJoinSpecialization.rust_specializes
