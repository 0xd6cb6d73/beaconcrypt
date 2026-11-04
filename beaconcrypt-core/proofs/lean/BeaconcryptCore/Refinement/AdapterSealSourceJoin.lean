-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterSealExtraction.Funs
import BeaconcryptCore.AdapterSealJoinExtraction.Funs

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

/-! The original prefixed seal call site constructs exactly two slices. Only that shape selects the actual extracted fixed-two join helper; every other generic join remains the supplied callback. These are source-instantiation equations without an arbitrary-count join, byte, allocator-success, codec or security premise. -/

namespace BeaconcryptCore.Refinement.AdapterSealSourceJoin

@[instance_reducible] def sourceCallbacks [AdapterWirePrimitive.Operations]
    (other : AdapterSealJoinCallbacks.Operations) : AdapterSealJoinCallbacks.Operations where
  join {N} parts :=
    if two : N = 2#usize then
      beaconcrypt_seal_join.ratchet._proof_join_seal_two
        ⟨parts.val, by simpa only [two] using parts.property⟩
    else other.join parts

theorem selected [AdapterWirePrimitive.Operations]
    (other : AdapterSealJoinCallbacks.Operations) (parts : Array (Slice U8) 2#usize) :
    (sourceCallbacks other).join parts =
      beaconcrypt_seal_join.ratchet._proof_join_seal_two parts := rfl

theorem outside [AdapterWirePrimitive.Operations] (other : AdapterSealJoinCallbacks.Operations)
    {N : Usize} (different : N ≠ 2#usize) (parts : Array (Slice U8) N) :
    (sourceCallbacks other).join parts = other.join parts := by
  exact dite_eq_right different

theorem single_independent [primitive : AdapterSealPrimitive.Operations]
    (left right : AdapterSealJoinCallbacks.Operations)
    (request : beaconcrypt_core.record_effects.AeadSealRequest) (plaintext : Slice U8)
    (single : request.plaintext = .Single plaintext) :
    @beaconcrypt_seal.ratchet.execute_seal_request primitive left request =
      @beaconcrypt_seal.ratchet.execute_seal_request primitive right request := by
  simp only [beaconcrypt_seal.ratchet.execute_seal_request, single]

end BeaconcryptCore.Refinement.AdapterSealSourceJoin

/-- info: 'BeaconcryptCore.Refinement.AdapterSealSourceJoin.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealSourceJoin.selected

/-- info: 'BeaconcryptCore.Refinement.AdapterSealSourceJoin.outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealSourceJoin.outside

/-- info: 'BeaconcryptCore.Refinement.AdapterSealSourceJoin.single_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealSourceJoin.single_independent
