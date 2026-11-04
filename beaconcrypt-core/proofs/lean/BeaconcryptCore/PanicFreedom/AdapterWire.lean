-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterWireExtraction.Funs
import BeaconcryptCore.Refinement.AdapterWireVector

/-! Native writer safety permits reservation refusal and arbitrary normal serializer replies. Reservation preserves all initialized bytes on both Result branches. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterWire
open Refinement
variable [operations : AdapterWirePrimitive.Operations]

structure Contracts : Prop where
  reserve : ∀ before capacity, ∃ result, operations.reserve before capacity = ok (result, before)

def SerializerNormal {T : Type} (serializer : AdapterWirePrimitive.Serializer T) : Prop :=
  ∀ value bytes, ∃ result, serializer.call_once value bytes = ok result

theorem encode_record_total (contracts : Contracts) {T : Type}
    (serializer : AdapterWirePrimitive.Serializer T) (capacity : Usize) (value : T)
    (serializerNormal : SerializerNormal serializer) :
    ∃ result, beaconcrypt.wire.encode_record serializer capacity value = ok result := by
  obtain ⟨allocation, reserved⟩ := contracts.reserve (Slice.new U8) capacity
  cases allocation with
  | Err error =>
    exact ⟨.None, by simp! only [beaconcrypt.wire.encode_record, alloc.vec.Vec.new,
      rust_primitives.sequence.seq_empty, alloc.vec.Vec.try_reserve_exact,
      reserved, core.result.Result.ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      bind_tc_ok]⟩
  | Ok success =>
    exact (serializerNormal value (AdapterWireVector.zeros capacity)).elim
      fun result serialized => by
        rcases result with ⟨written, bytes⟩
        by_cases empty : written = 0#usize
        · exact ⟨.None, by simp! only [beaconcrypt.wire.encode_record, alloc.vec.Vec.new,
            rust_primitives.sequence.seq_empty, alloc.vec.Vec.try_reserve_exact,
            reserved, core.result.Result.ok,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
            AdapterWireVector.resize_empty, AdapterWireVector.deref_mut_bytes,
            serialized, empty, ↓reduceIte, bind_tc_ok]⟩
        · exact ⟨.Some (AdapterWireVector.take bytes written), by
            simp! only [beaconcrypt.wire.encode_record, alloc.vec.Vec.new,
              rust_primitives.sequence.seq_empty, alloc.vec.Vec.try_reserve_exact,
              reserved, core.result.Result.ok,
              core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
              AdapterWireVector.resize_empty, AdapterWireVector.deref_mut_bytes,
              serialized, empty, ↓reduceIte, AdapterWireVector.truncate_bytes, bind_tc_ok, id_eq]⟩

end BeaconcryptCore.PanicFreedom.AdapterWire
