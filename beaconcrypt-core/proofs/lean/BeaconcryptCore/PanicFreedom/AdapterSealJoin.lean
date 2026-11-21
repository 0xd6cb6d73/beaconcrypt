-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterWire
import BeaconcryptCore.AdapterSealJoinExtraction.Funs
import BeaconcryptCore.Refinement.AdapterSealFixedParts
import BeaconcryptCore.Refinement.AdapterByteVector
import BeaconcryptCore.Refinement.FrameCodecWriteBytes
import BeaconcryptCore.Refinement.Transport

/-! The specialized source join returns normally on overflow and allocation refusal as well as success. Its source correspondence remains the separately checked fixed-two specialization. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterSealJoin
open Refinement
variable [operations : AdapterWirePrimitive.Operations]

theorem join_total (contracts : AdapterWire.Contracts) (parts : Array (Slice U8) 2#usize) :
    ∃ result, beaconcrypt_seal_join.ratchet._proof_join_seal_two parts = ok result := by
  obtain ⟨first, second, _, index0, index1⟩ := AdapterSealFixedParts.indices parts
  have initial := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len
    (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  obtain ⟨capacityOption, capacityRun, capacitySize⟩ := Transport.checked_add_exact first.len second.len
  cases capacityOption with
  | none =>
    exact ⟨.None, by simp! only [beaconcrypt_seal_join.ratchet._proof_join_seal_two,
      index0, index1, core.slice.Slice.len, rust_primitives.slice.slice_length,
      initial, capacityRun, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      bind_tc_ok]⟩
  | some capacity =>
    have length : first.val.length + second.val.length = capacity.val := by
      simp only [Transport.absLength, Slice.len_val, Slice.length] at capacitySize
      split_ifs at capacitySize with room
      · exact (Option.some.inj capacitySize).symm
    obtain ⟨allocation, reserved⟩ := contracts.reserve (Slice.new U8) capacity
    cases allocation with
    | Err error =>
      exact ⟨.None, by simp! only [beaconcrypt_seal_join.ratchet._proof_join_seal_two,
        index0, index1, core.slice.Slice.len, rust_primitives.slice.slice_length,
        initial, capacityRun, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
        alloc.vec.Vec.try_reserve_exact, reserved, core.result.Result.ok,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
        bind_tc_ok]⟩
    | Ok success =>
      have firstCopy : alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone
          (Slice.new U8) first = ok first :=
        AdapterByteVector.extend_bytes (Slice.new U8) first
          (by simpa only [Slice.new, List.length_nil, Nat.zero_add] using first.property)
      have secondCopy := AdapterByteVector.extend_bytes first second (by rw [length]; scalar_tac)
      exact ⟨_, by simp! only [beaconcrypt_seal_join.ratchet._proof_join_seal_two,
        index0, index1, core.slice.Slice.len, rust_primitives.slice.slice_length,
        initial, capacityRun, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
        alloc.vec.Vec.try_reserve_exact, reserved, core.result.Result.ok,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        firstCopy, secondCopy, bind_tc_ok]; rfl⟩

end BeaconcryptCore.PanicFreedom.AdapterSealJoin
