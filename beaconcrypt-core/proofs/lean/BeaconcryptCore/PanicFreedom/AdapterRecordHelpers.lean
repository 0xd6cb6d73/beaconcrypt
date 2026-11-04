-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterWire
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.Transport
import BeaconcryptCore.AdapterRecordHelpersExtraction.Funs
import BeaconcryptCore.Refinement.AdapterRecordFixedParts
import BeaconcryptCore.Refinement.AdapterByteVector
import BeaconcryptCore.Refinement.FrameCodecWriter
import BeaconcryptCore.Refinement.FrameCodecWriteBytes
import BeaconcryptCore.Refinement.Transport

/-! Native safety for the source-corresponding fixed-three record helpers, including length overflow, short output and allocation refusal. The selected dispatcher never invokes the arbitrary-many-parts fallback. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.PanicFreedom.AdapterRecordHelpers
open Refinement Computational AdapterNormal
open FrameCodecRepresentation FrameCodecWriteBytes

theorem frame_three_total (sequence sender : U64) (first second third output : Slice U8) :
    ∃ result, beaconcrypt_parse.frame.encode_three sequence sender first second third output = ok result := by
  obtain ⟨prefixOption, prefixRun, prefixExact⟩ := Transport.checked_add_exact first.len second.len
  cases prefixOption with
  | none => exact ⟨_, FrameCodecWriter.first_length_overflow sequence sender first second third output prefixRun⟩
  | some prefixLength =>
    obtain ⟨lengthOption, lengthRun, lengthExact⟩ := Transport.checked_add_exact prefixLength third.len
    cases lengthOption with
    | none => exact ⟨_, FrameCodecWriter.complete_length_overflow sequence sender first second third output prefixLength prefixRun lengthRun⟩
    | some payloadLength =>
      have prefixValue : first.val.length + second.val.length = prefixLength.val := by
        simp only [Transport.absLength, Slice.len_val, Slice.length] at prefixExact
        split_ifs at prefixExact with room
        · exact (Option.some.inj prefixExact).symm
      have lengthValue : prefixLength.val + third.val.length = payloadLength.val := by
        simp only [Transport.absLength, Slice.len_val, Slice.length] at lengthExact
        split_ifs at lengthExact with room
        · exact (Option.some.inj lengthExact).symm
      let payload : Slice U8 := ⟨first.val ++ second.val ++ third.val, by
        simp only [List.length_append, prefixValue, lengthValue]; scalar_tac⟩
      have payloadValue : payload.len = payloadLength :=
        PqxdhRefinement.usize_eq_of_val (by simp only [payload, Slice.len_val, Slice.length, List.length_append, prefixValue, lengthValue])
      obtain ⟨frameOption, frameRun, frameExact⟩ := TransportSizingBridge.encoded_frame_len_exact sequence sender payloadLength
      cases frameOption with
      | none =>
        have header := FrameCodecWriter.header_rejected sequence sender payloadLength output frameRun
        exact ⟨(0#usize, output), by simp! only [beaconcrypt_parse.frame.encode_three, core.slice.Slice.len,
          rust_primitives.slice.slice_length, prefixRun, lengthRun, header, bind_tc_ok]⟩
      | some frameLength =>
        by_cases short : output.len < frameLength
        · have header := FrameCodecWriter.header_short_output sequence sender payloadLength frameLength output frameRun short
          exact ⟨(0#usize, output), by simp! only [beaconcrypt_parse.frame.encode_three, core.slice.Slice.len,
            rust_primitives.slice.slice_length, prefixRun, lengthRun, header, bind_tc_ok]⟩
        · have measured : frameLength.val = CborSizing.frameLen sequence.val sender.val payloadLength.val ∧
              CborSizing.frameLen sequence.val sender.val payloadLength.val ≤ 33554432 := by
            simp only [Transport.absLength, Transport.messageCap] at frameExact
            split_ifs at frameExact with admitted
            · exact ⟨Option.some.inj frameExact, admitted⟩
          have frameView : frameBytes sequence sender payload = headerBytes sequence sender payload.len ++ payload.val := by
            simp only [frameBytes, headerBytes, tag, List.append_assoc]
          have payloadNatural : payload.val.length = payloadLength.val := by
            simp only [payload, List.length_append, prefixValue, lengthValue]
          have frameSize : (frameBytes sequence sender payload).length =
              CborSizing.frameLen sequence.val sender.val payloadLength.val := by
            rw [frameView, List.length_append]
            simpa only [payloadValue, payloadNatural] using FrameCodecWriteBytes.header_size sequence sender payload.len
          obtain ⟨length, bytes, returned, _, _⟩ := FrameCodecWriteBytes.encode_three_success
            sequence sender first second third payload output rfl
            (by rw [frameSize]; exact measured.2)
            (by
              rw [frameSize, ← measured.1]
              simpa only [UScalar.lt_equiv, Slice.len_val, Slice.length, not_lt] using short)
          exact ⟨(length, bytes), returned⟩

variable [operations : AdapterWirePrimitive.Operations]
variable [fallback : FrameDispatchFallback.Operations]

omit operations in
theorem encode_frame_closure_total
    (capture : beaconcrypt_record_helpers.wire._proof_encode_frame_three.closure)
    (output : Slice U8) :
    ∃ result, beaconcrypt_record_helpers.wire._proof_encode_frame_three.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once capture output = ok result := by
  rcases capture with ⟨sequence, sender, parts⟩
  obtain ⟨first, second, third, _, selected⟩ := FrameDispatch.selected_array sequence sender parts output
  simpa! only [beaconcrypt_record_helpers.wire._proof_encode_frame_three.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once,
    beaconcrypt_parse.encode_frame_parts, lift, bind_tc_ok, selected] using
    frame_three_total sequence sender first second third output

omit operations fallback in
private theorem checked_add_normal (left right : Usize) :
    Normal (core.num.Usize.checked_add left right) := by
  obtain ⟨result, returned, _⟩ := Refinement.Transport.checked_add_exact left right
  exact ⟨result, returned⟩

theorem encode_frame_total (contracts : AdapterWire.Contracts) (sequence sender : U64)
    (parts : Array (Slice U8) 3#usize) :
    ∃ result, beaconcrypt_record_helpers.wire._proof_encode_frame_three sequence sender parts = ok result := by
  have serializerNormal : AdapterWire.SerializerNormal
      beaconcrypt_record_helpers.wire._proof_encode_frame_three.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize :=
    fun capture output => encode_frame_closure_total capture output
  obtain ⟨first, second, third, _, index0, index1, index2⟩ := AdapterRecordFixedParts.indices parts
  unfold beaconcrypt_record_helpers.wire._proof_encode_frame_three
  simp only [index0, index1, index2, core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  repeat'
    first
    | exact normal_ok _
    | exact checked_add_normal _ _
    | exact BeaconcryptCore.PanicFreedom.Transport.encoded_frame_len_total _ _ _
    | exact AdapterWire.encode_record_total contracts _ _ _ serializerNormal
    | intro value
    | split
    | simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
        bind_tc_ok]
    | apply normal_bind

omit fallback in
theorem join_total (contracts : AdapterWire.Contracts) (parts : Array (Slice U8) 3#usize) :
    ∃ result, beaconcrypt_record_helpers.ratchet._proof_join_record_three parts = ok result := by
  obtain ⟨first, second, third, _, index0, index1, index2⟩ := AdapterRecordFixedParts.indices parts
  have initial := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len
    (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  obtain ⟨prefixOption, prefixRun, prefixExact⟩ := Refinement.Transport.checked_add_exact first.len second.len
  cases prefixOption with
  | none =>
    exact ⟨.None, by simp! only [beaconcrypt_record_helpers.ratchet._proof_join_record_three,
      index0, index1, core.slice.Slice.len, rust_primitives.slice.slice_length,
      initial, prefixRun, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, bind_tc_ok]⟩
  | some prefixLength =>
    have prefixValue : first.val.length + second.val.length = prefixLength.val := by
      simp only [Refinement.Transport.absLength, Slice.len_val, Slice.length] at prefixExact
      split_ifs at prefixExact with room
      · exact (Option.some.inj prefixExact).symm
    obtain ⟨capacityOption, capacityRun, capacityExact⟩ := Refinement.Transport.checked_add_exact prefixLength third.len
    cases capacityOption with
    | none =>
      exact ⟨.None, by simp! only [beaconcrypt_record_helpers.ratchet._proof_join_record_three,
        index0, index1, index2, core.slice.Slice.len, rust_primitives.slice.slice_length,
        initial, prefixRun, capacityRun, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, bind_tc_ok]⟩
    | some capacity =>
      have capacityValue : prefixLength.val + third.val.length = capacity.val := by
        simp only [Refinement.Transport.absLength, Slice.len_val, Slice.length] at capacityExact
        split_ifs at capacityExact with room
        · exact (Option.some.inj capacityExact).symm
      obtain ⟨allocation, reserved⟩ := contracts.reserve (Slice.new U8) capacity
      cases allocation with
      | Err error =>
        exact ⟨.None, by simp! only [beaconcrypt_record_helpers.ratchet._proof_join_record_three,
          index0, index1, index2, core.slice.Slice.len, rust_primitives.slice.slice_length,
          initial, prefixRun, capacityRun, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
          alloc.vec.Vec.try_reserve_exact, reserved, core.result.Result.ok,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, bind_tc_ok]⟩
      | Ok success =>
        have firstCopy : alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone
            (Slice.new U8) first = ok first := AdapterByteVector.extend_bytes (Slice.new U8) first
          (by simpa only [Slice.new, List.length_nil, Nat.zero_add] using first.property)
        have secondCopy := AdapterByteVector.extend_bytes first second (by rw [prefixValue]; scalar_tac)
        have thirdCopy := AdapterByteVector.extend_bytes
          ⟨first.val ++ second.val, by simp only [List.length_append]; rw [prefixValue]; scalar_tac⟩ third
          (by simp only [List.length_append]; rw [prefixValue, capacityValue]; scalar_tac)
        exact ⟨_, by simp! only [beaconcrypt_record_helpers.ratchet._proof_join_record_three,
          index0, index1, index2, core.slice.Slice.len, rust_primitives.slice.slice_length,
          initial, prefixRun, capacityRun, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
          alloc.vec.Vec.try_reserve_exact, reserved, core.result.Result.ok,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          firstCopy, secondCopy, thirdCopy, bind_tc_ok]; rfl⟩

end BeaconcryptCore.PanicFreedom.AdapterRecordHelpers
