-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordRawBytes
import BeaconcryptCore.Refinement.AdapterWireAllocation
import BeaconcryptCore.Computational.TransportSizingBridge

/-! The actual selected Frame3 helper computes its real capacity before a public empty-vector reservation. Trusted serialization receives the exact original three chunks and mutable zero-initialized output. All allocator and serializer failures remain Rust results with their reached common poststates. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterRecordFrameBytes
variable {E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def frame (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (sequence sender : U64) (first second third : Slice U8) : m (RustM (Option (alloc.vec.Vec U8))) :=
  simulateQ (AdapterRecordRawBytes.helper allocation serializer)
    (AdapterRecordHelperRequestExtraction.frame (E := E) (m := AdapterRecordHelperRequestMonad.Program E)
      sequence sender (Std.Array.make 3#usize [first, second, third])).run

def encode (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : Slice U8 → m (RustM (Usize × Slice U8))) (capacity : Usize) : m (RustM (Option (alloc.vec.Vec U8))) := do
  let reserved ← allocation (Slice.new U8) capacity
  match reserved with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok _) => do
      let serialized ← serializer (AdapterWireVector.zeros capacity)
      pure (do
        let result ← serialized
        .ok (if result.1 = 0#usize then none else some (AdapterWireVector.take result.2 result.1)))

/-- The actual fixed-three source body reduces to its exact capacity-selected allocator and serializer, preserving all Rust outcomes. -/
theorem frame_run
    (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (sequence sender : U64) (first second third : Slice U8) (prefixLength payloadLength capacity : Usize)
    (prefixSum : first.val.length + second.val.length = prefixLength.val)
    (length : prefixLength.val + third.val.length = payloadLength.val)
    (admitted : beaconcrypt_core.transport.encoded_frame_len sequence sender payloadLength = .ok (.Some capacity)) :
    frame allocation serializer sequence sender first second third =
      encode allocation (serializer sequence sender (Std.Array.make 3#usize [first, second, third])) capacity := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have addSecond := FrameCodecWriteBytes.checked_add_some first.len second.len prefixLength (by simpa only [Slice.len_val, Slice.length] using prefixSum)
  have addThird := FrameCodecWriteBytes.checked_add_some prefixLength third.len payloadLength (by simpa only [Slice.len_val, Slice.length] using length)
  have index0 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 0#usize = .ok first := rfl
  have index1 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 1#usize = .ok second := rfl
  have index2 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 2#usize = .ok third := rfl
  simp only [frame, AdapterRecordHelperRequestExtraction.frame, AdapterRecordHelperRequestMonad.Lifted.index,
    AdapterRecordHelperRequestMonad.Lifted.len, AdapterRecordHelperRequestMonad.Lifted.checkedAdd,
    AdapterRecordHelperRequestMonad.Lifted.branch, AdapterRecordHelperRequestMonad.Lifted.frameCapacity,
    index0, index1, index2, AdapterRecordHelperRequestMonad.Program.run_bind,
    AdapterRecordHelperRequestMonad.Program.run_lift, core.slice.Slice.len, rust_primitives.slice.slice_length,
    addFirst, addSecond, addThird, admitted, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
  simp! only [AdapterRecordHelperRequestMonad.Lifted.writeFrame, AdapterWireRequestExtraction.encodeRecord,
    AdapterWireRequestMonad.Operations.reserve, AdapterWireRequestMonad.Operations.serialize,
    AdapterWireRequestMonad.Lifted.new, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty,
    AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
    AdapterRecordHelperRequestMonad.Operations.reserve, AdapterRecordHelperRequestMonad.Operations.encodeFrame,
    AdapterRecordHelperRequestMonad.Program.query, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
    AdapterRecordRawBytes.helper, pure_bind, bind_tc_ok, bind_map_left, encode]
  apply bind_congr
  intro reserved
  cases reserved with
  | fail error | div => rfl
  | ok reply =>
      cases reply with
      | Err error =>
          simp! only [AdapterWireRequestMonad.Lifted.resultOk, AdapterWireRequestMonad.Lifted.branch,
            AdapterWireRequestMonad.Lifted.fromResidual, core.result.Result.ok,
            AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind, bind_tc_ok]
          rfl
      | Ok value =>
          simp! only [AdapterWireRequestMonad.Lifted.resultOk, AdapterWireRequestMonad.Lifted.branch,
            AdapterWireRequestMonad.Lifted.resize, AdapterWireRequestMonad.Lifted.derefMut,
            core.result.Result.ok, AdapterWireVector.resize_empty, AdapterWireVector.deref_mut_bytes,
            AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind, bind_tc_ok]
          simp only [simulateQ_bind, simulateQ_spec_query, AdapterRecordRawBytes.helper]
          apply bind_congr
          intro serialized
          cases serialized with
          | fail error | div => rfl
          | ok result =>
              rcases result with ⟨written, output⟩
              dsimp only
              by_cases empty : written = 0#usize <;> simp only [empty, ite_true, ite_false, bind_tc_ok, id_eq, AdapterWireRequestMonad.Lifted.truncate, AdapterWireVector.truncate_bytes,
                AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
                AdapterRecordHelperRequestMonad.Program.run_pure, pure_bind, simulateQ_pure]
open BeaconcryptCore.Computational
open FrameCodecRepresentation

/-- Successful source sizing determines the actual canonical frame length and its complete-message bound. -/
theorem capacity_value (sequence sender : U64) (payload : Slice U8) (capacity : Usize)
    (admitted : beaconcrypt_core.transport.encoded_frame_len sequence sender payload.len = .ok (.Some capacity)) :
    capacity.val = (frameBytes sequence sender payload).length ∧ (frameBytes sequence sender payload).length ≤ 33554432 := by
  obtain ⟨reply, run, size⟩ := TransportSizingBridge.encoded_frame_len_exact sequence sender payload.len
  have same : reply = .Some capacity := RustM.ok.inj (run.symm.trans admitted)
  rw [same] at size
  simp only [Transport.absLength, Transport.messageCap] at size
  split_ifs at size with bound
  · have value : capacity.val = CborSizing.frameLen sequence.val sender.val payload.len.val := Option.some.inj size
    have frameView : frameBytes sequence sender payload = FrameCodecWriteBytes.headerBytes sequence sender payload.len ++ payload.val := rfl
    have frameSize : (frameBytes sequence sender payload).length = CborSizing.frameLen sequence.val sender.val payload.len.val := by
      rw [frameView, List.length_append]
      simpa only [Slice.len_val, Slice.length] using FrameCodecWriteBytes.header_size sequence sender payload.len
    exact ⟨value.trans frameSize.symm, frameSize ▸ bound⟩

def serializer [FrameDispatchFallback.Operations] (sequence sender : U64)
    (parts : Std.Array (Slice U8) 3#usize) (output : Slice U8) : m (RustM (Usize × Slice U8)) :=
  pure (beaconcrypt_parse_dispatch.frame.encode_parts sequence sender (Std.Array.to_slice parts) output)

/-- The actual source Frame3 serializer and allocator produce exact canonical bytes on success; allocation rejection, Rust failure and divergence retain their distinct original outcomes. -/
theorem frame_bytes [FrameDispatchFallback.Operations]
    (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (sequence sender : U64) (first second third payload : Slice U8) (prefixLength capacity : Usize)
    (prefixSum : first.val.length + second.val.length = prefixLength.val)
    (payloadView : payload.val = first.val ++ second.val ++ third.val)
    (admitted : beaconcrypt_core.transport.encoded_frame_len sequence sender payload.len = .ok (.Some capacity)) :
    frame allocation (serializer (m := m)) sequence sender first second third =
      (fun reserved => do
        let reply ← reserved
        match reply with
        | .Err _ => .ok none
        | .Ok _ => .ok (some (⟨frameBytes sequence sender payload, by
            rw [← (capacity_value sequence sender payload capacity admitted).1]
            scalar_tac⟩ : alloc.vec.Vec U8))) <$> allocation (Slice.new U8) capacity := by
  have length : prefixLength.val + third.val.length = payload.len.val := by
    simp only [Slice.len_val, Slice.length, payloadView, List.length_append]
    omega
  obtain ⟨exactCapacity, bounded⟩ := capacity_value sequence sender payload capacity admitted
  rw [frame_run allocation (serializer (m := m)) sequence sender first second third prefixLength payload.len capacity prefixSum length admitted]
  unfold encode
  rw [← bind_pure_comp]
  apply bind_congr
  intro reserved
  cases reserved with
  | fail error | div => rfl
  | ok reply =>
      cases reply with
      | Err error => rfl
      | Ok success =>
          obtain ⟨written, result, sourceRun, sourceSize, sourceBytes⟩ :=
            FrameCodecWriteBytes.encode_three_success sequence sender first second third payload
              (AdapterWireVector.zeros capacity) payloadView bounded (by
                simp only [AdapterWireVector.zeros, List.length_replicate, exactCapacity, le_refl])
          have nonempty : written ≠ 0#usize := by
            intro zero
            have empty : written.val = 0 := by rw [zero]; rfl
            rw [sourceSize] at empty
            simp only [frameBytes, List.length_append, List.length_cons, List.length_nil] at empty
            omega
          have selected : Std.Array.to_slice (Std.Array.make 3#usize [first, second, third]) = FrameDispatch.three first second third := rfl
          simp only [serializer, selected, FrameDispatch.selected_three, sourceRun, pure_bind, bind_tc_ok, nonempty, ite_false]
          congr 3
          apply Subtype.ext
          simp only [AdapterWireVector.take, sourceBytes, sourceSize, List.take_left' rfl]

end BeaconcryptCore.Refinement.AdapterRecordFrameBytes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_run

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFrameBytes.capacity_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFrameBytes.capacity_value

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes
