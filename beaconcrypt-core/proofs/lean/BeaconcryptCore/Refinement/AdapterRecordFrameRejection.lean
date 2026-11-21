-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordFrameBytes
import BeaconcryptCore.Computational.TransportSizingBridge
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterRecordFrameRejection
variable {E : Type} {m : Type → Type} [Monad m]

/-- Actual prefix-length overflow returns before either public allocation or trusted serialization. -/
theorem sum_rejected
    (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (sequence sender : U64) (first second third : Slice U8)
    (rejected : core.num.Usize.checked_add first.len second.len = .ok .None) :
    AdapterRecordFrameBytes.frame allocation serializer sequence sender first second third = pure (.ok none) := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have index0 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 0#usize = .ok first := rfl
  have index1 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 1#usize = .ok second := rfl
  simp only [AdapterRecordFrameBytes.frame, AdapterRecordHelperRequestExtraction.frame,
    AdapterRecordHelperRequestMonad.Lifted.index, AdapterRecordHelperRequestMonad.Lifted.len,
    AdapterRecordHelperRequestMonad.Lifted.checkedAdd, AdapterRecordHelperRequestMonad.Lifted.branch,
    index0, index1, AdapterRecordHelperRequestMonad.Program.run_bind,
    AdapterRecordHelperRequestMonad.Program.run_lift,
    core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, rejected,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
  rfl

/-- The actual complete-length overflow also stops before allocator and serializer calls. -/
theorem total_rejected
    (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (sequence sender : U64) (first second third : Slice U8) (prefixLength : Usize)
    (prefixSum : first.val.length + second.val.length = prefixLength.val)
    (rejected : core.num.Usize.checked_add prefixLength third.len = .ok .None) :
    AdapterRecordFrameBytes.frame allocation serializer sequence sender first second third = pure (.ok none) := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have addSecond := FrameCodecWriteBytes.checked_add_some first.len second.len prefixLength (by simpa only [Slice.len_val, Slice.length] using prefixSum)
  have index0 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 0#usize = .ok first := rfl
  have index1 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 1#usize = .ok second := rfl
  have index2 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 2#usize = .ok third := rfl
  simp only [AdapterRecordFrameBytes.frame, AdapterRecordHelperRequestExtraction.frame,
    AdapterRecordHelperRequestMonad.Lifted.index, AdapterRecordHelperRequestMonad.Lifted.len,
    AdapterRecordHelperRequestMonad.Lifted.checkedAdd, AdapterRecordHelperRequestMonad.Lifted.branch,
    index0, index1, index2, AdapterRecordHelperRequestMonad.Program.run_bind,
    AdapterRecordHelperRequestMonad.Program.run_lift,
    core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, addSecond, rejected,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
  rfl


/-- The actual complete-message admission refusal reaches neither reservation nor the serializer. -/
theorem capacity_rejected
    (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (sequence sender : U64) (first second third : Slice U8) (prefixLength payloadLength : Usize)
    (prefixSum : first.val.length + second.val.length = prefixLength.val)
    (length : prefixLength.val + third.val.length = payloadLength.val)
    (rejected : beaconcrypt_core.transport.encoded_frame_len sequence sender payloadLength = .ok .None) :
    AdapterRecordFrameBytes.frame allocation serializer sequence sender first second third = pure (.ok none) := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have addSecond := FrameCodecWriteBytes.checked_add_some first.len second.len prefixLength (by simpa only [Slice.len_val, Slice.length] using prefixSum)
  have addThird := FrameCodecWriteBytes.checked_add_some prefixLength third.len payloadLength (by simpa only [Slice.len_val, Slice.length] using length)
  have index0 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 0#usize = .ok first := rfl
  have index1 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 1#usize = .ok second := rfl
  have index2 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 2#usize = .ok third := rfl
  simp only [AdapterRecordFrameBytes.frame, AdapterRecordHelperRequestExtraction.frame,
    AdapterRecordHelperRequestMonad.Lifted.index, AdapterRecordHelperRequestMonad.Lifted.len,
    AdapterRecordHelperRequestMonad.Lifted.checkedAdd, AdapterRecordHelperRequestMonad.Lifted.branch,
    AdapterRecordHelperRequestMonad.Lifted.frameCapacity,
    index0, index1, index2, AdapterRecordHelperRequestMonad.Program.run_bind,
    AdapterRecordHelperRequestMonad.Program.run_lift,
    core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, addSecond, addThird, rejected,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
  rfl

end BeaconcryptCore.Refinement.AdapterRecordFrameRejection

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFrameRejection.sum_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFrameRejection.sum_rejected

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFrameRejection.total_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFrameRejection.total_rejected

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFrameRejection.capacity_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFrameRejection.capacity_rejected
