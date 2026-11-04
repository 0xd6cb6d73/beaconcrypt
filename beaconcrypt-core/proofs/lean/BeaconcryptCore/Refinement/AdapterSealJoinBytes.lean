-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterByteVector
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
import BeaconcryptCore.Refinement.AdapterSealFixedParts
import BeaconcryptCore.AdapterSealJoinRequestExtraction
import BeaconcryptCore.Refinement.FrameCodecWriteBytes

/-! Actual fixed-two source joining preserves the bytes cloned after the public reservation gate. Every allocator failure/divergence keeps its reached state; successful standard reservation preserves the original vector contents. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterSealJoinBytes
open AdapterPublicWrapperRustT (RustT)
variable {m : Type → Type} [Monad m] {E : Type}

@[instance_reducible] def operations (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E))) :
    AdapterSealJoinRequestMonad.Operations E (RustT m) where
  reserve before capacity := ⟨(fun result => do let reply ← result; .ok (reply, before)) <$> allocation before capacity⟩

def join (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (first second : Slice U8) : RustT m (Option (alloc.vec.Vec U8)) :=
  letI := operations allocation
  AdapterSealJoinRequestExtraction.join (E := E) (Std.Array.make 2#usize [first, second])

variable [LawfulMonad m]
theorem join_run (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (first second : Slice U8) (capacity : Usize)
    (length : first.val.length + second.val.length = capacity.val) :
    (join allocation first second).run = (do
      let result ← allocation (Slice.new U8) capacity
      pure (do
        let reply ← result
        match reply with
        | .Err _ => .ok none
        | .Ok _ => .ok (some ⟨first.val ++ second.val, by
            rw [List.length_append, length]
            scalar_tac⟩))) := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have addSecond := FrameCodecWriteBytes.checked_add_some first.len second.len capacity (by simpa only [Slice.len_val, Slice.length] using length)
  have indices := AdapterSealFixedParts.indices2 first second
  simp only [join, AdapterSealJoinRequestExtraction.join, AdapterSealJoinRequestMonad.Lifted.index,
    AdapterSealJoinRequestMonad.Lifted.len, AdapterSealJoinRequestMonad.Lifted.checkedAdd,
    AdapterSealJoinRequestMonad.Lifted.branch, AdapterSealJoinRequestMonad.Lifted.new,
    indices.1, indices.2]
  simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
    core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, addSecond,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, bind_tc_ok]
  simp only [AdapterSealJoinRequestMonad.Operations.reserve]
  rw [bind_map_left]
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok reply =>
      cases reply with
      | Err error =>
          simp only [bind_tc_ok, AdapterSealJoinRequestMonad.Lifted.resultOk,
            core.result.Result.ok, RustT.run_liftRust, pure_bind]
          rfl
      | Ok success =>
          simp only [bind_tc_ok, AdapterSealJoinRequestMonad.Lifted.resultOk,
            core.result.Result.ok, RustT.run_liftRust, pure_bind]
          have firstCopy : alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone (Slice.new U8) first = .ok first := by
            exact AdapterByteVector.extend_bytes (Slice.new U8) first (by
              simpa only [Slice.new, List.length_nil, Nat.zero_add] using first.property)
          have secondCopy := AdapterByteVector.extend_bytes first second (by rw [length]; scalar_tac)
          simp only [AdapterSealJoinRequestMonad.Lifted.extend, RustT.run_bind, RustT.run_liftRust,
            firstCopy, secondCopy, pure_bind, RustT.run_pure]

theorem shared_run {Platform : Type}
    (allocation : alloc.vec.Vec U8 → Usize → StateT Platform m (RustM (core.result.Result Unit E)))
    (first second : Slice U8) (capacity : Usize)
    (length : first.val.length + second.val.length = capacity.val) (before : Platform) :
    ((join allocation first second).run).run before =
      (fun result => ((do
        let reply ← result.1
        match reply with
        | .Err _ => .ok none
        | .Ok _ => .ok (some ⟨first.val ++ second.val, by
            rw [List.length_append, length]
            scalar_tac⟩)), result.2)) <$> (allocation (Slice.new U8) capacity).run before := by
  rw [join_run allocation first second capacity length]
  rw [StateT.run_bind]
  exact bind_pure_comp _ _

end BeaconcryptCore.Refinement.AdapterSealJoinBytes

/-- info: 'BeaconcryptCore.Refinement.AdapterSealJoinBytes.join_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealJoinBytes.join_run

/-- info: 'BeaconcryptCore.Refinement.AdapterSealJoinBytes.shared_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealJoinBytes.shared_run
