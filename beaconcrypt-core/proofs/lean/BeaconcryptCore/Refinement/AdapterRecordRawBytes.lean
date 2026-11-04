-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordHelperRouting
import BeaconcryptCore.Refinement.AdapterByteVector
import BeaconcryptCore.Refinement.FrameCodecWriteBytes

/-! The actual fixed-three raw helper copies exactly its three byte chunks after one public empty-vector reservation. Reservation failure and divergence preserve their reached shared poststates and stop every copy. Standard vector extension is derived from the actual U8 clone model. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterRecordRawBytes
variable {E : Type} {m : Type → Type} [Monad m]

def helper (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8))) :
    QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m
  | .reserve before capacity =>
      (fun result => do let reply ← result; .ok (reply, before)) <$> allocation before capacity
  | .encodeFrame sequence sender parts output => serializer sequence sender parts output

def raw (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (first second third : Slice U8) : m (RustM (Option (alloc.vec.Vec U8))) :=
  simulateQ (helper allocation serializer) (AdapterRecordHelperRequestExtraction.raw
    (E := E) (m := AdapterRecordHelperRequestMonad.Program E)
    (Std.Array.make 3#usize [first, second, third])).run

variable [LawfulMonad m]
theorem raw_run (allocation : alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → m (RustM (Usize × Slice U8)))
    (first second third : Slice U8) (prefixLength capacity : Usize)
    (prefixSum : first.val.length + second.val.length = prefixLength.val)
    (length : prefixLength.val + third.val.length = capacity.val) :
    raw allocation serializer first second third = (do
      let result ← allocation (Slice.new U8) capacity
      pure (do
        let reply ← result
        match reply with
        | .Err _ => .ok none
        | .Ok _ => .ok (some ⟨first.val ++ second.val ++ third.val, by
            simp only [List.length_append]
            rw [prefixSum, length]
            scalar_tac⟩))) := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have addSecond := FrameCodecWriteBytes.checked_add_some first.len second.len prefixLength (by simpa only [Slice.len_val, Slice.length] using prefixSum)
  have addThird := FrameCodecWriteBytes.checked_add_some prefixLength third.len capacity (by simpa only [Slice.len_val, Slice.length] using length)
  have index0 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 0#usize = .ok first := rfl
  have index1 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 1#usize = .ok second := rfl
  have index2 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 2#usize = .ok third := rfl
  simp only [raw, AdapterRecordHelperRequestExtraction.raw, AdapterRecordHelperRequestMonad.Lifted.index,
    AdapterRecordHelperRequestMonad.Lifted.len, AdapterRecordHelperRequestMonad.Lifted.checkedAdd,
    AdapterRecordHelperRequestMonad.Lifted.branch, AdapterRecordHelperRequestMonad.Lifted.new,
    index0, index1, index2]
  simp only [AdapterRecordHelperRequestMonad.Program.run_bind,
    AdapterRecordHelperRequestMonad.Program.run_lift,
    core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, addSecond, addThird,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, bind_tc_ok, pure_bind]
  simp only [AdapterRecordHelperRequestMonad.Operations.reserve, AdapterRecordHelperRequestMonad.Program.query,
    simulateQ_bind, simulateQ_spec_query, helper]
  rw [bind_map_left]
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok reply =>
      cases reply with
      | Err error =>
          simp only [bind_tc_ok, AdapterRecordHelperRequestMonad.Lifted.resultOk,
            core.result.Result.ok, AdapterRecordHelperRequestMonad.Program.run_lift, pure_bind]
          rfl
      | Ok success =>
          simp only [bind_tc_ok, AdapterRecordHelperRequestMonad.Lifted.resultOk,
            core.result.Result.ok, AdapterRecordHelperRequestMonad.Program.run_lift, pure_bind]
          have firstCopy : alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone (Slice.new U8) first = .ok first :=
            AdapterByteVector.extend_bytes (Slice.new U8) first (by
              simpa only [Slice.new, List.length_nil, Nat.zero_add] using first.property)
          have secondCopy := AdapterByteVector.extend_bytes first second (by rw [prefixSum]; scalar_tac)
          have thirdCopy := AdapterByteVector.extend_bytes
            (⟨first.val ++ second.val, by rw [List.length_append, prefixSum]; scalar_tac⟩ : Slice U8) third (by
              change (first.val ++ second.val).length + third.val.length ≤ Usize.max
              rw [List.length_append, prefixSum, length]
              scalar_tac)
          simp only [AdapterRecordHelperRequestMonad.Lifted.extend,
            AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
            AdapterRecordHelperRequestMonad.Program.run_pure, firstCopy, secondCopy, thirdCopy,
            pure_bind, simulateQ_pure]

/-- Any successful raw source result has the literal three-chunk bytes; checked source arithmetic supplies its own capacity bounds. -/
theorem raw_success {Platform : Type}
    (allocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (first second third output : Slice U8) (before after : Platform)
    (supported : (.ok (some output), after) ∈ support ((raw allocation serializer first second third).run before)) :
    output.val = first.val ++ second.val ++ third.val := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have index0 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 0#usize = .ok first := rfl
  have index1 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 1#usize = .ok second := rfl
  have index2 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 2#usize = .ok third := rfl
  obtain ⟨prefixOption, prefixRun, prefixSize⟩ := Transport.checked_add_exact first.len second.len
  cases prefixOption with
  | none =>
      have stopped : raw allocation serializer first second third = pure (.ok none) := by
        simp only [raw, AdapterRecordHelperRequestExtraction.raw, AdapterRecordHelperRequestMonad.Lifted.index,
          AdapterRecordHelperRequestMonad.Lifted.len, AdapterRecordHelperRequestMonad.Lifted.checkedAdd,
          AdapterRecordHelperRequestMonad.Lifted.branch, index0, index1,
          AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
          core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, prefixRun,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
        rfl
      rw [stopped] at supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
      cases supported.1
  | some prefixLength =>
      have prefixSum : first.val.length + second.val.length = prefixLength.val := by
        simp only [Transport.absLength, Slice.len_val, Slice.length] at prefixSize
        split_ifs at prefixSize with room
        · exact (Option.some.inj prefixSize).symm
      obtain ⟨totalOption, totalRun, totalSize⟩ := Transport.checked_add_exact prefixLength third.len
      cases totalOption with
      | none =>
          have stopped : raw allocation serializer first second third = pure (.ok none) := by
            simp only [raw, AdapterRecordHelperRequestExtraction.raw, AdapterRecordHelperRequestMonad.Lifted.index,
              AdapterRecordHelperRequestMonad.Lifted.len, AdapterRecordHelperRequestMonad.Lifted.checkedAdd,
              AdapterRecordHelperRequestMonad.Lifted.branch, index0, index1, index2,
              AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
              core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, prefixRun, totalRun,
              core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
            rfl
          rw [stopped] at supported
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
          cases supported.1
      | some capacity =>
          have length : prefixLength.val + third.val.length = capacity.val := by
            simp only [Transport.absLength, Slice.len_val, Slice.length] at totalSize
            split_ifs at totalSize with room
            · exact (Option.some.inj totalSize).symm
          rw [raw_run allocation serializer first second third prefixLength capacity prefixSum length,
            StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨result, middle⟩, _allocated, returned⟩ := supported
          cases result with
          | fail error | div => simp [StateT.run_pure] at returned
          | ok result => cases result with
            | Err error => simp [StateT.run_pure] at returned
            | Ok success =>
                simp only [bind_tc_ok, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
                  RustM.ok.injEq, Option.some.injEq] at returned
                exact congrArg Subtype.val returned.1

end BeaconcryptCore.Refinement.AdapterRecordRawBytes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRawBytes.raw_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRawBytes.raw_run

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRawBytes.raw_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRawBytes.raw_success
