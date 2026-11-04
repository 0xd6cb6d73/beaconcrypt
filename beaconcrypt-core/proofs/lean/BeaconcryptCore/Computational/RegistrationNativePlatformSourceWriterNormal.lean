-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal
/-! The concrete fixed-three helper and registration response serializer return normally under every fallible public reservation. Checked arithmetic and capacity refusal are proved from their literal request trees, preserving all reached platform state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceWriterNormal
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSourceBuildNormal (Normal)
variable {P E : Type}
open AdapterRecordRawBytes (raw raw_run)
private theorem raw_normal
    (allocate : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E))
    (serializer : U64→U64→Std.Array (Slice U8) 3#usize→Slice U8→StateT P ProbComp (RustM (Usize×Slice U8)))
    (first second third : Slice U8) (before : P)
    (result : RustM (Option (alloc.vec.Vec U8))×P)
    (supported : result∈support ((raw (fun before capacity=>RustM.ok <$>allocate before capacity) serializer first second third).run before)) :
    ∃value,result.1=.ok value := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have index0 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 0#usize = .ok first := rfl
  have index1 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 1#usize = .ok second := rfl
  have index2 : Std.Array.index_usize (Std.Array.make 3#usize [first, second, third]) 2#usize = .ok third := rfl
  obtain ⟨prefixOption, prefixRun, prefixSize⟩ := Transport.checked_add_exact first.len second.len
  cases prefixOption with
  | none =>
      have stopped : raw (fun before capacity=>RustM.ok <$>allocate before capacity) serializer first second third = pure (.ok none) := by
        simp only [raw, AdapterRecordHelperRequestExtraction.raw, AdapterRecordHelperRequestMonad.Lifted.index,
          AdapterRecordHelperRequestMonad.Lifted.len, AdapterRecordHelperRequestMonad.Lifted.checkedAdd,
          AdapterRecordHelperRequestMonad.Lifted.branch, index0, index1,
          AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
          core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, prefixRun,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
        rfl
      rw [stopped] at supported
      simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
      subst result
      exact ⟨_,rfl⟩
  | some prefixLength =>
      have prefixSum : first.val.length + second.val.length = prefixLength.val := by
        simp only [Transport.absLength, Slice.len_val, Slice.length] at prefixSize
        split_ifs at prefixSize with room
        · exact (Option.some.inj prefixSize).symm
      obtain ⟨totalOption, totalRun, totalSize⟩ := Transport.checked_add_exact prefixLength third.len
      cases totalOption with
      | none =>
          have stopped : raw (fun before capacity=>RustM.ok <$>allocate before capacity) serializer first second third = pure (.ok none) := by
            simp only [raw, AdapterRecordHelperRequestExtraction.raw, AdapterRecordHelperRequestMonad.Lifted.index,
              AdapterRecordHelperRequestMonad.Lifted.len, AdapterRecordHelperRequestMonad.Lifted.checkedAdd,
              AdapterRecordHelperRequestMonad.Lifted.branch, index0, index1, index2,
              AdapterRecordHelperRequestMonad.Program.run_bind, AdapterRecordHelperRequestMonad.Program.run_lift,
              core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, prefixRun, totalRun,
              core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
            rfl
          rw [stopped] at supported
          simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
          subst result
          exact ⟨_,rfl⟩
      | some capacity =>
          have length : prefixLength.val + third.val.length = capacity.val := by
            simp only [Transport.absLength, Slice.len_val, Slice.length] at totalSize
            split_ifs at totalSize with room
            · exact (Option.some.inj totalSize).symm
          rw [raw_run _ serializer first second third prefixLength capacity prefixSum length] at supported
          simp only [bind_pure_comp,StateT.run_map,Functor.map_map,bind_tc_ok,support_map] at supported
          obtain ⟨allocated,called,same⟩ := supported
          subst result
          rcases allocated with ⟨reply,afterPlatform⟩
          cases reply <;> exact ⟨_,rfl⟩

private theorem frame_normal (reserve : Nat→StateT P ProbComp (core.result.Result Unit E))
    (sequence sender : U64) (first second third : Slice U8) (before : P)
    (result : RustM (Option (alloc.vec.Vec U8))×P)
    (supported : result∈support ((AdapterRecordFrameBytes.frame (RegistrationNativePlatformConcreteSource.rawAllocation reserve)
      RegistrationNativePlatformConcreteSource.serializer sequence sender first second third).run before)) :
    ∃value,result.1=.ok value := by
  have projected : (RegistrationNativeExtractedAllocation.abstractResult result.1,result.2)∈support
      ((RegistrationNativeExtractedAllocation.abstractResult <$>
        AdapterRecordFrameBytes.frame (RegistrationNativePlatformConcreteSource.rawAllocation reserve)
          RegistrationNativePlatformConcreteSource.serializer sequence sender first second third).run before) := by
    rw [StateT.run_map,support_map]
    exact ⟨result,supported,rfl⟩
  rw [RegistrationNativePlatformConcreteSource.frame_writer,StateT.run_map,support_map] at projected
  obtain ⟨ordinary,called,same⟩ := projected
  have normalEq := congrArg (fun value=>value.1) same
  rcases result with ⟨raw,afterPlatform⟩
  cases raw with
  | ok value => exact ⟨value,rfl⟩
  | fail error | div => simp only [RegistrationNativeExtractedAllocation.abstractResult,reduceCtorEq] at normalEq
private theorem helper_normal (reserve : Nat→StateT P ProbComp (core.result.Result Unit E))
    (request : record_effects.RecordWriteRequest) (before : P)
    (result : RustM (core.option.Option (alloc.vec.Vec U8))×P)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformConcreteSource.helper reserve)
      (AdapterRecordHelperRouting.route (E:=E) (m:=AdapterRecordHelperRequestMonad.Program E) request).run).run before)) :
    ∃value,result.1=.ok value := by
  cases request with
  | Raw parts =>
    obtain ⟨first,second,third,same⟩ := List.length_eq_three.mp parts.property
    rcases parts with ⟨values,length⟩
    dsimp only at same
    subst values
    exact raw_normal (fun _ capacity=>reserve capacity.val) RegistrationNativePlatformConcreteSource.serializer
      first second third before result supported
  | Frame parts sequence sender =>
    obtain ⟨first,second,third,same⟩ := List.length_eq_three.mp parts.property
    rcases parts with ⟨values,length⟩
    dsimp only at same
    subst values
    exact frame_normal reserve sequence sender first second third before result supported
variable {n : Nat}
theorem write (reserve : Nat→StateT P ProbComp (core.result.Result Unit E))
    (request : record_effects.RecordWriteRequest) :
    Normal (RegistrationNativePlatformSourceBuild.write (n:=n) (RegistrationNativePlatformConcreteSource.helper reserve) request) := by
  intro before previous result supported
  rw [RegistrationNativePlatformSourceBuild.write_run,StateT.run_map,support_map] at supported
  obtain ⟨written,called,same⟩ := supported
  unfold RegistrationNativePlatformSourceCompletion.writeWith at called
  rw [StateT.run_map,support_map] at called
  obtain ⟨raw,rawCalled,rawSame⟩ := called
  obtain ⟨value,normal⟩ := helper_normal reserve request previous raw rawCalled
  subst written
  subst result
  exact ⟨value,by simpa only [AdapterRecordNativeWriter.borrow_exact] using normal⟩
theorem encode (reserve : Usize→StateT P ProbComp (core.result.Result Unit E))
    (view : registration.SignedResponseView) :
    Normal (RegistrationNativePlatformSourceBuild.encode (n:=n) (RegistrationNativePlatformConcreteSource.writer reserve) view) := by
  intro before previous result supported
  rw [RegistrationNativePlatformSourceBuild.encode_run,StateT.run_map,support_map] at supported
  obtain ⟨written,called,same⟩ := supported
  unfold RegistrationNativePlatformSourceCompletion.encodeWith at called
  by_cases admitted : RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax view)≤CborSizing.maxMessageSize
  · obtain ⟨capacity,size,source⟩ := RegistrationNativePlatformConcreteSource.response_writer reserve view admitted
    rw [source,StateT.run_map,support_map] at called
    obtain ⟨reserved,reserveCalled,writeSame⟩ := called
    subst written
    subst result
    cases reserved.1 <;> exact ⟨_,rfl⟩
  · rw [RegistrationNativePlatformConcreteSource.response_rejected reserve view (Nat.lt_of_not_ge admitted)] at called
    simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at called
    subst written
    subst result
    exact ⟨_,rfl⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceWriterNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceWriterNormal.write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceWriterNormal.write

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceWriterNormal.encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceWriterNormal.encode
