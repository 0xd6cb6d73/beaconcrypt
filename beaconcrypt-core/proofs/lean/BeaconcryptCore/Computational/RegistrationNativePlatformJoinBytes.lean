-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Refinement.AdapterSealJoinBytes

/-! The actual source two-part prefixed seal join uses one public empty-vector reservation and retains the private native state verbatim. Successful reservation yields exactly prefix bytes followed by application bytes, derived from actual standard clone operations. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {E Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem joined (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : AdapterSealPrimitive.Operations.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)
    (prefixBytes : Std.Array U8 8#usize) (application : Slice U8) (capacity : Usize)
    (length : prefixBytes.val.length + application.val.length = capacity.val) (before : State n Auxiliary) :
    (simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation)
      (AdapterSealNative.joined E prefixBytes application)).run before =
      (fun result => ((do
        let reply ← result
        match reply with
        | .Err _ => .ok none
        | .Ok _ => .ok (some ⟨prefixBytes.val ++ application.val, by
            rw [List.length_append, length]
            scalar_tac⟩)), before)) <$> allocation (Slice.new U8) capacity := by
  let first : Slice U8 := Std.Array.to_slice prefixBytes
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have addSecond := FrameCodecWriteBytes.checked_add_some first.len application.len capacity (by simpa only [first, Std.Array.to_slice, Slice.len_val, Slice.length] using length)
  have indices := AdapterSealFixedParts.indices2 first application
  dsimp only [first] at addFirst addSecond indices
  unfold AdapterSealNative.joined AdapterSealRequestMonad.Lifted.join
  simp only [AdapterSealJoinRequestExtraction.join, AdapterSealJoinRequestMonad.Lifted.index,
    AdapterSealJoinRequestMonad.Lifted.len, AdapterSealJoinRequestMonad.Lifted.checkedAdd,
    AdapterSealJoinRequestMonad.Lifted.branch, AdapterSealJoinRequestMonad.Lifted.new,
    indices.1, indices.2]
  simp only [AdapterSealRequestMonad.Program.run_bind, AdapterSealRequestMonad.Program.run_lift,
    simulateQ_bind, pure_bind,
    core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, addSecond,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, bind_tc_ok]
  simp only [AdapterSealRequestMonad.Operations.reserve, AdapterSealRequestMonad.Program.query,
    simulateQ_spec_query, AdapterSealNative.native, RegistrationNativePlatformSourceSeal.handler,
    StateT.run_bind, StateT.run_lift, RegistrationNativePlatformSourceSeal.reserve, bind_map_left]
  simp only [bind_assoc, pure_bind]
  rw [← bind_pure_comp]
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok reply =>
      cases reply with
      | Err error =>
          change (simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation)
            (simulateQ (AdapterSealNative.native (E := E))
              (pure (RustM.ok (none : Option (alloc.vec.Vec U8)))))).run before = pure (.ok none, before)
          rw [simulateQ_pure, simulateQ_pure]
          rfl
      | Ok success =>
          change (simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation)
            (simulateQ (AdapterSealNative.native (E := E)) ((do
              let middle ← AdapterSealJoinRequestMonad.Lifted.extend (Slice.new U8) (Std.Array.to_slice prefixBytes)
              let final ← AdapterSealJoinRequestMonad.Lifted.extend middle application
              pure (some final) : AdapterSealRequestMonad.Program E (Option (alloc.vec.Vec U8))).run))).run before = _
          have firstCopy : alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone (Slice.new U8)
              (Std.Array.to_slice prefixBytes) = .ok (Std.Array.to_slice prefixBytes) :=
            AdapterByteVector.extend_bytes (Slice.new U8) (Std.Array.to_slice prefixBytes) (by
              simpa only [Slice.new, List.length_nil, Nat.zero_add] using (Std.Array.to_slice prefixBytes).property)
          have secondCopy := AdapterByteVector.extend_bytes (Std.Array.to_slice prefixBytes) application (by
            change prefixBytes.val.length + application.val.length ≤ Usize.max
            rw [length]
            scalar_tac)
          simp only [AdapterSealJoinRequestMonad.Lifted.extend, AdapterSealRequestMonad.Program.run_bind,
            AdapterSealRequestMonad.Program.run_lift, AdapterSealRequestMonad.Program.run_pure,
            firstCopy, secondCopy, pure_bind, simulateQ_pure]
          rfl

def marked (request : record_effects.AeadSealRequest) (before : State n Auxiliary) : State n Auxiliary :=
  { before with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.seal request)] }

theorem sealing_prefixed (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (request : record_effects.AeadSealRequest)
    (prefixBytes : Std.Array U8 8#usize) (application : Slice U8) (capacity : Usize)
    (length : prefixBytes.val.length + application.val.length = capacity.val)
    (prefixed : request.plaintext = .Prefixed prefixBytes application) (key : primitive.Key) (nonce : primitive.Nonce)
    (keyRun : AdapterSealRequestMonad.Lifted.key (m := RustM) request.key = .ok key)
    (nonceRun : AdapterSealRequestMonad.Lifted.nonce (m := RustM) request.nonce = .ok nonce)
    (before : State n Auxiliary) :
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request).run before = (do
      let result ← allocation (Slice.new U8) capacity
      match result with
      | .fail error => pure (.fail error, marked request before)
      | .div => pure (.div, marked request before)
      | .ok (.Err _) => pure (.ok none, marked request before)
      | .ok (.Ok _) => do
          let sealed ← (RegistrationNativePlatformSourceSeal.aead coins setup codec view failure
            ⟨prefixBytes.val ++ application.val, by rw [List.length_append, length]; scalar_tac⟩
            (some (Std.Array.to_slice request.associated_data)) nonce key).run before
          pure (AdapterSealNative.finish sealed.1, marked request sealed.2)) := by
  unfold RegistrationNativePlatformSourceSeal.sealing AdapterSealNative.execute
  simp only [keyRun, nonceRun, AdapterSealNative.continueWith, prefixed, simulateQ_bind, StateT.run_bind]
  rw [joined coins setup codec view failure allocation prefixBytes application capacity length before]
  rw [bind_map_left]
  rw [bind_assoc]
  apply bind_congr
  intro result
  cases result with
  | fail error =>
      simp only [bind_tc_fail, simulateQ_pure, StateT.run_pure, StateT.run_modify, pure_bind, marked]
  | div =>
      simp only [bind_tc_div, simulateQ_pure, StateT.run_pure, StateT.run_modify, pure_bind, marked]
  | ok reply =>
      cases reply with
      | Err error =>
          simp only [bind_tc_ok, simulateQ_pure, StateT.run_pure, StateT.run_modify, pure_bind, marked]
      | Ok success =>
          simp only [bind_tc_ok, AdapterSealNative.aead, simulateQ_map, simulateQ_spec_query,
            RegistrationNativePlatformSourceSeal.handler, StateT.run_map, StateT.run_pure, StateT.run_modify,
            marked, bind_map_left, pure_bind]

omit [Monad m] [LawfulMonad m] in
theorem input_correct (view : RegistrationNativePlatformSourceSeal.KeyView)
    (correct : view.Correct) (request : record_effects.AeadSealRequest)
    (prefixBytes : Std.Array U8 8#usize) (application : Slice U8) (capacity : Usize)
    (length : prefixBytes.val.length + application.val.length = capacity.val)
    (prefixed : request.plaintext = .Prefixed prefixBytes application) (key : primitive.Key) (nonce : primitive.Nonce)
    (keyRun : AdapterSealRequestMonad.Lifted.key (m := RustM) request.key = .ok key)
    (nonceRun : AdapterSealRequestMonad.Lifted.nonce (m := RustM) request.nonce = .ok nonce) :
    RegistrationNativePlatformSourceSeal.input view
      ⟨prefixBytes.val ++ application.val, by rw [List.length_append, length]; scalar_tac⟩
      (some (Std.Array.to_slice request.associated_data)) nonce key = RegistrationRecordPrimitives.sealInput request := by
  have keyBytes : view.key key = request.key := correct.1 request.key key keyRun
  have nonceBytes : view.nonce nonce = request.nonce := correct.2 request.nonce nonce nonceRun
  unfold RegistrationNativePlatformSourceSeal.input RegistrationRecordPrimitives.sealInput
  rw [keyBytes, nonceBytes, prefixed]
  simp only [RegistrationRecordPrimitives.plaintextBytes, TranscriptAuthParts.absSlice, List.map_append]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes.joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes.joined

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes.sealing_prefixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes.sealing_prefixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes.input_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJoinBytes.input_correct
