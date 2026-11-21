-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative
import BeaconcryptCore.Refinement.AdapterSealJoinBytes
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealNormal
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSourceBuildNormal (Normal)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {P E Auxiliary I KemSK Reader Response : Type} {base : OracleSpec I}
variable (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
private theorem joined_run (first second : Slice U8) (capacity : Usize)
    (length : first.val.length+second.val.length=capacity.val) :
    simulateQ (RegistrationNativePlatformSourceSeal.handler (n:=n) (Auxiliary:=Auxiliary) coins setup codec view failure allocation)
      (simulateQ AdapterSealNative.native
        (AdapterSealRequestMonad.Lifted.join (E:=E) (m:=AdapterSealRequestMonad.Program E)
          (Std.Array.make 2#usize [first,second])).run) =
    StateT.lift (AdapterSealJoinBytes.join allocation first second).run := by
  rw [AdapterSealJoinBytes.join_run allocation first second capacity length]
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq,Nat.zero_add])
  have addSecond := FrameCodecWriteBytes.checked_add_some first.len second.len capacity (by simpa only [Slice.len_val,Slice.length] using length)
  have indices := AdapterSealFixedParts.indices2 first second
  simp only [AdapterSealRequestMonad.Lifted.join,AdapterSealJoinRequestExtraction.join,
    AdapterSealJoinRequestMonad.Lifted.index,AdapterSealJoinRequestMonad.Lifted.len,
    AdapterSealJoinRequestMonad.Lifted.checkedAdd,AdapterSealJoinRequestMonad.Lifted.branch,
    AdapterSealJoinRequestMonad.Lifted.new,indices.1,indices.2,
    AdapterSealRequestMonad.Program.run_bind,AdapterSealRequestMonad.Program.run_lift,
    pure_bind,core.slice.Slice.len,rust_primitives.slice.slice_length,addFirst,addSecond,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    alloc.vec.Vec.new,rust_primitives.sequence.seq_empty,bind_tc_ok]
  simp only [AdapterSealRequestMonad.Operations.reserve,
    AdapterSealRequestMonad.Program.query,simulateQ_bind,simulateQ_spec_query,
    AdapterSealNative.native,RegistrationNativePlatformSourceSeal.handler]
  apply StateT.ext
  intro before
  apply StateT.ext
  intro previous
  simp only [RegistrationNativePlatformSourceSeal.reserve,StateT.run_bind,StateT.run_lift,
    StateT.run_pure,bind_map_left,bind_assoc,pure_bind]
  apply bind_congr
  rintro ⟨result,middle⟩
  cases result with
  | fail error => simp only [bind_tc_fail,simulateQ_pure,StateT.run_pure]
  | div => simp only [bind_tc_div,simulateQ_pure,StateT.run_pure]
  | ok reply =>
    cases reply with
    | Err error =>
      simp only [bind_tc_ok,AdapterSealJoinRequestMonad.Lifted.resultOk,
        core.result.Result.ok,AdapterSealRequestMonad.Program.run_lift,
        AdapterSealJoinRequestMonad.Lifted.fromResidual,simulateQ_pure,StateT.run_pure,pure_bind]
      rfl
    | Ok success =>
      have firstCopy : alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone (Slice.new U8) first=.ok first :=
        AdapterByteVector.extend_bytes (Slice.new U8) first (by simpa only [Slice.new,List.length_nil,Nat.zero_add] using first.property)
      have secondCopy := AdapterByteVector.extend_bytes first second (by rw [length];scalar_tac)
      simp only [bind_tc_ok,AdapterSealJoinRequestMonad.Lifted.resultOk,
        core.result.Result.ok,AdapterSealRequestMonad.Program.run_lift,pure_bind,
        AdapterSealJoinRequestMonad.Lifted.extend,AdapterSealRequestMonad.Program.run_bind,
        AdapterSealRequestMonad.Program.run_pure,firstCopy,secondCopy,simulateQ_pure,StateT.run_pure]
omit primitives in
private theorem pure_normal {S X : Type} (value : X) : Normal (S:=S) (P:=P) (pure (.ok value)) := by
  intro before previous result supported
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  subst result
  exact ⟨value,rfl⟩
private theorem joined_normal
    (allocate : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E))
    (first second : Slice U8) :
    Normal (simulateQ (RegistrationNativePlatformSourceSeal.handler (n:=n) (Auxiliary:=Auxiliary) coins setup codec view failure
      (fun before capacity=>RustM.ok <$>allocate before capacity))
      (simulateQ AdapterSealNative.native
        (AdapterSealRequestMonad.Lifted.join (E:=E) (m:=AdapterSealRequestMonad.Program E)
          (Std.Array.make 2#usize [first,second])).run)) := by
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq,Nat.zero_add])
  have indices := AdapterSealFixedParts.indices2 first second
  obtain ⟨capacity,capacityRun,size⟩ := Transport.checked_add_exact first.len second.len
  cases capacity with
  | none =>
    have stopped : simulateQ AdapterSealNative.native
        (AdapterSealRequestMonad.Lifted.join (E:=E) (m:=AdapterSealRequestMonad.Program E)
          (Std.Array.make 2#usize [first,second])).run = pure (.ok .None) := by
      simp only [AdapterSealRequestMonad.Lifted.join,AdapterSealJoinRequestExtraction.join,
        AdapterSealJoinRequestMonad.Lifted.index,AdapterSealJoinRequestMonad.Lifted.len,
        AdapterSealJoinRequestMonad.Lifted.checkedAdd,AdapterSealJoinRequestMonad.Lifted.branch,
        indices.1,indices.2,AdapterSealRequestMonad.Program.run_bind,
        AdapterSealRequestMonad.Program.run_lift,pure_bind,core.slice.Slice.len,
        rust_primitives.slice.slice_length,addFirst,capacityRun,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        AdapterSealJoinRequestMonad.Lifted.fromResidual]
      rfl
    rw [stopped,simulateQ_pure]
    exact pure_normal _
  | some capacity =>
    have length : first.val.length+second.val.length=capacity.val := by
      simp only [Transport.absLength,Slice.len_val,Slice.length] at size
      split_ifs at size with room
      exact (Option.some.inj size).symm
    rw [joined_run coins setup codec view failure _ first second capacity length,
      AdapterSealJoinBytes.join_run _ first second capacity length]
    simp only [bind_map_left,bind_tc_ok]
    intro before previous result supported
    simp only [StateT.run_lift,StateT.run_map,
      bind_pure_comp,Functor.map_map,support_map] at supported
    obtain ⟨allocated,called,same⟩ := supported
    subst result
    rcases allocated with ⟨allocationReply,afterPlatform⟩
    cases allocationReply <;> exact ⟨_,rfl⟩
private theorem aead_normal (allocate : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E))
    (plaintext : Slice U8) (associated : Std.Array U8 151#usize)
    (nonce : primitives.Nonce) (key : primitives.Key) :
    Normal (simulateQ (RegistrationNativePlatformSourceSeal.handler (n:=n) (Auxiliary:=Auxiliary) coins setup codec view failure
      (fun before capacity=>RustM.ok <$>allocate before capacity)) (AdapterSealNative.aead E plaintext associated nonce key)) := by
  intro before previous result supported
  rw [AdapterSealNative.aead,simulateQ_map,simulateQ_spec_query] at supported
  simp only [RegistrationNativePlatformSourceSeal.handler,StateT.run_map] at supported
  rw [RegistrationNativePlatformSourceSeal.aead_run,StateT.run_map] at supported
  simp only [Functor.map_map,support_map] at supported
  obtain ⟨sealed,called,same⟩ := supported
  subst result
  change ∃value,AdapterSealNative.finish (.ok (RegistrationNativePlatformSourceSeal.detached failure sealed.1.1))=.ok value
  cases detachedEq : RegistrationNativePlatformSourceSeal.detached failure sealed.1.1 <;> exact ⟨_,rfl⟩
omit primitives in
private theorem bind_ok {S X Y : Type} (work : StateT S (StateT P ProbComp) (RustM X)) (safe : Normal work)
    (next : RustM X→StateT S (StateT P ProbComp) (RustM Y))
    (continued : ∀value,Normal (next (.ok value))) : Normal (work >>= next) := by
  intro before previous result reached
  simp only [StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨middle,called,finished⟩ := reached
  obtain ⟨value,normal⟩ := safe before previous middle called
  rw [normal] at finished
  exact continued value middle.1.2 middle.2 result finished

theorem execute
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (allocate : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E))
    (request : record_effects.AeadSealRequest) :
    Normal (simulateQ (RegistrationNativePlatformSourceSeal.handler (n:=n) (Auxiliary:=Auxiliary) coins setup codec view failure
      (fun before capacity=>RustM.ok <$>allocate before capacity)) (AdapterSealNative.execute E request)) := by
  obtain ⟨nativeKey,keyRun,_keyView⟩ := converted.key request.key
  obtain ⟨nativeNonce,nonceRun,_nonceView⟩ := converted.nonce request.nonce
  simp only [AdapterSealNative.execute,AdapterSealRequestMonad.Lifted.key,
    AdapterSealRequestMonad.Lifted.nonce,AdapterRecordRequestMonad.liftRust,
    core.convert.Into.Blanket.into,
    beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832,
    beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812,
    keyRun,nonceRun,AdapterSealNative.continueWith]
  cases form : request.plaintext with
  | Single plaintext => exact aead_normal coins setup codec view failure allocate plaintext request.associated_data nativeNonce nativeKey
  | Prefixed prefixBytes application =>
    rw [simulateQ_bind]
    apply bind_ok _ (joined_normal coins setup codec view failure allocate (Std.Array.to_slice prefixBytes) application)
    intro optional
    cases optional with
    | none => simpa only [AdapterSealNative.continueWith,simulateQ_pure] using pure_normal (S:=RegistrationWorldAgreement.State n Auxiliary) (P:=P) (core.option.Option.None : AdapterSealNative.Output)
    | some joined => exact aead_normal coins setup codec view failure allocate joined request.associated_data nativeNonce nativeKey

theorem sealing
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (allocate : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E))
    (request : record_effects.AeadSealRequest) :
    Normal (RegistrationNativePlatformSourceSeal.sealing (n:=n) (Auxiliary:=Auxiliary) coins setup codec view failure
      (fun before capacity=>RustM.ok <$>allocate before capacity) request) := by
  intro before previous result supported
  unfold RegistrationNativePlatformSourceSeal.sealing at supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,later⟩ := supported
  obtain ⟨value,normal⟩ := execute coins setup codec view failure converted allocate request before previous middle called
  simp only [StateT.run_modify,StateT.run_pure,support_pure,Set.mem_singleton_iff] at later
  obtain ⟨between,rfl,rfl⟩ := later
  exact ⟨value,normal⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealNormal.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealNormal.execute

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealNormal.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealNormal.sealing
