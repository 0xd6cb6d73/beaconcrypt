-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordProjection
import BeaconcryptCore.Computational.RegistrationNativePlatformRawReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace

/-! The actual allocator/raw writer source emits the selected AEAD body, tag and commitment digest, retaining the source hash cache through its literal write marker. The source trace and all intermediate states belong to one successful execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame
open BeaconcryptCore.Refinement
open BeaconcryptCore.Refinement.RegistrationRecords
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformSourceSealTrace (joint)
variable {n : Nat} {E Platform N V ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Joint callback support retains the exact original nested native/platform result. -/
theorem joint_support (work : StateT N (StateT Platform ProbComp) V)
    (value : V) (before after : N) (previous next : Platform) :
    (value, (after, next)) ∈ support ((joint work).run (before, previous)) ↔
      ((value, after), next) ∈ support ((work.run before).run previous) := by
  change (value, (after, next)) ∈ support ((fun result : (V × N) × Platform =>
    (result.1.1, (result.1.2, result.2))) <$> ((work.run before).run previous)) ↔ _
  rw [support_map]
  constructor
  · rintro ⟨⟨⟨reply, current⟩, platform⟩, called, same⟩
    simp only [Prod.mk.injEq] at same
    rcases same with ⟨rfl, rfl, rfl⟩
    exact called
  · intro called
    exact ⟨((value, after), next), called, rfl⟩

variable [primitive : AdapterSealPrimitive.Operations]

abbrev Trace (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : Local n × Platform) :=
  RegistrationNativePlatformRecordTrace.Trace
    (fun query => joint (RegistrationNativePlatformServerCompletion.records coins setup codec query))
    (fun request => joint (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request))
    (fun transcript => joint (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript))
    (fun request => joint (RegistrationNativePlatformSourceBuild.write (AdapterRecordRawBytes.helper rawAllocation serializer) request))
    initial completed before after

/-- The concrete source writer supplies exactly the actual AEAD body/tag and hash reply, and preserves the actual hash cache through its reservation and write marker. -/
theorem frame (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
    (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : Local n × Platform)
    (actual : Trace coins setup codec view failure allocation erased rawAllocation serializer initial completed before after)
    (digest : CtxRomAuth.CtxDigest) (hashed : actual.digestReply = .Some (RegistrationAuthenticationShared.digestArray digest)) :
    ∃ ciphertext tag, actual.aeadReply = .Some (ciphertext, tag) ∧
      TranscriptAuthParts.absSlice completed.ciphertext = TranscriptAuthParts.absSlice ciphertext ++ absBytes tag ++ digest.toList ∧
      actual.fourth.1.world.1.primitive.2 = after.1.world.1.primitive.2 := by
  let proxy := RegistrationNativePlatformRecordProjection.project _ _ _ _ initial completed before after actual
  obtain ⟨ciphertext, tag, replied, sealEq, encrypted, tagged, _encoded⟩ :=
    RegistrationNativeServerRecordFields.transcript _ initial completed before after proxy
  obtain ⟨bound, _boundRun, context, _sequence⟩ := RegistrationNativeServerRecordFields.context _ initial completed before after proxy
  change actual.aead.pending.seal.context = serverRecordContext initial bound at context
  obtain ⟨writer, resumed, _state, writerSeal, writerCipher, writerTag, writerCommitment⟩ :=
    server_commitment_reply_refines actual.commitmentState (RegistrationAuthenticationShared.digestArray digest)
  have hashResumed := actual.hashResumed
  rw [hashed] at hashResumed
  have writerEq : writer = actual.writer := by
    simpa only [RustM.ok.injEq, core.result.Result.Ok.injEq] using resumed.symm.trans hashResumed
  have retained : writer.pending.seal = actual.aead.pending.seal := writerSeal.trans sealEq
  have cipher := writerCipher.trans encrypted
  have tagEq := writerTag.trans tagged
  rw [writerEq] at retained cipher tagEq writerCommitment
  let parts := Std.Array.make 3#usize [ciphertext, Std.Array.to_slice tag, Std.Array.to_slice (RegistrationAuthenticationShared.digestArray digest)]
  have requested : actual.writer.request = .ok (.Raw parts) := by
    simp only [registration.ServerRecordWrite.request, record_effects.SealWrite.request,
      core.array.Array.as_slice, rust_primitives.slice.array_as_slice, retained, cipher, tagEq, writerCommitment,
      ratchet.concrete.SendSeal.impl.context, context, serverRecordContext, bind_tc_ok]
    rfl
  have requestEq : actual.writeRequest = .Raw parts := RustM.ok.inj (actual.writeRequested.symm.trans requested)
  obtain ⟨result, finished, retention⟩ := RegistrationPublication.server_seal_retention_refines actual.writer actual.writeReply
  have resultEq : result = .Ok completed := RustM.ok.inj (finished.symm.trans actual.writeResumed)
  cases resultEq
  have called := actual.writeCalled
  rw [requestEq, retention.2.2.2.1] at called
  have nested := (joint_support _ _ _ _ _ _).mp called
  obtain ⟨written, sameState⟩ := RegistrationNativePlatformRawReceipt.successful rawAllocation serializer parts completed.ciphertext
    actual.fourth.1 after.1 actual.fourth.2 after.2 nested
  have bytes := congrArg (List.map absByte) written
  refine ⟨ciphertext, tag, replied, ?_, ?_⟩
  · simpa [parts, Std.Array.make, TranscriptAuthParts.absSlice, Std.Array.to_slice,
      absBytes, RegistrationAuthenticationShared.digestArray, List.map_map, Function.comp_def, List.append_assoc] using bytes
  · rw [sameState]

end BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame.joint_support' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame.joint_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame.frame
