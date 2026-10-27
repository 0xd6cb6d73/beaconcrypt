-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxSourceSeal
import BeaconcryptCore.Computational.RawCtxNativeFramePrelude
import BeaconcryptCore.Computational.RawCtxInterpretedOpening
import BeaconcryptCore.Refinement.RecordEffects

/-! Interpret the actual extracted detached-AEAD, commitment and writer continuations for ordinary frames. Fixed-width typed primitive replies make the tag16/hash64 representation contracts explicit. Primitive semantics, native scheduling, allocation and codec correctness remain external. -/

open CoreModels Aeneas OracleComp
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RecordEffects
open BeaconcryptCore.Computational.RawCtxInterpretedOpening (bindResult)
open BeaconcryptCore.Computational.RawCtxNativeFramePrelude (sliceBytes)

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RecordEffectsSendBridge

/-- Ordinary primitive replies retain arbitrary ciphertext bytes, a tag16 and a hash64. -/
abbrev PrimitiveSpec :=
  (RawCtxSourceSeal.AeadInput →ₒ Option ((Slice Std.U8) × Std.Array Std.U8 16#usize)) +
    ((Pqxdh.Bytes →ₒ Option (Std.Array Std.U8 64#usize)) +
      (RawCtxReceive.DecodedFrame →ₒ Option Pqxdh.Bytes))

abbrev Result := ConcreteRatchetKernel × core.option.Option (record_effects.SealedRecord Pqxdh.Bytes)

def toCoreOption {α : Type} : Option α → core.option.Option α
  | none => .None
  | some value => .Some value

/-- Representation changes the replies, preserving the actual queried bytes and metadata. -/
def modelAdapter : QueryImpl RawCtxSourceSeal.SealSpec (OracleComp PrimitiveSpec)
  | .inl input => do
      let reply ← PrimitiveSpec.query (.inl input)
      pure (reply.map fun pair => (sliceBytes pair.1, absBytes pair.2))
  | .inr (.inl transcript) => do
      let reply ← PrimitiveSpec.query (.inr (.inl transcript))
      pure (reply.map absBytes)
  | .inr (.inr frame) => liftM (PrimitiveSpec.query (.inr (.inr frame)))

def inputOf (pending : SendSeal record_effects.SealFrameContext) : RawCtxSourceSend.SealInput :=
  ⟨pending.material, pending.sequence,
    ⟨sliceBytes pending.context.plaintext, pending.context.target_kid,
      pending.context.sender_kid, absBytes pending.context.associated_data⟩⟩

def plaintextBytes : record_effects.SealPlaintextRequest → Pqxdh.Bytes
  | .Single plaintext => sliceBytes plaintext
  | .Prefixed header application => absBytes header ++ sliceBytes application

def aeadQuery (request : record_effects.AeadSealRequest) : RawCtxSourceSeal.AeadInput :=
  ⟨absBytes request.key, absBytes request.nonce, absBytes request.associated_data,
    plaintextBytes request.plaintext⟩

def partsBytes (parts : Std.Array (Slice Std.U8) 3#usize) : Pqxdh.Bytes :=
  parts.val.flatMap sliceBytes

/-- Every writer reply, including failure, is finished on the actual selected send capability. -/
def executeWrite (pending : record_effects.SealWrite) :
    OracleComp PrimitiveSpec (RustM (ConcreteRatchetKernel ×
      core.option.Option (record_effects.SealedRecord Pqxdh.Bytes))) :=
  bindResult pending.request fun request =>
    match request with
    | .Raw _ => pure .div
    | .Frame parts sequence sender => do
        let written ← PrimitiveSpec.query (.inr (.inr ⟨sequence, sender, partsBytes parts⟩))
        pure (pending.finish (toCoreOption written))

/-- The transcript is erased through the actual borrowed getter before its continuation resumes. -/
def executeCommitment (erased : Std.Array Std.U8 357#usize)
    (pending : record_effects.SealCommitment) :
    OracleComp PrimitiveSpec (RustM (ConcreteRatchetKernel ×
      core.option.Option (record_effects.SealedRecord Pqxdh.Bytes))) :=
  bindResult (record_effects.SealCommitment.impl.transcript pending) fun transcript =>
  bindResult (commitment.CommitmentTranscript.as_bytes transcript) fun bytes => do
    let digest ← PrimitiveSpec.query (.inr (.inl (absBytes bytes)))
    bindResult pending.transcript_mut fun borrowed =>
    bindResult (commitment.CommitmentTranscript.as_mut_bytes borrowed.1) fun bytesBorrowed =>
    let retained := borrowed.2 (bytesBorrowed.2 erased)
    bindResult (retained.resume (toCoreOption digest)) fun next =>
      match next with
      | .Rejected kernel => pure (ok (kernel, .None))
      | .WriteRequested writer => executeWrite writer

/-- Only primitive requests are interpreted; extraction supplies every phase and failure kernel. -/
def execute (erased : Std.Array Std.U8 357#usize) (pending : record_effects.SealAead) :
    OracleComp PrimitiveSpec (RustM (ConcreteRatchetKernel ×
      core.option.Option (record_effects.SealedRecord Pqxdh.Bytes))) :=
  bindResult pending.request fun request => do
    let detached ← PrimitiveSpec.query (.inl (aeadQuery request))
    bindResult (pending.resume (toCoreOption detached)) fun next =>
      match next with
      | .Rejected kernel => pure (ok (kernel, .None))
      | .CommitmentRequested commitment => executeCommitment erased commitment

/-- Ordinary requests use the exact represented selected key, nonce, AD and caller plaintext. -/
theorem aead_request_exact (pending : record_effects.SealAead)
    (ordinary : pending.seal.context.prefix = .None) :
    (aeadQuery <$> pending.request) = ok (RawCtxSourceSeal.aeadInput (inputOf pending.seal)) := by
  simp only [record_effects.SealAead.request, SendSeal.impl.material, SendSeal.impl.context,
    RatchetMaterial.impl.key, RatchetMaterial.impl.nonce, RatchetKey.as_bytes,
    RatchetNonce.as_bytes, record_effects.SealFrameContext.plaintext_request, ordinary,
    bind_tc_ok]
  rfl

/-- The functional frame writer receives exact ordered body/tag/commitment bytes and source metadata. -/
theorem executeWrite_exact (pending : record_effects.SealWrite)
    (framed : pending.seal.context.encoding = .Frame) :
    executeWrite pending = (do
      let written ← PrimitiveSpec.query (.inr (.inr
        (RawCtxSourceSeal.frame (inputOf pending.seal) (sliceBytes pending.ciphertext)
          (absBytes pending.tag) (absBytes pending.commitment))))
      pure (pending.finish (toCoreOption written))) := by
  simp only [executeWrite, record_effects.SealWrite.request, core.array.Array.as_slice,
    SendSeal.impl.context, SendSeal.impl.sequence, framed, bind_tc_ok, bindResult,
    rust_primitives.slice.array_as_slice]
  change (do
    let written ← PrimitiveSpec.query (.inr (.inr
      (⟨pending.seal.sequence, pending.seal.context.sender_kid, sliceBytes pending.ciphertext ++
          (absBytes pending.tag ++ (absBytes pending.commitment ++ []))⟩ : RawCtxReceive.DecodedFrame)))
    pure (pending.finish (toCoreOption written)) : OracleComp PrimitiveSpec (RustM Result)) = _
  apply congrArg (fun payload : Pqxdh.Bytes => (do
    let written ← PrimitiveSpec.query (.inr (.inr
      ⟨pending.seal.sequence, pending.seal.context.sender_kid, payload⟩))
    pure (pending.finish (toCoreOption written)) : OracleComp PrimitiveSpec (RustM Result)))
  simp only [List.append_nil, List.append_assoc]

def finishResult (pending : SendSeal record_effects.SealFrameContext)
    (written : Option Pqxdh.Bytes) : RustM (ConcreteRatchetKernel ×
      core.option.Option (record_effects.SealedRecord Pqxdh.Bytes)) :=
  pending.finish (toCoreOption (written.map fun ciphertext =>
    ⟨ciphertext, pending.context.target_kid, pending.sequence⟩))

/-- Finishing either writer outcome is exactly the preexisting affine send completion. -/
theorem write_finish_old_exact (pending : record_effects.SealWrite)
    (written : Option Pqxdh.Bytes) :
    pending.finish (toCoreOption written) = finishResult pending.seal written := by
  cases written <;> simp only [toCoreOption, seal_write_finish_exact, finishResult,
    Option.map_none, Option.map_some, SendSeal.finish_returns_interpreter_result]

/-- Erasure changes no retained operand, and all three hash/writer reply failures stay explicit. -/
theorem executeCommitment_exact (erased : Std.Array Std.U8 357#usize)
    (pending : record_effects.SealCommitment)
    (framed : pending.seal.context.encoding = .Frame) :
    executeCommitment erased pending = (do
      let digest ← PrimitiveSpec.query (.inr (.inl (absBytes pending.transcript.bytes)))
      match digest with
      | none => pure (finishResult pending.seal none)
      | some digest => do
          let written ← PrimitiveSpec.query (.inr (.inr
            (RawCtxSourceSeal.frame (inputOf pending.seal) (sliceBytes pending.ciphertext)
              (absBytes pending.tag) (absBytes digest))))
          pure (finishResult pending.seal written)) := by
  simp only [executeCommitment, record_effects.SealCommitment.impl.transcript,
    commitment.CommitmentTranscript.as_bytes, record_effects.SealCommitment.transcript_mut,
    commitment.CommitmentTranscript.as_mut_bytes, bindResult]
  refine bind_congr fun digest => ?_
  cases digest with
  | none => simp only [toCoreOption, seal_commitment_missing_exact, finishResult,
      Option.map_none, SendSeal.finish_returns_interpreter_result]
  | some digest =>
      simp only [toCoreOption, seal_commitment_supplied_exact]
      simpa only [write_finish_old_exact] using
        executeWrite_exact ⟨pending.seal, pending.ciphertext, pending.tag, digest⟩ framed

/-- The typed primitive ledger keeps AEAD, hash and writer failures in their actual order. -/
def sealProgram (pending : SendSeal record_effects.SealFrameContext) :
    OracleComp PrimitiveSpec (RustM Result) := do
  let detached ← PrimitiveSpec.query (.inl (RawCtxSourceSeal.aeadInput (inputOf pending)))
  match detached with
  | none => pure (finishResult pending none)
  | some (body, tag) => do
      let digest ← PrimitiveSpec.query (.inr (.inl
        (RawCtxSourceSeal.hashInput (inputOf pending) (absBytes tag))))
      match digest with
      | none => pure (finishResult pending none)
      | some digest => do
          let written ← PrimitiveSpec.query (.inr (.inr
            (RawCtxSourceSeal.frame (inputOf pending) (sliceBytes body)
              (absBytes tag) (absBytes digest))))
          pure (finishResult pending written)

/-- The actual extracted continuation program is exactly the byte-level primitive ledger. -/
theorem execute_exact (erased : Std.Array Std.U8 357#usize) (pending : record_effects.SealAead)
    (ordinary : pending.seal.context.prefix = .None)
    (framed : pending.seal.context.encoding = .Frame) :
    execute erased pending = sealProgram pending.seal := by
  simp only [execute, record_effects.SealAead.request, SendSeal.impl.material,
    SendSeal.impl.context, RatchetMaterial.impl.key, RatchetMaterial.impl.nonce,
    RatchetKey.as_bytes, RatchetNonce.as_bytes, record_effects.SealFrameContext.plaintext_request,
    ordinary, bind_tc_ok, bindResult]
  rw [sealProgram]
  refine bind_congr fun detached => ?_
  cases detached with
  | none => simp only [toCoreOption, seal_aead_missing_exact, finishResult,
      Option.map_none, SendSeal.finish_returns_interpreter_result]
  | some pair =>
      rcases pair with ⟨body, tag⟩
      obtain ⟨next, run, sameSeal, sameBody, sameTag, transcript⟩ :=
        seal_aead_supplied_exact pending body tag
      simp only [toCoreOption, run]
      have hashEq : absBytes next.transcript.bytes =
          RawCtxSourceSeal.hashInput (inputOf pending.seal) (absBytes tag) := by
        simpa only [RawCtxSourceSeal.hashInput, inputOf,
          BeaconcryptCore.Refinement.RepresentationBridge.absMaterial] using transcript
      rw [executeCommitment_exact erased next (by simpa only [sameSeal] using framed),
        sameSeal, sameBody, sameTag, hashEq]
      refine bind_congr fun digest => ?_
      cases digest <;> rfl


/-- Typed fixed-width reply representation supplies exactly the existing optional source sealing model. -/
theorem model_exact (pending : SendSeal record_effects.SealFrameContext) :
    (do
      let written ← simulateQ modelAdapter (RawCtxSourceSeal.sealInput (inputOf pending))
      pure (finishResult pending written)) = sealProgram pending := by
  rw [RawCtxSourceSeal.sealInput, simulateQ_bind, simulateQ_spec_query]
  simp only [modelAdapter, bind_assoc, pure_bind]
  rw [sealProgram]
  refine bind_congr fun detached => ?_
  cases detached with
  | none => simp only [Option.map_none, simulateQ_pure, pure_bind]
  | some pair =>
      rcases pair with ⟨body, tag⟩
      simp only [Option.map_some,
        show (inputOf pending).context.associatedData.length = 281 from absBytes_length pending.context.associated_data,
        absBytes_length, ite_true]
      rw [ite_eq_left (by decide : (16#usize).val = 16)]
      rw [simulateQ_bind, simulateQ_spec_query]
      simp only [modelAdapter, bind_assoc, pure_bind]
      refine bind_congr fun digest => ?_
      cases digest with
      | none => simp only [Option.map_none, simulateQ_pure, pure_bind]
      | some digest =>
          simp only [Option.map_some, simulateQ_spec_query, modelAdapter]
          refine bind_congr fun written => ?_
          cases written <;> rfl

/-- The extracted ordinary-frame send refines the existing sealing model for every represented primitive reply. -/
theorem source_seal_model (erased : Std.Array Std.U8 357#usize) (pending : record_effects.SealAead)
    (ordinary : pending.seal.context.prefix = .None)
    (framed : pending.seal.context.encoding = .Frame) :
    execute erased pending = (do
      let written ← simulateQ modelAdapter (RawCtxSourceSeal.sealInput (inputOf pending.seal))
      pure (finishResult pending.seal written)) :=
  (execute_exact erased pending ordinary framed).trans (model_exact pending.seal).symm

/-- Every optional result consumes exactly the entire preexisting advanced send kernel and retains target/sequence metadata. -/
theorem finishResult_exact (pending : SendSeal record_effects.SealFrameContext)
    (written : Option Pqxdh.Bytes) :
    finishResult pending written = ok (pending.advanced,
      toCoreOption (written.map fun ciphertext =>
        (⟨ciphertext, pending.context.target_kid, pending.sequence⟩ : record_effects.SealedRecord Pqxdh.Bytes))) :=
  SendSeal.finish_returns_interpreter_result pending _

/-- Arbitrary stateful probabilistic primitives retain exactly the same complete state, including on failure. -/
theorem stateful_execution {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (erased : Std.Array Std.U8 357#usize) (pending : record_effects.SealAead)
    (ordinary : pending.seal.context.prefix = .None)
    (framed : pending.seal.context.encoding = .Frame) (state : PrimitiveState) :
    (simulateQ impl (execute erased pending)).run state =
      (simulateQ impl (do
        let written ← simulateQ modelAdapter (RawCtxSourceSeal.sealInput (inputOf pending.seal))
        pure (finishResult pending.seal written))).run state :=
  congrArg (fun program => (simulateQ impl program).run state)
    (source_seal_model erased pending ordinary framed)

end BeaconcryptCore.Computational.RecordEffectsSendBridge

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.aead_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.aead_request_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.executeWrite_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.executeWrite_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.write_finish_old_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.write_finish_old_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.executeCommitment_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.executeCommitment_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.execute_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.execute_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.model_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.model_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.source_seal_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.source_seal_model

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.finishResult_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.finishResult_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsSendBridge.stateful_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsSendBridge.stateful_execution
