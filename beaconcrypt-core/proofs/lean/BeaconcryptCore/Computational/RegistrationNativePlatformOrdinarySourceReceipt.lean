-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriterTotal
import BeaconcryptCore.Computational.RecordEffectsSendBridge
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
/-! Concrete source children for the extracted ordinary send driver expand the actual detached-seal and Frame3 writer request programs. The external service sees only public reservation capacity. Typed AEAD/tag and hash replies are primitive representation interfaces; fixed-array conversion is a narrow primitive functional contract. All callbacks and continuations share the same monad. The optional after-attempt action is a trusted analysis receipt, pure by default; writing_source removes that default and attempted_source derives the separate counter interpretation on every Rust outcome. It is not an added Rust source call. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open PqxdhRefinement
variable {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}
variable [primitives : AdapterSealPrimitive.Operations]

open RegistrationNativePlatformOrdinarySourceNative (Sealed Conversion sealing sealing_single afterAttempt hashing abstractCore abstractOutput)

def frameOfRequest : record_effects.RecordWriteRequest→Option RawCtxReceive.DecodedFrame
  | .Frame parts sequence sender=>some ⟨sequence,sender,parts.val.flatMap TranscriptAuthParts.absSlice⟩
  | _=>none
omit primitives in
/-- A literal source Frame3 request records exactly its ciphertext, tag and commitment chunks. -/
theorem receipt_frame (sequence sender : U64) (first second third : Slice U8) :
    frameOfRequest (.Frame (Std.Array.make 3#usize [first,second,third]) sequence sender)=
      some ⟨sequence,sender,TranscriptAuthParts.absSlice first++TranscriptAuthParts.absSlice second++TranscriptAuthParts.absSlice third⟩ := by
  change some (⟨sequence,sender,TranscriptAuthParts.absSlice first++(TranscriptAuthParts.absSlice second++(TranscriptAuthParts.absSlice third++[]))⟩ : RawCtxReceive.DecodedFrame)=_
  simp only [List.append_nil,List.append_assoc]

def writing [FrameDispatchFallback.Operations] (reserve : Nat→m (core.result.Result Unit E))
    (request : record_effects.RecordWriteRequest) (receipt : RawCtxReceive.DecodedFrame→m Unit) :=
  RegistrationNativePlatformOrdinarySourceNative.writing reserve request
    (match frameOfRequest request with | none=>pure () | some frame=>receipt frame)

def native (aead : RawCtxSourceSeal.AeadInput→m Sealed)
    (hash : Pqxdh.Bytes→m (Option (Std.Array U8 64#usize))) (reserve : Nat→m (core.result.Result Unit E))
    (receipt : RawCtxReceive.DecodedFrame→m Unit) : QueryImpl RecordEffectsSendBridge.PrimitiveSpec m
  | .inl input=>aead input
  | .inr (.inl bytes)=>hash bytes
  | .inr (.inr frame)=>afterAttempt (receipt frame) (RegistrationNativePlatformOrdinaryWriter.write reserve frame)

omit primitives in
/-- The exact pending source writer chooses its own frame-dependent analysis receipt after retaining every actual Rust result. -/
theorem fromWrite [FrameDispatchFallback.Operations]
    (reserve : Nat→m (core.result.Result Unit E)) (pending : record_effects.SealWrite)
    (framed : pending.seal.context.encoding=.Frame) (receipt : RawCtxReceive.DecodedFrame→m Unit) :
    abstractCore <$> (RegistrationNativePlatformOrdinarySend.fromWrite (fun request=>writing reserve request receipt) pending).run=(do
      let written←RegistrationNativePlatformOrdinaryWriter.write reserve
        (RawCtxSourceSeal.frame (RecordEffectsSendBridge.inputOf pending.seal)
          (TranscriptAuthParts.absSlice pending.ciphertext) (absBytes pending.tag) (absBytes pending.commitment))
      receipt (RawCtxSourceSeal.frame (RecordEffectsSendBridge.inputOf pending.seal)
          (TranscriptAuthParts.absSlice pending.ciphertext) (absBytes pending.tag) (absBytes pending.commitment))
      pure (RecordEffectsSendBridge.finishResult pending.seal written)) := by
  convert RegistrationNativePlatformOrdinarySourceNative.fromWrite reserve pending framed
    (receipt (RawCtxSourceSeal.frame (RecordEffectsSendBridge.inputOf pending.seal)
      (TranscriptAuthParts.absSlice pending.ciphertext) (absBytes pending.tag) (absBytes pending.commitment))) using 1
  unfold RegistrationNativePlatformOrdinarySend.fromWrite
  simp only [record_effects.SealWrite.request,framed,ratchet.concrete.SendSeal.impl.context,
    ratchet.concrete.SendSeal.impl.sequence,core.array.Array.as_slice,rust_primitives.slice.array_as_slice,
    RustT.run_bind,RustT.run_liftRust,bind_tc_ok,pure_bind,writing,receipt_frame]
  rfl
omit primitives in
/-- The actual mutable transcript return is consumed before resuming commitment and writing, preserving every shared primitive poststate. -/
theorem fromCommitment [FrameDispatchFallback.Operations]
    (aead : RawCtxSourceSeal.AeadInput → m Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (pending : record_effects.SealCommitment) (framed : pending.seal.context.encoding = .Frame) (receipt : RawCtxReceive.DecodedFrame→m Unit) :
    abstractCore <$> (RegistrationNativePlatformOrdinarySend.fromCommitment (hashing hash erased) (fun request => writing reserve request receipt) pending).run =
      simulateQ (native aead hash reserve receipt) (RecordEffectsSendBridge.executeCommitment erased.bytes pending) := by
  rw [RecordEffectsSendBridge.executeCommitment_exact erased.bytes pending framed]
  unfold RegistrationNativePlatformOrdinarySend.fromCommitment
  simp only [record_effects.SealCommitment.transcript_mut, RustT.run_bind,
    RustT.run_liftRust, pure_bind, hashing, bind_map_left, map_bind,
    simulateQ_bind, simulateQ_spec_query, native]
  apply bind_congr
  intro digest
  cases digest with
  | none =>
      simp only [RecordEffects.seal_commitment_missing_exact, RustT.run_pure, map_pure,
        abstractCore, bind_tc_ok, RecordEffectsSendBridge.finishResult_exact,
        RecordEffectsSendBridge.toCoreOption, simulateQ_pure]
      rfl
  | some digest =>
      simp only [RecordEffects.seal_commitment_supplied_exact]
      convert fromWrite reserve ⟨pending.seal, pending.ciphertext, pending.tag, digest⟩ framed receipt using 1
      simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query, native, afterAttempt, bind_assoc, pure_bind]
      rfl

/-- The complete ordinary source AEAD/commitment/writer suffix is the typed native primitive programme, including every optional rejection and public reservation poststate. -/
theorem fromAead [FrameDispatchFallback.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : Conversion view)
    (failure : primitives.Error) (aead : RawCtxSourceSeal.AeadInput → m Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (pending : record_effects.SealAead) (ordinary : pending.seal.context.prefix = .None)
    (framed : pending.seal.context.encoding = .Frame) (receipt : RawCtxReceive.DecodedFrame→m Unit) :
    abstractCore <$> (RegistrationNativePlatformOrdinarySend.fromAead
      (sealing view failure reserve aead) (hashing hash erased) (fun request => writing reserve request receipt) pending).run =
      simulateQ (native aead hash reserve receipt) (RecordEffectsSendBridge.execute erased.bytes pending) := by
  unfold RegistrationNativePlatformOrdinarySend.fromAead RecordEffectsSendBridge.execute
  simp only [record_effects.SealAead.request, ratchet.concrete.SendSeal.impl.material,
    ratchet.concrete.SendSeal.impl.context, ratchet.RatchetMaterial.impl.key,
    ratchet.RatchetMaterial.impl.nonce, ratchet.RatchetKey.as_bytes, ratchet.RatchetNonce.as_bytes,
    record_effects.SealFrameContext.plaintext_request, ordinary, bind_tc_ok,
    RustT.run_bind, RustT.run_liftRust, pure_bind, RawCtxInterpretedOpening.bindResult,
    simulateQ_bind, simulateQ_spec_query, native]
  rw [sealing_single view converted]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro detached
  cases detached with
  | none =>
      have absent : pending.resume (none : Option (Slice U8 × Std.Array U8 16#usize)) = .ok (.Rejected pending.seal.advanced) :=
        RecordEffects.seal_aead_missing_exact pending
      simp only [RecordEffectsSendBridge.toCoreOption, absent, simulateQ_pure, RustT.run_pure, map_pure, abstractCore, bind_tc_ok]
      rfl
  | some pair =>
      rcases pair with ⟨body, tag⟩
      obtain ⟨next, resumed, sameSeal, sameBody, sameTag, transcript⟩ := RecordEffects.seal_aead_supplied_exact pending body tag
      simp only [resumed, RecordEffectsSendBridge.toCoreOption]
      exact fromCommitment aead hash reserve erased next (by simpa only [sameSeal] using framed) receipt

omit primitives in
private theorem resume_context (pending : ratchet.concrete.SendKdf record_effects.SealFrameContext)
    (response : ratchet.RatchetKdfResponse) :
    (RawCtxSourceSend.resumeSend pending response).context = pending.context := by
  obtain ⟨stepped, _step, fields⟩ := RawCtxSourceSend.resumeSend_fields pending response
  rw [fields]

/-- The KDF prefix uses the exact extracted old-chain request and complete 76-byte response before the source child suffix runs. -/
theorem fromKdf [FrameDispatchFallback.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : Conversion view)
    (failure : primitives.Error) (kdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m Sealed) (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (pending : record_effects.RecordSendKdf) (ordinary : pending.pending.context.prefix = .None)
    (framed : pending.pending.context.encoding = .Frame) (receipt : RawCtxReceive.DecodedFrame→m Unit) :
    abstractCore <$> (RegistrationNativePlatformOrdinarySend.fromKdf
      (fun request => .ok <$> kdf request) (sealing view failure reserve aead)
      (hashing hash erased) (fun request => writing reserve request receipt) pending).run = (do
        let response ← kdf pending.pending.request
        simulateQ (native aead hash reserve receipt)
          (RecordEffectsSendBridge.execute erased.bytes ⟨RawCtxSourceSend.resumeSend pending.pending response⟩)) := by
  unfold RegistrationNativePlatformOrdinarySend.fromKdf
  simp only [record_effects.RecordSendKdf.request, ratchet.concrete.SendKdf.impl.request,
    RustT.run_bind, RustT.run_liftRust, pure_bind, bind_map_left, map_bind]
  apply bind_congr
  intro response
  simp only [record_effects.RecordSendKdf.resume, RawCtxSourceSend.resumeSend_exact, bind_tc_ok]
  exact fromAead view converted failure aead hash reserve erased _
    (by simpa only [resume_context] using ordinary) (by simpa only [resume_context] using framed) receipt

omit primitives in
private theorem begin_context (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) (pending : ratchet.concrete.SendKdf record_effects.SealFrameContext)
    (called : ratchet.concrete.begin_send kernel context = .ok (.SendKdfRequested pending)) : pending.context = context := by
  by_cases exhausted : kernel.refined.control.send_sequence = core.num.U64.MAX
  · rw [ratchet.concrete.begin_send_exhausted_restores_entry kernel context exhausted] at called
    cases called
  · obtain ⟨selected, started, _entry, selectedContext, _⟩ := RawCtxSourceSend.beginSend_fields kernel context exhausted
    have equal := RustM.ok.inj ((RawCtxSourceSend.beginSend_exact kernel context).symm.trans called)
    rw [started] at equal
    cases equal
    exact selectedContext

omit primitives in
private theorem record_context (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) (pending : record_effects.RecordSendKdf)
    (called : record_effects.begin_record_send kernel context = .ok (.KdfRequested pending)) :
    pending.pending.context = context := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty context.plaintext = .ok result := ⟨_, rfl⟩
  obtain ⟨start, startRun⟩ := ratchet.concrete.begin_send_total kernel context
  obtain ⟨noPrefix, prefixRun⟩ : ∃ result, core.option.Option.is_none context.prefix = .ok result := by
    cases context.prefix <;> exact ⟨_, rfl⟩
  cases start with
  | SendExhausted entry sequence =>
      cases empty <;> cases noPrefix <;> simp [record_effects.begin_record_send, emptyRun, prefixRun, startRun] at called
  | SendKdfRequested selected =>
      have selectedContext := begin_context kernel context selected startRun
      cases empty <;> cases noPrefix <;>
        simp only [record_effects.begin_record_send, emptyRun, prefixRun, startRun, bind_tc_ok, ite_true] at called
      all_goals cases called
      all_goals exact selectedContext

def abstractOutput (result : RustM AdapterRecordStatefulSend.Result) : RustM RecordEffectsSendBridge.Result := do
  let value ← result
  .ok (value.1, _root_.Option.map (fun record =>
    (⟨TranscriptAuthParts.absSlice record.ciphertext, record.key_id, record.seq⟩ : record_effects.SealedRecord Pqxdh.Bytes)) value.2)

omit primitives in
private theorem render_output (value : RegistrationNativePlatformOrdinarySend.Result) :
    abstractOutput <$> (RegistrationNativePlatformOrdinarySourceDriver.render (m := m) value).run =
      pure (abstractCore (.ok value)) := by
  rcases value with ⟨kernel, encrypted⟩
  cases encrypted <;>
    simp only [RegistrationNativePlatformOrdinarySourceDriver.render,
      AdapterRecordSendRequestMonad.Lifted.outputMap, core.option.Option.map,
      RustT.run_bind, RustT.run_liftRust, RustT.run_pure, pure_bind, map_pure,
      beaconcrypt_record_send.ratchet.execute_record_send.closure.Insts.CoreOpsFunctionFnOnceTupleSealedRecordVecU8Encrypted.call_once,
      bind_tc_ok]
  all_goals rfl

omit primitives in
private theorem render_bind (work : RustT m RegistrationNativePlatformOrdinarySend.Result) :
    abstractOutput <$> (work >>= RegistrationNativePlatformOrdinarySourceDriver.render).run =
      abstractCore <$> work.run := by
  rw [RustT.run_bind, map_bind, ← bind_pure_comp]
  apply bind_congr
  intro result
  cases result with
  | fail error | div => simp only [map_pure]; rfl
  | ok value => exact render_output value

def callbacks [FrameDispatchFallback.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (kdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m Sealed) (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript) (receipt : RawCtxReceive.DecodedFrame→m Unit) :
    QueryImpl AdapterRecordSendRequestMonad.Spec m
  | .kdf request => .ok <$> kdf request
  | .sealing request => sealing view failure reserve aead request
  | .hash transcript => hashing hash erased transcript
  | .writer request => writing reserve request receipt

noncomputable def byteController
    (kdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m Sealed) (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E))
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) (receipt : RawCtxReceive.DecodedFrame→m Unit) : m (RustM RecordEffectsSendBridge.Result) :=
  match record_effects.begin_record_send kernel context with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Rejected entry) => pure (.ok (entry, .None))
  | .ok (.KdfRequested pending) => do
      let response ← kdf pending.pending.request
      let ready := RawCtxSourceSend.resumeSend pending.pending response
      let written ← simulateQ (native aead hash reserve receipt ∘ₛ RecordEffectsSendBridge.modelAdapter)
        (RawCtxSourceSeal.sealInput (RecordEffectsSendBridge.inputOf ready))
      pure (RecordEffectsSendBridge.finishResult ready written)

/-- The complete actual extracted outer driver expands its four native children and equals the exact byte-level send controller in the same state monad. -/
theorem source_program [FrameDispatchFallback.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : Conversion view)
    (failure : primitives.Error) (kdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m Sealed) (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext)
    (ordinary : context.prefix = .None) (framed : context.encoding = .Frame) (receipt : RawCtxReceive.DecodedFrame→m Unit) :
    abstractOutput <$> simulateQ (callbacks view failure kdf aead hash reserve erased receipt)
      (AdapterRecordStatefulSend.program kernel context) = byteController kdf aead hash reserve kernel context receipt := by
  rw [RegistrationNativePlatformOrdinarySourceDriver.program, render_bind]
  unfold RegistrationNativePlatformOrdinarySend.execute byteController
  simp only [RustT.run_bind, RustT.run_liftRust, pure_bind]
  cases started : record_effects.begin_record_send kernel context with
  | fail error | div => simp only [map_pure]; rfl
  | ok start =>
      cases start with
      | Rejected entry => simp only [RustT.run_pure, map_pure]; rfl
      | KdfRequested pending =>
          have sameContext := record_context kernel context pending started
          have prefixNone : pending.pending.context.prefix = .None := by rw [sameContext]; exact ordinary
          have frameEncoding : pending.pending.context.encoding = .Frame := by rw [sameContext]; exact framed
          change abstractCore <$> (RegistrationNativePlatformOrdinarySend.fromKdf
            (fun request => .ok <$> kdf request) (sealing view failure reserve aead)
            (hashing hash erased) (fun request => writing reserve request receipt) pending).run = _
          rw [fromKdf view converted failure kdf aead hash reserve erased pending prefixNone frameEncoding receipt]
          apply bind_congr
          intro response
          rw [RecordEffectsSendBridge.source_seal_model erased.bytes _
            (by simpa only [resume_context] using prefixNone) (by simpa only [resume_context] using frameEncoding)]
          simp only [simulateQ_bind, simulateQ_pure, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.receipt_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.receipt_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromWrite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromWrite
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromCommitment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromCommitment
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromAead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromAead
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromKdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.fromKdf
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceipt.source_program
