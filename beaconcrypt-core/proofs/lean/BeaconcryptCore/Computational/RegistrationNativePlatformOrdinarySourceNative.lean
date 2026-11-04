-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceDriver
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open PqxdhRefinement
variable {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}
variable [primitives : AdapterSealPrimitive.Operations]

abbrev Sealed := Option (alloc.vec.Vec U8 × Std.Array U8 16#usize)
structure Conversion (view : RegistrationNativePlatformSourceSeal.KeyView) : Prop where
  key : ∀ bytes, ∃ value, primitives.fromKey bytes = .ok value ∧ view.key value = bytes
  nonce : ∀ bytes, ∃ value, primitives.fromNonce bytes = .ok value ∧ view.nonce value = bytes

def sealHandler (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (reserve : Nat → m (core.result.Result Unit E)) (aead : RawCtxSourceSeal.AeadInput → m Sealed) :
    QueryImpl (AdapterSealNative.Spec E) m
  | .reserve before capacity => (fun reply => .ok (reply, before)) <$> reserve capacity.val
  | .aead plaintext associated nonce key =>
      (fun reply => .ok (match reply with | none => .Err failure | some pair => .Ok pair)) <$>
        aead (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)

def sealing (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (reserve : Nat → m (core.result.Result Unit E)) (aead : RawCtxSourceSeal.AeadInput → m Sealed)
    (request : record_effects.AeadSealRequest) : m (RustM AdapterSealNative.Output) :=
  simulateQ (sealHandler view failure reserve aead) (AdapterSealNative.source E request)

/-- On ordinary Single plaintext the actual source child performs exactly its fixed-array conversions and one trusted AEAD request, with no public reservation. -/
theorem sealing_single (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : Conversion view)
    (failure : primitives.Error) (reserve : Nat → m (core.result.Result Unit E))
    (aead : RawCtxSourceSeal.AeadInput → m Sealed)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize)
    (associated : Std.Array U8 281#usize) (plaintext : Slice U8) :
    sealing view failure reserve aead ⟨key, nonce, associated, .Single plaintext⟩ =
      .ok <$> aead ⟨absBytes key, absBytes nonce, absBytes associated, TranscriptAuthParts.absSlice plaintext⟩ := by
  obtain ⟨nativeKey, keyRun, keyView⟩ := converted.key key
  obtain ⟨nativeNonce, nonceRun, nonceView⟩ := converted.nonce nonce
  unfold sealing
  rw [AdapterSealNative.source_native]
  simp only [AdapterSealNative.execute, AdapterSealRequestMonad.Lifted.key,
    AdapterSealRequestMonad.Lifted.nonce, AdapterRecordRequestMonad.liftRust,
    core.convert.Into.Blanket.into,
    beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832,
    beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812,
    keyRun, nonceRun, AdapterSealNative.continueWith,
    AdapterSealNative.aead, simulateQ_map, simulateQ_spec_query, sealHandler,
    Functor.map_map]
  simp only [RegistrationNativePlatformSourceSeal.input, keyView, nonceView]
  apply congrArg₂ (fun f work => f <$> work)
  · funext reply
    cases reply <;> rfl
  · rfl

def afterAttempt {A : Type} (receipt : m Unit) (work : m A) : m A := do
  let value ← work
  receipt
  pure value

omit primitives in
private theorem afterAttempt_map {A B : Type} (receipt : m Unit) (f : A → B) (work : m A) :
    f <$> afterAttempt receipt work = afterAttempt receipt (f <$> work) := by
  simp only [afterAttempt, map_bind, map_pure, bind_map_left]


def writing [FrameDispatchFallback.Operations] (reserve : Nat → m (core.result.Result Unit E))
    (request : record_effects.RecordWriteRequest) (receipt : m Unit := pure ()) : m (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  afterAttempt receipt (simulateQ (AdapterRecordRawBytes.helper (fun _ size => .ok <$> reserve size.val)
    (AdapterRecordFrameBytes.serializer (m := m)))
    (AdapterRecordHelperRouting.route (E := E) (m := AdapterRecordHelperRequestMonad.Program E) request).run)

omit primitives in
/-- With the default pure analysis receipt, writing is literally the actual interpreted source helper, including Rust failure and divergence. -/
theorem writing_source [FrameDispatchFallback.Operations]
    (reserve : Nat → m (core.result.Result Unit E)) (request : record_effects.RecordWriteRequest) :
    writing reserve request = simulateQ (AdapterRecordRawBytes.helper (fun _ size => .ok <$> reserve size.val)
      (AdapterRecordFrameBytes.serializer (m := m)))
      (AdapterRecordHelperRouting.route (E := E) (m := AdapterRecordHelperRequestMonad.Program E) request).run := by
  simp only [writing, afterAttempt, pure_bind, bind_pure]

omit primitives in
/-- A separate trusted analysis counter records exactly one writer attempt after every returned Rust outcome; erasing that counter is the literal source helper execution. -/
theorem attempted_source [FrameDispatchFallback.Operations]
    (reserve : Nat → m (core.result.Result Unit E)) (request : record_effects.RecordWriteRequest) (previous : Nat) :
    ((afterAttempt (modify fun count : Nat => count + 1)
      (simulateQ (fun query => StateT.lift ((AdapterRecordRawBytes.helper
        (fun _ size => .ok <$> reserve size.val) (AdapterRecordFrameBytes.serializer (m := m))) query))
        (AdapterRecordHelperRouting.route (E := E) (m := AdapterRecordHelperRequestMonad.Program E) request).run) :
      StateT Nat m (RustM (Option (alloc.vec.Vec U8)))).run previous) =
      (fun reply => (reply, previous + 1)) <$> writing reserve request := by
  have same : simulateQ (fun query => StateT.lift ((AdapterRecordRawBytes.helper
        (fun _ size => .ok <$> reserve size.val) (AdapterRecordFrameBytes.serializer (m := m))) query))
        (AdapterRecordHelperRouting.route (E := E) (m := AdapterRecordHelperRequestMonad.Program E) request).run =
      (StateT.lift (simulateQ (AdapterRecordRawBytes.helper (fun _ size => .ok <$> reserve size.val)
        (AdapterRecordFrameBytes.serializer (m := m)))
        (AdapterRecordHelperRouting.route (E := E) (m := AdapterRecordHelperRequestMonad.Program E) request).run) :
      StateT Nat m (RustM (Option (alloc.vec.Vec U8)))) := by
    exact simulateQ_liftTarget (m := m) (n := StateT Nat m)
      (AdapterRecordRawBytes.helper (fun _ size => .ok <$> reserve size.val) (AdapterRecordFrameBytes.serializer (m := m)))
      (AdapterRecordHelperRouting.route (E := E) (m := AdapterRecordHelperRequestMonad.Program E) request).run
  rw [same, writing_source]
  simp only [afterAttempt, StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_modify,
    map_pure, bind_pure_comp, Functor.map_map]


def abstractCore (result : RustM RegistrationNativePlatformOrdinarySend.Result) :
    RustM RecordEffectsSendBridge.Result := do
  let value ← result
  .ok (value.1, _root_.Option.map (fun record => ⟨TranscriptAuthParts.absSlice record.ciphertext, record.key_id, record.seq⟩) value.2)

omit [LawfulMonad m] primitives in
private theorem writing_frame [FrameDispatchFallback.Operations]
    (reserve : Nat → m (core.result.Result Unit E)) (sequence sender : U64) (first second third : Slice U8)
    (receipt : m Unit := pure ()) :
    writing reserve (.Frame (Std.Array.make 3#usize [first, second, third]) sequence sender) receipt =
      afterAttempt receipt (AdapterRecordFrameBytes.frame (fun _ size => .ok <$> reserve size.val)
        (AdapterRecordFrameBytes.serializer (m := m)) sequence sender first second third) := rfl

private def finishBytes (pending : ratchet.concrete.SendSeal record_effects.SealFrameContext)
    (written : RustM (Option Pqxdh.Bytes)) : RustM RecordEffectsSendBridge.Result := do
  let bytes ← written
  RecordEffectsSendBridge.finishResult pending bytes

omit primitives in
private theorem writer_finish (pending : record_effects.SealWrite)
    (written : RustM (Option (alloc.vec.Vec U8))) :
    abstractCore (do let value ← written; pending.finish value) =
      finishBytes pending.seal (RegistrationNativeExtractedAllocation.abstractResult written) := by
  cases written with
  | fail error | div => rfl
  | ok reply =>
      cases reply <;> simp only [bind_tc_ok, RecordEffects.seal_write_finish_exact,
        abstractCore, finishBytes, RecordEffectsSendBridge.finishResult_exact,
        RegistrationNativeExtractedAllocation.abstractResult,
        RegistrationNativeExtractedAllocation.output]
      all_goals rfl

omit primitives in
/-- The actual source writer and actual core completion retain the advanced kernel and exact metadata on both public reservation outcomes. -/
theorem fromWrite [FrameDispatchFallback.Operations]
    (reserve : Nat → m (core.result.Result Unit E)) (pending : record_effects.SealWrite)
    (framed : pending.seal.context.encoding = .Frame) (receipt : m Unit := pure ()) :
    abstractCore <$> (RegistrationNativePlatformOrdinarySend.fromWrite (fun request => writing reserve request receipt) pending).run = (do
      let written ← RegistrationNativePlatformOrdinaryWriter.write reserve
        (RawCtxSourceSeal.frame (RecordEffectsSendBridge.inputOf pending.seal)
          (TranscriptAuthParts.absSlice pending.ciphertext) (absBytes pending.tag) (absBytes pending.commitment))
      receipt
      pure (RecordEffectsSendBridge.finishResult pending.seal written)) := by
  unfold RegistrationNativePlatformOrdinarySend.fromWrite
  simp only [record_effects.SealWrite.request, framed, ratchet.concrete.SendSeal.impl.context,
    ratchet.concrete.SendSeal.impl.sequence, core.array.Array.as_slice, rust_primitives.slice.array_as_slice,
    RustT.run_bind, RustT.run_liftRust, bind_tc_ok, pure_bind, map_bind]
  rw [writing_frame (receipt := receipt)]
  have tail : (fun written : RustM (Option (alloc.vec.Vec U8)) =>
      (abstractCore <$> (match written with
        | .ok value => pure (pending.finish value)
        | .fail error => pure (.fail error)
        | .div => pure .div : m (RustM RegistrationNativePlatformOrdinarySend.Result)))) =
      (fun written => pure (abstractCore (do let value ← written; pending.finish value))) := by
    funext written
    cases written <;> simp only [map_pure] <;> rfl
  let work := afterAttempt receipt (AdapterRecordFrameBytes.frame (fun _ size => .ok <$> reserve size.val)
    (AdapterRecordFrameBytes.serializer (m := m)) pending.seal.sequence pending.seal.context.sender_kid
    pending.ciphertext (Std.Array.to_slice pending.tag) (Std.Array.to_slice pending.commitment))
  trans (fun written => abstractCore (do let value ← written; pending.finish value)) <$> work
  · convert (congrArg (fun next => work >>= next) tail).trans (bind_pure_comp _ _) using 1
    congr 1
    funext written
    cases written <;> rfl
  dsimp only [work]
  have factor : (fun written => abstractCore (do let value ← written; pending.finish value)) =
      finishBytes pending.seal ∘ RegistrationNativeExtractedAllocation.abstractResult :=
    funext (writer_finish pending)
  trans finishBytes pending.seal <$> (RegistrationNativeExtractedAllocation.abstractResult <$>
    afterAttempt receipt (AdapterRecordFrameBytes.frame (fun _ size => .ok <$> reserve size.val)
      (AdapterRecordFrameBytes.serializer (m := m)) pending.seal.sequence pending.seal.context.sender_kid
      pending.ciphertext (Std.Array.to_slice pending.tag) (Std.Array.to_slice pending.commitment)))
  · rw [Functor.map_map]
    exact congrArg (fun f => f <$> work) factor
  rw [afterAttempt_map]
  have total := congrArg (fun work => finishBytes pending.seal <$> afterAttempt receipt work)
    (RegistrationNativePlatformOrdinaryWriterTotal.source reserve pending.seal.sequence pending.seal.context.sender_kid
      pending.ciphertext (Std.Array.to_slice pending.tag) (Std.Array.to_slice pending.commitment))
  apply total.trans
  simp only [afterAttempt, map_bind, map_pure, bind_map_left, finishBytes, bind_tc_ok, RecordEffectsSendBridge.finishResult_exact]
  rfl

def hashing (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (erased : commitment.CommitmentTranscript) (transcript : commitment.CommitmentTranscript) :
    m (RustM RegistrationNativePlatformOrdinarySend.HashReply) :=
  (fun digest => .ok (digest, erased)) <$> hash (absBytes transcript.bytes)

def native (aead : RawCtxSourceSeal.AeadInput → m Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (receipt : m Unit := pure ()) : QueryImpl RecordEffectsSendBridge.PrimitiveSpec m
  | .inl input => aead input
  | .inr (.inl bytes) => hash bytes
  | .inr (.inr frame) => afterAttempt receipt (RegistrationNativePlatformOrdinaryWriter.write reserve frame)

omit primitives in
/-- The actual mutable transcript return is consumed before resuming commitment and writing, preserving every shared primitive poststate. -/
theorem fromCommitment [FrameDispatchFallback.Operations]
    (aead : RawCtxSourceSeal.AeadInput → m Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (pending : record_effects.SealCommitment) (framed : pending.seal.context.encoding = .Frame) (receipt : m Unit := pure ()) :
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
    (framed : pending.seal.context.encoding = .Frame) (receipt : m Unit := pure ()) :
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
    (framed : pending.pending.context.encoding = .Frame) (receipt : m Unit := pure ()) :
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
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript) (receipt : m Unit := pure ()) :
    QueryImpl AdapterRecordSendRequestMonad.Spec m
  | .kdf request => .ok <$> kdf request
  | .sealing request => sealing view failure reserve aead request
  | .hash transcript => hashing hash erased transcript
  | .writer request => writing reserve request receipt

noncomputable def byteController
    (kdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m Sealed) (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E))
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) (receipt : m Unit := pure ()) : m (RustM RecordEffectsSendBridge.Result) :=
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
    (ordinary : context.prefix = .None) (framed : context.encoding = .Frame) (receipt : m Unit := pure ()) :
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

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.sealing_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.sealing_single

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.writing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.writing_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.attempted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.attempted_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromWrite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromWrite

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromCommitment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromCommitment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromAead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromAead

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromKdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.fromKdf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative.source_program
