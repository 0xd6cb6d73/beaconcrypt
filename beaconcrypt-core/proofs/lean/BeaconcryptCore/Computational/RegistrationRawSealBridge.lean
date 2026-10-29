-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor
import BeaconcryptCore.Computational.RecordEffectsSendBridge
import BeaconcryptCore.Computational.CborRawRegistrationBuild

/-!
Registration seals a streamed LE64 prefix and application under its populated binding, then writes raw protected bytes. This differs from the ordinary unprefixed framed send. The primitive adapter below exposes the same actual AEAD, hash and raw-writer operands to the existing byte sealing program. Typed optional replies retain malformed writer output and representability failure; final response admission remains the actual native continuation.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RecordEffects
open BeaconcryptCore.Refinement.RegistrationRecords

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationRawSealBridge

abbrev PrimitiveSpec :=
  (RawCtxSourceSeal.AeadInput →ₒ core.option.Option (Slice Std.U8 × Std.Array Std.U8 16#usize)) +
    ((Pqxdh.Bytes →ₒ core.option.Option (Std.Array Std.U8 64#usize)) +
      (Pqxdh.Bytes →ₒ core.option.Option (Slice Std.U8)))

abbrev Spec := RegistrationRecordPrimitives.Spec + PrimitiveSpec

def toOption {Value : Type} : core.option.Option Value → Option Value
  | .None => none
  | .Some value => some value

def nativeAdapter : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp Spec)
  | .seal request => Spec.query (.inr (.inl (RegistrationRecordPrimitives.sealInput request)))
  | .hash transcript => Spec.query (.inr (.inr (.inl (absBytes transcript.bytes))))
  | .write (.Raw parts) => Spec.query (.inr (.inr (.inr (RegistrationRecordPrimitives.partsBytes parts))))
  | query => Spec.query (.inl query)

def modelAdapter : QueryImpl RawCtxSourceSeal.SealSpec (OracleComp Spec)
  | .inl input => do
      let reply ← Spec.query (.inr (.inl input))
      pure ((toOption reply).map fun pair => (TranscriptAuthParts.absSlice pair.1, absBytes pair.2))
  | .inr (.inl bytes) => do
      let reply ← Spec.query (.inr (.inr (.inl bytes)))
      pure ((toOption reply).map absBytes)
  | .inr (.inr frame) => do
      let reply ← Spec.query (.inr (.inr (.inr frame.payload)))
      pure ((toOption reply).map TranscriptAuthParts.absSlice)

def plaintext (context : record_effects.SealFrameContext) : Pqxdh.Bytes :=
  match context.prefix with
  | .None => TranscriptAuthParts.absSlice context.plaintext
  | .Some prefixBytes => absBytes prefixBytes ++ TranscriptAuthParts.absSlice context.plaintext

def inputOf (selected : SendSeal record_effects.SealFrameContext) : RawCtxSourceSend.SealInput :=
  ⟨selected.material, selected.sequence,
    ⟨plaintext selected.context, selected.context.target_kid, selected.context.sender_kid,
      absBytes selected.context.associated_data⟩⟩

theorem seal_request (pending : record_effects.SealAead) :
    (RegistrationRecordPrimitives.sealInput <$> pending.request) =
      .ok (RawCtxSourceSeal.aeadInput (inputOf pending.seal)) := by
  simp only [record_effects.SealAead.request, SendSeal.impl.material, SendSeal.impl.context,
    ratchet.RatchetMaterial.impl.key, ratchet.RatchetMaterial.impl.nonce,
    ratchet.RatchetKey.as_bytes, ratchet.RatchetNonce.as_bytes,
    record_effects.SealFrameContext.plaintext_request, bind_tc_ok]
  cases prefixEq : pending.seal.context.prefix <;>
    simp only [prefixEq, bind_tc_ok, RawCtxSourceSeal.aeadInput, inputOf, plaintext,
      BeaconcryptCore.Refinement.RepresentationBridge.absMaterial] <;> rfl

theorem raw_request (pending : record_effects.SealWrite) (raw : pending.seal.context.encoding = .Raw) :
    ∃ parts, pending.request = .ok (.Raw parts) ∧ RegistrationRecordPrimitives.partsBytes parts =
      TranscriptAuthParts.absSlice pending.ciphertext ++ absBytes pending.tag ++ absBytes pending.commitment := by
  simp only [record_effects.SealWrite.request, core.array.Array.as_slice, SendSeal.impl.context,
    raw, bind_tc_ok, rust_primitives.slice.array_as_slice]
  refine ⟨_, rfl, ?_⟩
  change TranscriptAuthParts.absSlice pending.ciphertext ++
      (absBytes pending.tag ++ (absBytes pending.commitment ++ [])) = _
  simp only [List.append_nil, List.append_assoc]

/-- The returned writer slice is already representable; projecting it to model bytes and back introduces no new allocation premise. -/
theorem opened_roundtrip (bytes : Slice Std.U8) :
    RegistrationAuthenticationShared.openedBytes (some (TranscriptAuthParts.absSlice bytes)) = .Some bytes := by
  have inverse (byte : Std.U8) : BeaconcryptCore.Refinement.ProtocolComposition.concreteByte (absByte byte) = byte := by
    apply absByte_injective
    simp
  simp [RegistrationAuthenticationShared.openedBytes, TranscriptAuthParts.absSlice,
    List.map_map, Function.comp_def, inverse, bytes.property]
  congr 1

/-- The actual final response admission depends on the selected seal and state, rather than the already-written part descriptors. -/
theorem finish_irrelevant (left right : registration.ServerRecordWrite)
    (state : left.state = right.state) (sealSame : left.pending.seal = right.pending.seal)
    (written : core.option.Option (Slice Std.U8)) : left.resume written = right.resume written := by
  simp only [registration.ServerRecordWrite.resume, seal_write_finish_exact, state, sealSame]

def finish (state : registration.ServerRecordState) (selected : SendSeal record_effects.SealFrameContext)
    (written : Option Pqxdh.Bytes) : RustM RegistrationServerRecordExecutor.Result :=
  registration.ServerRecordWrite.resume
    ⟨state, ⟨selected, ⟨[], by simp⟩, Std.Array.repeat 16#usize 0#u8, Std.Array.repeat 64#usize 0#u8⟩⟩
    (RegistrationAuthenticationShared.openedBytes written)

theorem finish_none (state : registration.ServerRecordState) (selected : SendSeal record_effects.SealFrameContext) :
    finish state selected none = .ok (.Err state.candidate.previous_state) := by
  simp only [finish, RegistrationAuthenticationShared.openedBytes, registration.ServerRecordWrite.resume,
    pqxdh.server_abort_candidate, seal_write_finish_exact, bind_tc_ok]
  rfl

theorem finish_some (pending : registration.ServerRecordWrite) (written : Slice Std.U8) :
    finish pending.state pending.pending.seal (some (TranscriptAuthParts.absSlice written)) = pending.resume (.Some written) := by
  rw [finish, opened_roundtrip]
  exact finish_irrelevant _ pending rfl rfl (.Some written)

theorem finish_reply (pending : registration.ServerRecordWrite) (written : core.option.Option (Slice Std.U8)) :
    finish pending.state pending.pending.seal ((toOption written).map TranscriptAuthParts.absSlice) =
      pending.resume written := by
  cases written with
  | none =>
      rw [show (toOption (.None : core.option.Option (Slice Std.U8))).map TranscriptAuthParts.absSlice = none from rfl,
        finish_none]
      simp only [registration.ServerRecordWrite.resume, seal_write_finish_exact,
        pqxdh.server_abort_candidate, bind_tc_ok]
      rfl
  | some bytes => exact finish_some pending bytes

def writeProgram (state : registration.ServerRecordState) (selected : SendSeal record_effects.SealFrameContext)
    (bytes : Pqxdh.Bytes) : OracleComp Spec (RustM RegistrationServerRecordExecutor.Result) := do
  let written ← Spec.query (.inr (.inr (.inr bytes)))
  pure (finish state selected ((toOption written).map TranscriptAuthParts.absSlice))

def commitmentProgram (state : registration.ServerRecordState) (selected : SendSeal record_effects.SealFrameContext)
    (body tag transcript : Pqxdh.Bytes) : OracleComp Spec (RustM RegistrationServerRecordExecutor.Result) := do
  let digest ← Spec.query (.inr (.inr (.inl transcript)))
  match digest with
  | .None => pure (finish state selected none)
  | .Some digest => writeProgram state selected (body ++ tag ++ absBytes digest)

theorem write_exact (pending : registration.ServerRecordWrite) (raw : pending.pending.seal.context.encoding = .Raw) :
    simulateQ nativeAdapter (RegistrationServerRecordExecutor.fromWrite pending) =
      writeProgram pending.state pending.pending.seal (TranscriptAuthParts.absSlice pending.pending.ciphertext ++
        absBytes pending.pending.tag ++ absBytes pending.pending.commitment) := by
  obtain ⟨parts, requested, bytes⟩ := raw_request pending.pending raw
  calc
    _ = writeProgram pending.state pending.pending.seal (RegistrationRecordPrimitives.partsBytes parts) := by
      simp only [RegistrationServerRecordExecutor.fromWrite, registration.ServerRecordWrite.request,
        requested, RegistrationServerRecordExecutor.continueWith, simulateQ_bind, simulateQ_spec_query,
        nativeAdapter, simulateQ_pure, writeProgram]
      apply bind_congr
      intro written
      rw [finish_reply]
    _ = _ := congrArg (writeProgram pending.state pending.pending.seal) bytes

theorem commitment_exact (pending : registration.ServerRecordCommitment)
    (raw : pending.pending.seal.context.encoding = .Raw) :
    simulateQ nativeAdapter (RegistrationServerRecordExecutor.fromCommitment pending) =
      commitmentProgram pending.state pending.pending.seal (TranscriptAuthParts.absSlice pending.pending.ciphertext)
        (absBytes pending.pending.tag) (absBytes pending.pending.transcript.bytes) := by
  simp only [RegistrationServerRecordExecutor.fromCommitment, registration.ServerRecordCommitment.transcript,
    record_effects.SealCommitment.impl.transcript, RegistrationServerRecordExecutor.continueWith,
    simulateQ_bind, simulateQ_spec_query, nativeAdapter, commitmentProgram]
  apply bind_congr
  intro digest
  cases digest with
  | none =>
      simp only [registration.ServerRecordCommitment.resume, seal_commitment_missing_exact,
        pqxdh.server_abort_candidate, bind_tc_ok, RegistrationServerRecordExecutor.continueResult,
        simulateQ_pure, finish_none]
  | some digest =>
      obtain ⟨next, resumed, stateSame, sealSame, ciphertextSame, tagSame, digestSame⟩ :=
        server_commitment_reply_refines pending digest
      simp only [resumed, RegistrationServerRecordExecutor.continueResult]
      rw [write_exact next (by simpa only [sealSame] using raw)]
      simp only [stateSame, sealSame, ciphertextSame, tagSame, digestSame]

def model (pending : registration.ServerRecordAead) : OracleComp Spec (RustM RegistrationServerRecordExecutor.Result) := do
  let written ← simulateQ modelAdapter (RawCtxSourceSeal.sealInput (inputOf pending.pending.seal))
  pure (finish pending.state pending.pending.seal written)

def aeadProgram (state : registration.ServerRecordState) (selected : SendSeal record_effects.SealFrameContext)
    (input : RawCtxSourceSend.SealInput) : OracleComp Spec (RustM RegistrationServerRecordExecutor.Result) := do
  let detached ← Spec.query (.inr (.inl (RawCtxSourceSeal.aeadInput input)))
  match detached with
  | .None => pure (finish state selected none)
  | .Some (body, tag) =>
      commitmentProgram state selected (TranscriptAuthParts.absSlice body)
        (absBytes tag) (RawCtxSourceSeal.hashInput input (absBytes tag))

theorem model_program (pending : registration.ServerRecordAead) :
    model pending = aeadProgram pending.state pending.pending.seal (inputOf pending.pending.seal) := by
  simp only [model, aeadProgram, RawCtxSourceSeal.sealInput, simulateQ_bind, simulateQ_spec_query,
    modelAdapter, bind_assoc, pure_bind]
  apply bind_congr
  intro detached
  cases detached with
  | none => simp only [toOption, Option.map_none, simulateQ_pure, pure_bind]
  | some pair =>
      obtain ⟨body, tag⟩ := pair
      simp only [toOption, Option.map_some, inputOf, absBytes_length,
        Std.UScalar.ofNatCore_val_eq, ite_true, simulateQ_bind, simulateQ_spec_query,
        modelAdapter, bind_assoc, pure_bind, commitmentProgram]
      apply bind_congr
      intro digest
      cases digest with
      | none => simp only [Option.map_none, simulateQ_pure, pure_bind]
      | some digest =>
          simp only [toOption, Option.map_some, simulateQ_spec_query, modelAdapter,
            bind_assoc, pure_bind, writeProgram, RawCtxSourceSeal.frame]

def aeadCall (input : RawCtxSourceSeal.AeadInput)
    (next : core.option.Option (Slice Std.U8 × Std.Array Std.U8 16#usize) →
      OracleComp Spec (RustM RegistrationServerRecordExecutor.Result)) :
    OracleComp Spec (RustM RegistrationServerRecordExecutor.Result) := do
  let detached ← Spec.query (.inr (.inl input))
  next detached

theorem native_program (pending : registration.ServerRecordAead)
    (raw : pending.pending.seal.context.encoding = .Raw) :
    simulateQ nativeAdapter (RegistrationServerRecordExecutor.fromAead pending) =
      aeadProgram pending.state pending.pending.seal (inputOf pending.pending.seal) := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RecordEffects.SealAead_request_total pending.pending
  have requestedBytes := seal_request pending.pending
  rw [requested] at requestedBytes
  change RustM.ok (RegistrationRecordPrimitives.sealInput request) =
    RustM.ok (RawCtxSourceSeal.aeadInput (inputOf pending.pending.seal)) at requestedBytes
  have bytesSame := RustM.ok.inj requestedBytes
  simp only [RegistrationServerRecordExecutor.fromAead, registration.ServerRecordAead.request,
    requested, RegistrationServerRecordExecutor.continueWith, simulateQ_bind, simulateQ_spec_query,
    nativeAdapter]
  change aeadCall (RegistrationRecordPrimitives.sealInput request)
    (fun detached => simulateQ nativeAdapter
      (RegistrationServerRecordExecutor.continueResult (pending.resume detached)
        RegistrationServerRecordExecutor.fromCommitment)) = _
  rw [bytesSame]
  simp only [aeadCall, aeadProgram]
  apply bind_congr
  intro detached
  cases detached with
  | none =>
      simp only [registration.ServerRecordAead.resume, seal_aead_missing_exact,
        pqxdh.server_abort_candidate, bind_tc_ok, RegistrationServerRecordExecutor.continueResult,
        simulateQ_pure, finish_none]
  | some pair =>
      obtain ⟨body, tag⟩ := pair
      obtain ⟨next, resumed, stateSame, sealSame, bodySame, tagSame, transcript⟩ :=
        server_aead_reply_refines pending body tag
      simp only [resumed, RegistrationServerRecordExecutor.continueResult]
      rw [commitment_exact next (by simpa only [sealSame] using raw)]
      have hashSame : absBytes next.pending.transcript.bytes =
          RawCtxSourceSeal.hashInput (inputOf pending.pending.seal) (absBytes tag) := by
        simpa only [RawCtxSourceSeal.hashInput, inputOf,
          BeaconcryptCore.Refinement.RepresentationBridge.absMaterial] using transcript
      simp only [stateSame, sealSame, bodySame, tagSame, hashSame]

/-- Prefix-aware raw registration sealing is the existing source sealing program followed by the actual native response admission. -/
theorem model_exact (pending : registration.ServerRecordAead)
    (raw : pending.pending.seal.context.encoding = .Raw) :
    simulateQ nativeAdapter (RegistrationServerRecordExecutor.fromAead pending) = model pending :=
  (native_program pending raw).trans (model_program pending).symm

theorem stateful_execution {State Domain : Type} {target : OracleSpec Domain}
    (implementation : QueryImpl Spec (StateT State (OracleComp target)))
    (pending : registration.ServerRecordAead) (raw : pending.pending.seal.context.encoding = .Raw) (state : State) :
    (simulateQ implementation (simulateQ nativeAdapter (RegistrationServerRecordExecutor.fromAead pending))).run state =
      (simulateQ implementation (model pending)).run state :=
  congrArg (fun program => (simulateQ implementation program).run state) (model_exact pending raw)

noncomputable def primitiveImplementation {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl PrimitiveSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl input => simulateQ (MldsaSharedSource.implementation source writer) (do
      let sealed ← MldsaSharedNative.recordLift (.inr (.inl input))
      pure (RegistrationRecordPrimitives.sealedBytes sealed))
  | .inr (.inl bytes) => simulateQ (MldsaSharedSource.implementation source writer) (do
      let digest ← MldsaSharedNative.authLift ((), bytes)
      pure (.Some (RegistrationAuthenticationShared.digestArray digest)))
  | .inr (.inr bytes) => pure (RegistrationAuthenticationShared.openedBytes (some bytes))

noncomputable def implementation {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => RegistrationRecordPrimitives.implementation source writer request
  | .inr request => primitiveImplementation source writer request

private theorem map_state_apply {State Input Output : Type} (mapResult : Input → Output)
    (work : StateT State ProbComp Input) (state : State) :
    (mapResult <$> work) state = Prod.map mapResult id <$> work state := by
  change (work state >>= fun result => pure (mapResult result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

theorem query_projection {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (request : RegistrationRecordPrimitives.Request) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (implementation source writer) (nativeAdapter request)).run state =
      (RegistrationRecordPrimitives.implementation source writer request).run state := by
  cases request with
  | rootKdf request => rfl
  | initialKdf request => rfl
  | ratchetKdf request => rfl
  | openAead request => rfl
  | «seal» request => rfl
  | hash request =>
      rw [RegistrationRecordPrimitives.hash_exact]
      simp only [nativeAdapter, simulateQ_spec_query, implementation, primitiveImplementation,
        MldsaSharedNative.authLift, simulateQ_map, simulateQ_spec_query,
        StateT.run, map_state_apply, MldsaSharedSource.implementation,
        MldsaSharedNative.primitives, MldsaSharedNative.authentication, bind_pure_comp,
        Functor.map_map]
      rfl
  | write request => cases request <;> rfl

theorem program_projection {Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RegistrationRecordPrimitives.Spec Result) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (implementation source writer) (simulateQ nativeAdapter work)).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, query_projection, ih]

theorem shared_execution {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : registration.ServerRecordAead) (raw : pending.pending.seal.context.encoding = .Raw)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationRecordPrimitives.implementation source writer)
      (RegistrationServerRecordExecutor.fromAead pending)).run state =
      (simulateQ (implementation source writer) (model pending)).run state := by
  rw [← program_projection source writer, model_exact pending raw]

end BeaconcryptCore.Computational.RegistrationRawSealBridge

/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.seal_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.seal_request
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.raw_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.raw_request
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.opened_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.opened_roundtrip
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_irrelevant
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_none
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_some
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.finish_reply
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.write_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.write_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.commitment_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.commitment_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.model_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.model_program
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.native_program
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.model_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.model_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.stateful_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.stateful_execution
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.query_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.query_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.program_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationRawSealBridge.shared_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawSealBridge.shared_execution
