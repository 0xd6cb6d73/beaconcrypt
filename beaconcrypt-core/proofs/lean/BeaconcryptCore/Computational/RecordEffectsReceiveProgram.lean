-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxInterpretedOpening
import BeaconcryptCore.Computational.RawCtxNativeFramePrelude
import BeaconcryptCore.Computational.RecordEffectsReceiveRank

/-! This private request interpreter dispatches the actual extracted record controller. Primitive replies and transcript erasure remain explicit; phase selection and retained state are extracted operations. -/

open CoreModels Aeneas OracleComp
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Computational.RawCtxInterpretedOpening (bindResult)
open BeaconcryptCore.Computational.RecordEffectsReceiveRank (rank resume_decreasing)

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RecordEffectsReceiveProgram

abbrev Result := ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted

def aeadQuery (request : record.AeadRequest) : RawCtxSourceOpen.BaseInput :=
  ⟨absBytes request.key, absBytes request.nonce, absBytes request.associated_data,
    RawCtxNativeFramePrelude.sliceBytes request.ciphertext⟩

def decryptedOf (opened : record.OpenedRecord Pqxdh.Bytes) : RawCtxWholeOwner.Decrypted :=
  ⟨opened.plaintext, opened.key_id, opened.seq⟩

def compareDigest (digest : Option Pqxdh.Bytes)
    (pending : record_effects.RecordReceiveCommitment) : RustM Bool :=
  match digest with
  | none => ok false
  | some digest => do
      let supplied ← pending.supplied_commitment
      ok (decide (digest = absBytes supplied))

/-- The actual optional AEAD request and reply are finished on the retained capability. -/
def executeAead (pending : record_effects.RecordReceiveAead) :
    OracleComp RawCtxSourceOpen.OpenSpec (RustM Result) :=
  bindResult (pending.request) fun request => do
    let plaintext ← match request with
      | .None => pure core.option.Option.None
      | .Some request => RawCtxSourceOpen.OpenSpec.query (.inr (aeadQuery request))
    bindResult (pending.finish plaintext) fun result =>
      pure (ok (result.1, RawCtxOwnerResult.mapReply decryptedOf result.2))

/-- Hashing and equality retain the actual digest; the only mutation is explicit transcript erasure. -/
def executeCommitment (erased : Std.Array Std.U8 357#usize)
    (pending : record_effects.RecordReceiveCommitment) :
    OracleComp RawCtxSourceOpen.OpenSpec (RustM Result) :=
  bindResult (record_effects.RecordReceiveCommitment.transcript pending) fun transcript =>
  bindResult (commitment.CommitmentTranscript.as_bytes transcript) fun bytes => do
    let digest ← RawCtxSourceOpen.OpenSpec.query (.inl (absBytes bytes))
    bindResult (pending.transcript_mut) fun borrowed =>
    bindResult (commitment.CommitmentTranscript.as_mut_bytes borrowed.1) fun bytesBorrowed =>
    let retained := borrowed.2 (bytesBorrowed.2 erased)
    bindResult (compareDigest digest retained) fun matched =>
    bindResult (retained.resume matched) fun next =>
      match next with
      | .Rejected kernel => pure (ok (kernel, .None))
      | .AeadRequested opening => executeAead opening
      | .KdfRequested _ | .CommitmentRequested _ => pure .div


def execute (erased : Std.Array Std.U8 357#usize)
    (effect : record_effects.RecordReceiveEffect) :
    OracleComp RawCtxSourceOpen.NativeSpec (RustM Result) :=
  match effect with
  | .Rejected kernel => pure (ok (kernel, .None))
  | .KdfRequested pending =>
      bindResult (pending.request) fun request => do
        let response ← RawCtxSourceOpen.NativeSpec.query (.inl request)
        match _resumed : pending.resume response with
        | .ok next => execute erased next
        | .fail error => pure (.fail error)
        | .div => pure .div
  | .CommitmentRequested pending =>
      simulateQ RawCtxSourceOpen.openLift (executeCommitment erased pending)
  | .AeadRequested pending => simulateQ RawCtxSourceOpen.openLift (executeAead pending)
termination_by rank effect
decreasing_by exact resume_decreasing pending response next _resumed

/-- Start with the actual extracted admission and composed record entrypoint. -/
def receive (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (sequence : Std.U64) (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (sender : Std.U64) : OracleComp RawCtxSourceOpen.NativeSpec (RustM Result) :=
  bindResult (record_effects.begin_record_receive kernel sequence payload ad sender) (execute erased)

/-- Decoding and the sender-route check retain their explicit adapter boundary. -/
def decoded (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (expected : Std.U64) (frame : RawCtxReceive.DecodedFrame) (payload : Slice Std.U8)
    (ad : Std.Array Std.U8 281#usize) : OracleComp RawCtxSourceOpen.NativeSpec (RustM Result) :=
  if frame.sender = expected then receive erased kernel frame.sequence payload ad frame.sender
  else pure (ok (kernel, .None))

theorem execute_kdf (erased : Std.Array Std.U8 357#usize)
    (pending : record_effects.RecordReceiveKdf) :
    execute erased (.KdfRequested pending) = (do
      let response ← RawCtxSourceOpen.NativeSpec.query (.inl pending.pending.request)
      bindResult (pending.resume response) (execute erased)) := by
  rw [execute]
  simp only [record_effects.RecordReceiveKdf.request, ReceiveKdf.impl.request, bindResult]
  refine bind_congr fun response => ?_
  split <;> rename_i h <;> rw [h]

end BeaconcryptCore.Computational.RecordEffectsReceiveProgram

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveProgram.execute_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveProgram.execute_kdf
