-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord
import BeaconcryptCore.Computational.RegistrationSeedPublic
/-! The actual stateful source first-record controller does not inspect its retained advanced whole kernel. Replacing only that kernel preserves every reached allocator, AEAD, mutable hash and raw writer effect, including enclosing Rust failures and divergence. This is the seed-erasure step required by the restricted source client; it does not move a private seed into the environment. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic
open RegistrationNativePlatformServerRecord (continueWith continueResult)
open BeaconcryptCore.Refinement.RecordEffects
open RegistrationKernelErasure (mapResult)
open RegistrationPublicationKernelErasure (mapOk)
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def written (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordWrite) : registration.ServerRecordWrite :=
  { pending with pending := { pending.pending with «seal» := { pending.pending.seal with advanced := kernel } } }

def commitment (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordCommitment) : registration.ServerRecordCommitment :=
  { pending with pending := { pending.pending with «seal» := { pending.pending.seal with advanced := kernel } } }

private theorem write_resume (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordWrite)
    (reply : core.option.Option (Slice U8)) :
    (written kernel pending).resume reply = mapResult kernel (pending.resume reply) := by
  rw [← RegistrationRawSealBridge.finish_reply (written kernel pending) reply,
    ← RegistrationRawSealBridge.finish_reply pending reply]
  exact RegistrationKernelErasure.finish_map kernel pending.state pending.pending.seal _

/-- Actual raw writing retains all same-state writer failures and changes only the kernel in a successful continuation. -/
theorem fromWrite (kernel : ConcreteRatchetKernel)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordWrite) :
    RegistrationNativePlatformServerRecord.fromWrite write (written kernel pending) =
      mapResult kernel <$> RegistrationNativePlatformServerRecord.fromWrite write pending := by
  have request : (written kernel pending).request = pending.request := rfl
  unfold RegistrationNativePlatformServerRecord.fromWrite
  rw [request]
  cases requested : pending.request with
  | fail error => simp only [continueWith, map_pure]; rfl
  | div => simp only [continueWith, map_pure]; rfl
  | ok value =>
      simp only [continueWith, map_bind, map_pure]
      apply bind_congr
      intro reply
      apply congrArg pure
      cases reply with
      | fail error => rfl
      | div => rfl
      | ok optional => exact write_resume kernel pending optional

private theorem commitment_resume (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordCommitment)
    (reply : core.option.Option (Std.Array U8 64#usize)) :
    (commitment kernel pending).resume reply =
      mapOk (written kernel) <$> pending.resume reply := by
  cases reply <;> simp only [commitment, written, registration.ServerRecordCommitment.resume,
    seal_commitment_missing_exact, seal_commitment_supplied_exact, pqxdh.server_abort_candidate,
    bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok, mapOk]

private theorem continue_map {Input : Type} (kernel : ConcreteRatchetKernel) (transform : Input → Input)
    (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → m (RustM RegistrationServerRecordExecutor.Result))
    (preserved : ∀ value, next (transform value) = mapResult kernel <$> next value) :
    continueResult (mapOk transform <$> action) next = mapResult kernel <$> continueResult action next := by
  cases action with
  | fail error => simp only [continueResult, map_pure]; rfl
  | div => simp only [continueResult, map_pure]; rfl
  | ok value => cases value with
    | Err previous => simp only [RawCtxMaterialInterpretation.rust_map_ok, mapOk, continueResult, map_pure]; rfl
    | Ok value =>
      simp only [RawCtxMaterialInterpretation.rust_map_ok, mapOk, continueResult]
      exact preserved value

/-- The actual mutable commitment callback and its returned replacement retain their full effects under hidden-kernel replacement. -/
theorem fromCommitment (kernel : ConcreteRatchetKernel)
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) :
    RegistrationNativePlatformCommitment.fromCommitment hash write (commitment kernel pending) =
      mapResult kernel <$> RegistrationNativePlatformCommitment.fromCommitment hash write pending := by
  rw [RegistrationNativePlatformCommitment.normalize, RegistrationNativePlatformCommitment.normalize]
  simp only [commitment, map_bind]
  apply bind_congr
  intro reply
  cases reply with
  | fail error => simp only [bind_tc_fail, continueResult, map_pure]; rfl
  | div => simp only [bind_tc_div, continueResult, map_pure]; rfl
  | ok pair =>
    simp only [bind_tc_ok]
    change continueResult ((commitment kernel pending).resume pair.1)
      (RegistrationNativePlatformServerRecord.fromWrite write) =
      mapResult kernel <$> continueResult (pending.resume pair.1) (RegistrationNativePlatformServerRecord.fromWrite write)
    rw [commitment_resume]
    exact continue_map kernel (written kernel) (pending.resume pair.1)
      (RegistrationNativePlatformServerRecord.fromWrite write) (fromWrite kernel write)


private theorem aead_resume (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordAead)
    (reply : core.option.Option (Slice U8 × Std.Array U8 16#usize)) :
    (RegistrationKernelErasure.selected kernel pending).resume reply =
      mapOk (commitment kernel) <$> pending.resume reply := by
  cases reply with
  | none =>
    simp only [RegistrationKernelErasure.selected, registration.ServerRecordAead.resume,
      seal_aead_missing_exact, pqxdh.server_abort_candidate, bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok, mapOk]
  | some pair =>
    rcases pair with ⟨ciphertext, tag⟩
    obtain ⟨transcript, transcriptRun, _bytes⟩ := PqxdhRefinement.build_commitment_transcript_abs
      pending.pending.seal.material.key.bytes pending.pending.seal.material.nonce.bytes
      pending.pending.seal.context.associated_data tag pending.pending.seal.sequence pending.pending.seal.context.sender_kid
    simp only [RegistrationKernelErasure.selected, registration.ServerRecordAead.resume,
      record_effects.SealAead.resume, SendSeal.impl.material, SendSeal.impl.context,
      SendSeal.impl.sequence, ratchet.RatchetMaterial.impl.key, ratchet.RatchetMaterial.impl.nonce,
      ratchet.RatchetKey.as_bytes, ratchet.RatchetNonce.as_bytes, bind_tc_ok]
    dsimp! only
    simp only [transcriptRun, bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok, mapOk, commitment]


/-- Actual prefixed source sealing, mutable hashing and writing have identical effects for every retained private kernel, including all enclosing failures. -/
theorem fromAead (kernel : ConcreteRatchetKernel)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) :
    RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write (RegistrationKernelErasure.selected kernel pending) =
      mapResult kernel <$> RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write pending := by
  have request : (RegistrationKernelErasure.selected kernel pending).request = pending.request := rfl
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  rw [request]
  cases requested : pending.request with
  | fail error => simp only [continueWith, map_pure]; rfl
  | div => simp only [continueWith, map_pure]; rfl
  | ok value =>
    simp only [continueWith, map_bind]
    apply bind_congr
    intro reply
    cases reply with
    | fail error => simp only [bind_tc_fail, continueResult, map_pure]; rfl
    | div => simp only [bind_tc_div, continueResult, map_pure]; rfl
    | ok optional =>
      simp only [bind_tc_ok]
      rw [aead_resume]
      exact continue_map kernel (commitment kernel) (pending.resume optional)
        (RegistrationNativePlatformCommitment.fromCommitment hash write) (fromCommitment kernel hash write)


end BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic.fromWrite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic.fromWrite

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic.fromCommitment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic.fromCommitment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic.fromAead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic.fromAead
