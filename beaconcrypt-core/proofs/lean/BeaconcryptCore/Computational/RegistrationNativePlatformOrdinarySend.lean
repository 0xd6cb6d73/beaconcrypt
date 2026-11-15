-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
import BeaconcryptCore.Refinement.AdapterSealNative
import BeaconcryptCore.Refinement.AdapterRecordNativeWriter
import BeaconcryptCore.Refinement.RecordEffects
import BeaconcryptCore.PanicFreedom.RecordEffectsSend

/-! The ordinary record controller executes its actual extracted core phases above the common state monad. Detached sealing and frame writing retain enclosing Rust failures and divergence. An ordinary Single seal requests no prefixed-plaintext reservation; only its later actual Frame3 writer allocates. This additive controller does not replace the previously checked registration profile or identify it with an older static writer experiment. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterRecordRequestMonad (liftRust)
variable {m : Type → Type} [Monad m]

abbrev Result := ratchet.concrete.ConcreteRatchetKernel × core.option.Option (record_effects.SealedRecord (alloc.vec.Vec U8))
abbrev HashReply := core.option.Option (Array U8 64#usize) × commitment.CommitmentTranscript

def fromWrite (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : record_effects.SealWrite) : RustT m Result := do
  let request ← liftRust pending.request
  let written ← (⟨write request⟩ : RustT m _)
  liftRust (pending.finish written)

def fromCommitment
    (hash : commitment.CommitmentTranscript → m (RustM HashReply))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : record_effects.SealCommitment) : RustT m Result := do
  let (transcript, back) ← liftRust pending.transcript_mut
  let (reply, changed) ← (⟨hash transcript⟩ : RustT m _)
  let next ← liftRust ((back changed).resume reply)
  match next with
  | .Rejected kernel => pure (kernel, .None)
  | .WriteRequested ready => fromWrite write ready

def fromAead
    (sealing : record_effects.AeadSealRequest → m (RustM AdapterSealNative.Output))
    (hash : commitment.CommitmentTranscript → m (RustM HashReply))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : record_effects.SealAead) : RustT m Result := do
  let request ← liftRust pending.request
  let sealed ← (⟨sealing request⟩ : RustT m _)
  let next ← liftRust (pending.resume sealed)
  match next with
  | .Rejected kernel => pure (kernel, .None)
  | .CommitmentRequested ready => fromCommitment hash write ready

def fromKdf
    (kdf : ratchet.SymmetricRatchetKdfRequest → m (RustM ratchet.RatchetKdfResponse))
    (sealing : record_effects.AeadSealRequest → m (RustM AdapterSealNative.Output))
    (hash : commitment.CommitmentTranscript → m (RustM HashReply))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : record_effects.RecordSendKdf) : RustT m Result := do
  let request ← liftRust pending.request
  let response ← (⟨kdf request⟩ : RustT m _)
  let ready ← liftRust (pending.resume response)
  fromAead sealing hash write ready

def execute
    (kdf : ratchet.SymmetricRatchetKdfRequest → m (RustM ratchet.RatchetKdfResponse))
    (sealing : record_effects.AeadSealRequest → m (RustM AdapterSealNative.Output))
    (hash : commitment.CommitmentTranscript → m (RustM HashReply))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) : RustT m Result := do
  let next ← liftRust (record_effects.begin_record_send kernel context)
  match next with
  | .Rejected original => pure (original, .None)
  | .KdfRequested pending => fromKdf kdf sealing hash write pending

section Single
variable [primitive : AdapterSealPrimitive.Operations]
def NoReserve : AdapterSealNative.Request → Prop
  | .reserve _ _ => False
  | .aead _ _ _ _ => True

/-- The actual detached-seal source specialization on Single plaintext never requests the prefixed join allocator, including failed key or nonce conversion. -/
theorem single_no_reserve (E : Type) (key : Array U8 32#usize) (nonce : Array U8 12#usize)
    (associated : Array U8 151#usize) (plaintext : Slice U8) :
    (AdapterSealNative.execute E ⟨key, nonce, associated, .Single plaintext⟩).AllQueriesSatisfy NoReserve := by
  unfold AdapterSealNative.execute
  cases AdapterSealRequestMonad.Lifted.key (m := RustM) key with
  | fail error => simp [AdapterSealNative.continueWith]
  | div => simp [AdapterSealNative.continueWith]
  | ok nativeKey =>
      simp only [AdapterSealNative.continueWith]
      cases AdapterSealRequestMonad.Lifted.nonce (m := RustM) nonce with
      | fail error => simp
      | div => simp
      | ok nativeNonce =>
          change OracleComp.AllQueriesSatisfy (((AdapterSealNative.Spec E).query (.aead plaintext (.Some (Array.to_slice associated)) nativeNonce nativeKey) : OracleComp (AdapterSealNative.Spec E) AdapterSealNative.NativeReply) >>= fun result => pure (AdapterSealNative.finish result)) NoReserve
          exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => allQueriesSatisfy_pure _ _⟩
end Single

variable [LawfulMonad m]

/-- A normal writer rejection keeps the same already advanced send kernel and emits no ciphertext. -/
theorem fromWrite_none (pending : record_effects.SealWrite) :
    (fromWrite (m := m) (fun _ => pure (.ok .None)) pending).run =
      pure (.ok (pending.seal.advanced, .None)) := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RecordEffectsSend.SealWrite_request_total pending
  unfold fromWrite
  simp only [requested, RustT.run_bind, RustT.run_liftRust, pure_bind]
  rw [RecordEffects.seal_write_finish_exact]

/-- Missing detached AEAD stops before hashing and writing while retaining the consumed send step. -/
theorem fromAead_none
    (hash : commitment.CommitmentTranscript → m (RustM HashReply))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (pending : record_effects.SealAead) :
    (fromAead (fun _ => pure (.ok .None)) hash write pending).run =
      pure (.ok (pending.seal.advanced, .None)) := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RecordEffects.SealAead_request_total pending
  unfold fromAead
  simp only [requested, RustT.run_bind, RustT.run_liftRust, pure_bind]
  rw [RecordEffects.seal_aead_missing_exact]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend.single_no_reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend.single_no_reserve

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend.fromWrite_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend.fromWrite_none

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend.fromAead_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend.fromAead_none
