-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord
import BeaconcryptCore.Refinement.AdapterServerCommitmentLens

/-! The actual mutable commitment getter and returned transcript are threaded around the hash callback before resuming the first-record controller. Any returned replacement, including erasure after an optional hash failure, is consumed through the actual source lens. The next Core continuation is proved independent of that replacement; hash effects and enclosing failures remain visible. Physical erasure is a separate primitive functional obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCommitment
open RegistrationServerRecordExecutor (Result)
open RegistrationNativePlatformServerRecord (continueWith continueResult fromWrite)
open BeaconcryptCore.Refinement
variable {m : Type → Type} [Monad m]

abbrev HashReply := RustM (core.option.Option (Std.Array U8 64#usize) × commitment.CommitmentTranscript)

def fromCommitment (hash : commitment.CommitmentTranscript → m HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) : m (RustM Result) :=
  continueWith pending.transcript_mut fun selected => do
    let result ← hash selected.1
    continueResult (do
      let reply ← result
      (selected.2 reply.2).resume reply.1) (fromWrite write)

theorem normalize (hash : commitment.CommitmentTranscript → m HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) :
    fromCommitment hash write pending = (do
      let result ← hash pending.pending.transcript
      continueResult (do let reply ← result; pending.resume reply.1) (fromWrite write)) := by
  unfold fromCommitment
  rw [AdapterServerCommitmentLens.getter]
  apply bind_congr
  intro result
  cases result with
  | fail error => rfl
  | div => rfl
  | ok pair =>
      change continueResult ((AdapterServerCommitmentLens.replace pending pair.2).resume pair.1) (fromWrite write) = _
      rw [AdapterServerCommitmentLens.resume_replace]
      rfl

variable [LawfulMonad m]

theorem native (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (erased : commitment.CommitmentTranscript)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) :
    fromCommitment (fun transcript => (fun reply => RustM.ok (reply, erased)) <$> record (.hash transcript)) write pending =
      RegistrationNativePlatformServerRecord.fromCommitment record write pending := by
  rw [normalize]
  unfold RegistrationNativePlatformServerRecord.fromCommitment
  rw [bind_map_left]
  rfl

section Map
variable {left right : Type → Type} [Monad left] [Monad right]
variable {F : ∀ {Value : Type}, left Value → right Value}
variable (hom : Cslib.IsMonadHom left right F)
include hom

private theorem continueResult_map {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → left (RustM Result)) :
    F (continueResult action next) = continueResult action (fun value => F (next value)) := by
  cases action with
  | ok result => cases result <;> first | rfl | exact hom.map_pure _
  | fail error => exact hom.map_pure _
  | div => exact hom.map_pure _

theorem fromCommitment_map (hash : commitment.CommitmentTranscript → left HashReply)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) :
    F (fromCommitment hash write pending) =
      fromCommitment (fun transcript => F (hash transcript)) (fun request => F (write request)) pending := by
  rw [normalize, normalize, hom.map_bind]
  apply bind_congr
  intro result
  rw [continueResult_map hom]
  apply congrArg (continueResult (do let reply ← result; pending.resume reply.1))
  funext next
  exact RegistrationNativePlatformServerRecord.fromWrite_map hom write next

end Map

omit [LawfulMonad m] in
theorem fromCommitment_run {σ : Type} (hash : commitment.CommitmentTranscript → StateT σ m HashReply)
    (write : record_effects.RecordWriteRequest → StateT σ m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) (before : σ) :
    (fromCommitment hash write pending).run before = (do
      let result ← (hash pending.pending.transcript).run before
      (continueResult (do let reply ← result.1; pending.resume reply.1) (fromWrite write)).run result.2) := by
  rw [normalize]
  exact StateT.run_bind _ _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformCommitment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.normalize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.fromCommitment_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.fromCommitment_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.fromCommitment_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCommitment.fromCommitment_run
