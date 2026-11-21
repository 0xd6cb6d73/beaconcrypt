-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformCommitment

/-! The source detached-seal dispatcher can allocate its prefixed plaintext before reaching AEAD. This controller therefore retains the enclosing RustM seal result as well as the enclosing writer result. Neither failure nor divergence is converted into an optional primitive reply or allowed to reach a later source continuation. The ordinary optional-seal interface is a checked compatibility specialization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord
open RegistrationRecordPrimitives (Spec)
open RegistrationServerRecordExecutor (Result)
open RegistrationNativePlatformServerRecord (continueWith continueResult fromCommitment)
variable {m : Type → Type} [Monad m]

def fromAead (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let result ← sealing request
    continueResult (do let reply ← result; pending.resume reply) (fromCommitment record write)

def fromRatchet (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← record (.ratchetKdf request)
    continueResult (pending.resume reply) (fromAead record sealing write)

def fromInitial (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← record (.initialKdf request)
    continueResult (pending.resume reply) (fromRatchet record sealing write)

def fromAeadWithHash
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let result ← sealing request
    continueResult (do let reply ← result; pending.resume reply)
      (RegistrationNativePlatformCommitment.fromCommitment hash write)

def fromRatchetWithHash (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← record (.ratchetKdf request)
    continueResult (pending.resume reply) (fromAeadWithHash sealing hash write)

def fromInitialWithHash (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← record (.initialKdf request)
    continueResult (pending.resume reply) (fromRatchetWithHash record sealing hash write)

variable [LawfulMonad m]

theorem fromAeadWithHash_native (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (erased : commitment.CommitmentTranscript)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) :
    fromAeadWithHash sealing (fun transcript => (fun reply => RustM.ok (reply, erased)) <$> record (.hash transcript))
      write pending = fromAead record sealing write pending := by
  unfold fromAeadWithHash fromAead
  apply congrArg (continueWith pending.request)
  funext request
  apply bind_congr
  intro result
  apply congrArg (continueResult (do let reply ← result; pending.resume reply))
  funext next
  exact RegistrationNativePlatformCommitment.native record erased write next

theorem fromRatchetWithHash_native (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (erased : commitment.CommitmentTranscript)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) :
    fromRatchetWithHash record sealing (fun transcript => (fun reply => RustM.ok (reply, erased)) <$> record (.hash transcript))
      write pending = fromRatchet record sealing write pending := by
  unfold fromRatchetWithHash fromRatchet
  apply congrArg (continueWith pending.request)
  funext request
  apply bind_congr
  intro reply
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromAeadWithHash_native record sealing erased write next

theorem fromInitialWithHash_native (record : QueryImpl Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (erased : commitment.CommitmentTranscript)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) :
    fromInitialWithHash record sealing (fun transcript => (fun reply => RustM.ok (reply, erased)) <$> record (.hash transcript))
      write pending = fromInitial record sealing write pending := by
  unfold fromInitialWithHash fromInitial
  apply congrArg (continueWith pending.request)
  funext request
  apply bind_congr
  intro reply
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromRatchetWithHash_native record sealing erased write next

theorem fromAead_pure (record : QueryImpl Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) :
    fromAead record (fun request => RustM.ok <$> record (.seal request)) write pending =
      RegistrationNativePlatformServerRecord.fromAead record write pending := by
  unfold fromAead RegistrationNativePlatformServerRecord.fromAead
  apply congrArg (continueWith pending.request)
  funext request
  rw [bind_map_left]
  rfl

theorem fromRatchet_pure (record : QueryImpl Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) :
    fromRatchet record (fun request => RustM.ok <$> record (.seal request)) write pending =
      RegistrationNativePlatformServerRecord.fromRatchet record write pending := by
  unfold fromRatchet RegistrationNativePlatformServerRecord.fromRatchet
  apply congrArg (continueWith pending.request)
  funext request
  apply bind_congr
  intro reply
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromAead_pure record write next

theorem fromInitial_pure (record : QueryImpl Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) :
    fromInitial record (fun request => RustM.ok <$> record (.seal request)) write pending =
      RegistrationNativePlatformServerRecord.fromInitial record write pending := by
  unfold fromInitial RegistrationNativePlatformServerRecord.fromInitial
  apply congrArg (continueWith pending.request)
  funext request
  apply bind_congr
  intro reply
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromRatchet_pure record write next

section Map
variable {left right : Type → Type} [Monad left] [Monad right]
variable {F : ∀ {Value : Type}, left Value → right Value}
variable (hom : Cslib.IsMonadHom left right F)
include hom

private theorem continueWith_map {Input : Type} (action : RustM Input)
    (next : Input → left (RustM Result)) :
    F (continueWith action next) = continueWith action (fun value => F (next value)) := by
  cases action <;> first | rfl | exact hom.map_pure _

private theorem continueResult_map {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → left (RustM Result)) :
    F (continueResult action next) = continueResult action (fun value => F (next value)) := by
  cases action with
  | ok result => cases result <;> first | rfl | exact hom.map_pure _
  | fail error => exact hom.map_pure _
  | div => exact hom.map_pure _

theorem fromAead_map (record : QueryImpl Spec left)
    (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) :
    F (fromAead record sealing write pending) =
      fromAead (fun query => F (record query)) (fun request => F (sealing request))
        (fun request => F (write request)) pending := by
  unfold fromAead
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro result
  rw [continueResult_map hom]
  apply congrArg (continueResult (do let reply ← result; pending.resume reply))
  funext next
  exact RegistrationNativePlatformServerRecord.fromCommitment_map hom record write next

theorem fromRatchet_map (record : QueryImpl Spec left)
    (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) :
    F (fromRatchet record sealing write pending) =
      fromRatchet (fun query => F (record query)) (fun request => F (sealing request))
        (fun request => F (write request)) pending := by
  unfold fromRatchet
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromAead_map hom record sealing write next

theorem fromInitial_map (record : QueryImpl Spec left)
    (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) :
    F (fromInitial record sealing write pending) =
      fromInitial (fun query => F (record query)) (fun request => F (sealing request))
        (fun request => F (write request)) pending := by
  unfold fromInitial
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromRatchet_map hom record sealing write next

theorem fromAeadWithHash_map
    (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → left RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) :
    F (fromAeadWithHash sealing hash write pending) =
      fromAeadWithHash (fun request => F (sealing request)) (fun transcript => F (hash transcript))
        (fun request => F (write request)) pending := by
  unfold fromAeadWithHash
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro result
  rw [continueResult_map hom]
  apply congrArg (continueResult (do let reply ← result; pending.resume reply))
  funext next
  exact RegistrationNativePlatformCommitment.fromCommitment_map hom hash write next

theorem fromRatchetWithHash_map (record : QueryImpl Spec left)
    (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → left RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) :
    F (fromRatchetWithHash record sealing hash write pending) =
      fromRatchetWithHash (fun query => F (record query)) (fun request => F (sealing request))
        (fun transcript => F (hash transcript)) (fun request => F (write request)) pending := by
  unfold fromRatchetWithHash
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromAeadWithHash_map hom sealing hash write next

theorem fromInitialWithHash_map (record : QueryImpl Spec left)
    (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → left RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) :
    F (fromInitialWithHash record sealing hash write pending) =
      fromInitialWithHash (fun query => F (record query)) (fun request => F (sealing request))
        (fun transcript => F (hash transcript)) (fun request => F (write request)) pending := by
  unfold fromInitialWithHash
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromRatchetWithHash_map hom record sealing hash write next

end Map

omit [LawfulMonad m] in
theorem fromAead_run {σ : Type} (record : QueryImpl Spec (StateT σ m))
    (sealing : record_effects.AeadSealRequest → StateT σ m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (write : record_effects.RecordWriteRequest → StateT σ m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) (before : σ) :
    (fromAead record sealing write pending).run before =
      match pending.request with
      | .ok request => do
          let result ← (sealing request).run before
          (continueResult (do let reply ← result.1; pending.resume reply) (fromCommitment record write)).run result.2
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before) := by
  unfold fromAead continueWith
  cases pending.request with
  | ok request => exact StateT.run_bind _ _ _
  | fail error => rfl
  | div => rfl

omit [LawfulMonad m] in
theorem fromAeadWithHash_run {σ : Type}
    (sealing : record_effects.AeadSealRequest → StateT σ m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT σ m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT σ m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) (before : σ) :
    (fromAeadWithHash sealing hash write pending).run before =
      match pending.request with
      | .ok request => do
          let result ← (sealing request).run before
          (continueResult (do let reply ← result.1; pending.resume reply)
            (RegistrationNativePlatformCommitment.fromCommitment hash write)).run result.2
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before) := by
  unfold fromAeadWithHash continueWith
  cases pending.request with
  | ok request => exact StateT.run_bind _ _ _
  | fail error => rfl
  | div => rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAead_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAead_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchet_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchet_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitial_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitial_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAead_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAead_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchet_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchet_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitial_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitial_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAead_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAead_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAeadWithHash_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAeadWithHash_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchetWithHash_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchetWithHash_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitialWithHash_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitialWithHash_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAeadWithHash_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAeadWithHash_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchetWithHash_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromRatchetWithHash_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitialWithHash_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromInitialWithHash_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAeadWithHash_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord.fromAeadWithHash_run
