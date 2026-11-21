-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication
import BeaconcryptCore.Computational.RegistrationNativeResponseCandidate
import BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate

/-! Successful source seal, mutable commitment and stateful write continuations replay their same optional replies in the unchanged Core record controller. This derives public response candidate lineage only; it does not equate complete executions or discard any actual failure/poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordSupport
variable {I S A B : Type} {base : OracleSpec I}
abbrev M (S : Type) (base : OracleSpec I) := StateT S (OracleComp base)
def Possible (work : M S base A) (value : A) : Prop := ∃ before after, (value,after) ∈ support (work.run before)
private theorem pure_possible (value actual : A) (possible : Possible (pure value : M S base A) actual) : value=actual := by
  obtain ⟨before,after,supported⟩ := possible
  simp only [StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq] at supported
  exact supported.1.symm
private theorem bind_possible (work : M S base A) (next : A → M S base B) (value : B)
    (possible : Possible (work >>= next) value) : ∃ middle, Possible work middle ∧ Possible (next middle) value := by
  obtain ⟨before,after,supported⟩ := possible
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  exact ⟨middle.1,⟨before,middle.2,called⟩,⟨middle.2,after,continued⟩⟩
private theorem with_replay {Input : Type} (action : RustM Input)
    (next : Input → M S base (RustM RegistrationServerRecordExecutor.Result))
    (old : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result))
    (completed : registration.ServerResponseHash)
    (replay : ∀ value, Possible (next value) (.ok (.Ok completed)) → .ok (.Ok completed) ∈ support (old value))
    (possible : Possible (RegistrationNativePlatformServerRecord.continueWith action next) (.ok (.Ok completed))) :
    .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.continueWith action old) := by
  cases action with
  | fail error | div => cases pure_possible _ _ possible
  | ok value => exact replay value possible
private theorem result_replay {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → M S base (RustM RegistrationServerRecordExecutor.Result))
    (old : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result))
    (completed : registration.ServerResponseHash)
    (replay : ∀ value, Possible (next value) (.ok (.Ok completed)) → .ok (.Ok completed) ∈ support (old value))
    (possible : Possible (RegistrationNativePlatformServerRecord.continueResult action next) (.ok (.Ok completed))) :
    .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.continueResult action old) := by
  cases action with
  | fail error | div => cases pure_possible _ _ possible
  | ok reply => cases reply with
    | Err previous => cases pure_possible _ _ possible
    | Ok value => exact replay value possible
variable (sealing : record_effects.AeadSealRequest → M S base (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → M S base RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → M S base (RustM (core.option.Option (Slice U8))))
private theorem fromWrite (pending : registration.ServerRecordWrite) (completed : registration.ServerResponseHash)
    (possible : Possible (RegistrationNativePlatformServerRecord.fromWrite write pending) (.ok (.Ok completed))) :
    .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.fromWrite pending) := by
  unfold RegistrationNativePlatformServerRecord.fromWrite RegistrationServerRecordExecutor.fromWrite at *
  apply with_replay _ _ _ completed _ possible
  intro request called
  obtain ⟨result,_written,returned⟩ := bind_possible _ _ _ called
  have equal := pure_possible _ _ returned
  cases result with
  | fail error | div => cases equal
  | ok reply =>
    rw [mem_support_bind_iff]
    exact ⟨reply,mem_support_query _ _,by rw [mem_support_pure_iff]; exact equal.symm⟩
private theorem fromCommitment (pending : registration.ServerRecordCommitment) (completed : registration.ServerResponseHash)
    (possible : Possible (RegistrationNativePlatformCommitment.fromCommitment hash write pending) (.ok (.Ok completed))) :
    .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.fromCommitment pending) := by
  rw [RegistrationNativePlatformCommitment.normalize] at possible
  obtain ⟨result,_hashed,continued⟩ := bind_possible _ _ _ possible
  have transcript : pending.transcript = .ok pending.pending.transcript := rfl
  simp only [RegistrationServerRecordExecutor.fromCommitment,transcript,RegistrationServerRecordExecutor.continueWith,mem_support_bind_iff]
  cases result with
  | fail error | div => cases pure_possible _ _ continued
  | ok reply =>
    refine ⟨reply.1,mem_support_query _ _,?_⟩
    exact result_replay _ _ _ completed (fun next supported => fromWrite write next completed supported) continued
/-- A successful actual seal/hash/stateful-writer result has its same Core continuation support; enclosing failures and returned source state are not identified with a pure execution. -/
theorem fromAead (pending : registration.ServerRecordAead) (completed : registration.ServerResponseHash)
    (possible : Possible (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write pending) (.ok (.Ok completed))) :
    .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.fromAead pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash RegistrationServerRecordExecutor.fromAead at *
  apply with_replay _ _ _ completed _ possible
  intro request called
  obtain ⟨result,_sealed,continued⟩ := bind_possible _ _ _ called
  cases result with
  | fail error | div => cases pure_possible _ _ continued
  | ok reply =>
    rw [mem_support_bind_iff]
    refine ⟨reply,mem_support_query _ _,?_⟩
    exact result_replay _ _ _ completed (fun next supported => fromCommitment hash write next completed supported) continued
/-- The actual source supplied-KDF record retains its admitted public candidate on every successful result, independently of all allocator, raw-writer, hash and primitive failures elsewhere. -/
theorem factored (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (completed : registration.ServerResponseHash)
    (possible : Possible (RegistrationNativePlatformBoundPublication.record sealing hash write initial output) (.ok (.Ok completed))) :
    .ok (.Ok completed) ∈ support (RegistrationBoundKeySchedule.factored initial output) := by
  unfold RegistrationNativePlatformBoundPublication.record RegistrationBoundKeySchedule.factored at *
  exact result_replay _ _ _ completed (fun next supported => fromAead sealing hash write next completed supported) possible
end BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordSupport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordSupport.fromAead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordSupport.fromAead

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordSupport.factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordSupport.factored
