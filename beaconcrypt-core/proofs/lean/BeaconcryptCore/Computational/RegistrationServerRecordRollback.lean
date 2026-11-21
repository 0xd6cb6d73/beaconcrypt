-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord
import BeaconcryptCore.Refinement.RegistrationRecords
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The actual first-record source controller keeps its original completion control on every optional rejection and keeps that same candidate on success. Enclosing primitive failure/divergence remains a separate outcome with its reached external poststate. No primitive success premise is used. -/
namespace BeaconcryptCore.Computational.RegistrationServerRecordRollback
open RegistrationNativePlatformServerRecord (continueWith continueResult fromWrite)
open RegistrationNativePlatformSourceRecord (fromAeadWithHash fromRatchetWithHash fromInitialWithHash)
open BeaconcryptCore.Refinement.RegistrationRecords

inductive Request where
  | record (request : RegistrationRecordPrimitives.Request)
  | sealing (request : record_effects.AeadSealRequest)
  | commitment (transcript : commitment.CommitmentTranscript)
  | writing (request : record_effects.RecordWriteRequest)

abbrev Spec : OracleSpec Request
  | .record request => RegistrationRecordPrimitives.Spec.Range request
  | .sealing _ => RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))
  | .commitment _ => RegistrationNativePlatformCommitment.HashReply
  | .writing _ => RustM (core.option.Option (Slice U8))

def Post {Value : Type} (previous : Value → pqxdh.ServerState) (control : pqxdh.ServerState) :
    RustM (core.result.Result Value pqxdh.ServerState) → Prop
  | .fail _ | .div => True
  | .ok (.Err rejected) => rejected = control
  | .ok (.Ok value) => previous value = control

private theorem write_reply (pending : registration.ServerRecordWrite)
    (reply : RustM (core.option.Option (Slice U8))) :
    Post (fun hashed : registration.ServerResponseHash => hashed.candidate.previous_state)
      pending.state.candidate.previous_state (do let bytes ← reply; pending.resume bytes) := by
  cases reply with
  | fail error | div => trivial
  | ok bytes =>
    obtain ⟨result, resumed, retained⟩ := BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines pending bytes
    simp only [bind_tc_ok, resumed]
    cases result with
    | Err previous => exact retained
    | Ok hashed =>
      change hashed.candidate.previous_state = pending.state.candidate.previous_state
      rw [retained.1]

theorem fromWrite_post (pending : registration.ServerRecordWrite)
    (output : RustM RegistrationServerRecordExecutor.Result)
    (supported : output ∈ support (fromWrite (m := OracleComp Spec) (fun request => Spec.query (.writing request)) pending)) :
    Post (fun hashed : registration.ServerResponseHash => hashed.candidate.previous_state) pending.state.candidate.previous_state output := by
  unfold fromWrite at supported
  cases requested : pending.request with
  | fail error | div =>
    simp only [requested, continueWith, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    trivial
  | ok request =>
    simp only [requested, continueWith, mem_support_bind_iff] at supported
    obtain ⟨reply, _called, returned⟩ := supported
    simp only [support_pure, Set.mem_singleton_iff] at returned
    cases returned
    exact write_reply pending reply

theorem fromCommitment_post (pending : registration.ServerRecordCommitment)
    (output : RustM RegistrationServerRecordExecutor.Result)
    (supported : output ∈ support (RegistrationNativePlatformCommitment.fromCommitment (m := OracleComp Spec)
      (fun transcript => Spec.query (.commitment transcript)) (fun request => Spec.query (.writing request)) pending)) :
    Post (fun hashed : registration.ServerResponseHash => hashed.candidate.previous_state) pending.state.candidate.previous_state output := by
  rw [RegistrationNativePlatformCommitment.normalize] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨reply, _called, continued⟩ := supported
  cases reply with
  | fail error | div =>
    simp only [bind_tc_fail, bind_tc_div, continueResult, support_pure, Set.mem_singleton_iff] at continued
    cases continued
    trivial
  | ok pair =>
    rcases pair with ⟨digest, _updated⟩
    cases digest with
    | none =>
      simp only [bind_tc_ok, registration.ServerRecordCommitment.resume,
        BeaconcryptCore.Refinement.RecordEffects.seal_commitment_missing_exact,
        pqxdh.server_abort_candidate, continueResult, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      rfl
    | some digest =>
      obtain ⟨next, resumed, stateSame, _rest⟩ := server_commitment_reply_refines pending digest
      simp only [bind_tc_ok, resumed, continueResult] at continued
      have retained := fromWrite_post next output continued
      simpa only [stateSame] using retained

theorem fromAead_post (pending : registration.ServerRecordAead)
    (output : RustM RegistrationServerRecordExecutor.Result)
    (supported : output ∈ support (fromAeadWithHash (m := OracleComp Spec)
      (fun request => Spec.query (.sealing request)) (fun transcript => Spec.query (.commitment transcript))
      (fun request => Spec.query (.writing request)) pending)) :
    Post (fun hashed : registration.ServerResponseHash => hashed.candidate.previous_state) pending.state.candidate.previous_state output := by
  unfold fromAeadWithHash at supported
  cases requested : pending.request with
  | fail error | div =>
    simp only [requested, continueWith, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    trivial
  | ok request =>
    simp only [requested, continueWith, mem_support_bind_iff] at supported
    obtain ⟨reply, _called, continued⟩ := supported
    cases reply with
    | fail error | div =>
      simp only [bind_tc_fail, bind_tc_div, continueResult, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      trivial
    | ok optional => cases optional with
      | none =>
        simp only [bind_tc_ok, registration.ServerRecordAead.resume,
          BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact,
          pqxdh.server_abort_candidate, continueResult, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        rfl
      | some pair =>
        rcases pair with ⟨ciphertext, tag⟩
        obtain ⟨next, resumed, stateSame, _rest⟩ := server_aead_reply_refines pending ciphertext tag
        simp only [bind_tc_ok, resumed, continueResult] at continued
        have retained := fromCommitment_post next output continued
        simpa only [stateSame] using retained

theorem fromRatchet_post (pending : registration.ServerInitialSeal)
    (output : RustM RegistrationServerRecordExecutor.Result)
    (supported : output ∈ support (fromRatchetWithHash (m := OracleComp Spec) (fun request => Spec.query (.record request))
      (fun request => Spec.query (.sealing request)) (fun transcript => Spec.query (.commitment transcript))
      (fun request => Spec.query (.writing request)) pending)) :
    Post (fun hashed : registration.ServerResponseHash => hashed.candidate.previous_state) pending.state.candidate.previous_state output := by
  unfold fromRatchetWithHash at supported
  cases requested : pending.request with
  | fail error | div =>
    simp only [requested, continueWith, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    trivial
  | ok request =>
    simp only [requested, continueWith, mem_support_bind_iff] at supported
    obtain ⟨reply, _called, continued⟩ := supported
    cases reply with
    | none =>
      have missing : pending.resume .None = .ok (.Err pending.state.candidate.previous_state) := rfl
      simp only [missing, continueResult, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      rfl
    | some reply =>
      obtain ⟨next, resumed, stateSame, _rest⟩ := server_step_kdf_refines pending reply
      simp only [resumed, continueResult] at continued
      have retained := fromAead_post next output continued
      simpa only [stateSame] using retained

theorem fromInitial_post (pending : registration.ServerInitialKdf)
    (output : RustM RegistrationServerRecordExecutor.Result)
    (supported : output ∈ support (fromInitialWithHash (m := OracleComp Spec) (fun request => Spec.query (.record request))
      (fun request => Spec.query (.sealing request)) (fun transcript => Spec.query (.commitment transcript))
      (fun request => Spec.query (.writing request)) pending)) :
    Post (fun hashed : registration.ServerResponseHash => hashed.candidate.previous_state) pending.candidate.previous_state output := by
  unfold fromInitialWithHash at supported
  cases requested : pending.request with
  | fail error | div =>
    simp only [requested, continueWith, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    trivial
  | ok request =>
    simp only [requested, continueWith, mem_support_bind_iff] at supported
    obtain ⟨reply, _called, continued⟩ := supported
    cases reply with
    | none =>
      have missing : pending.resume .None = .ok (.Err pending.candidate.previous_state) := rfl
      simp only [missing, continueResult, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      rfl
    | some reply =>
      obtain ⟨_kernel, _bound, next, _kernelRun, _boundRun, _bytes, resumed, stateSame, _rest⟩ := server_kdf_prefix_refines pending reply
      simp only [resumed, continueResult] at continued
      have retained := fromRatchet_post next output continued
      simpa only [stateSame] using retained
def implementation {m : Type → Type} (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8)))) : QueryImpl Spec m
  | .record request => record request
  | .sealing request => sealing request
  | .commitment transcript => hash transcript
  | .writing request => write request

theorem interpret {m : Type → Type} [Monad m] [LawfulMonad m]
    (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) :
    simulateQ (implementation record sealing hash write)
      (fromInitialWithHash (m := OracleComp Spec) (fun request => Spec.query (.record request))
        (fun request => Spec.query (.sealing request)) (fun transcript => Spec.query (.commitment transcript))
        (fun request => Spec.query (.writing request)) pending) =
      fromInitialWithHash record sealing hash write pending := by
  have translated := RegistrationNativePlatformSourceRecord.fromInitialWithHash_map
    (simulateQ_isMonadHom (implementation record sealing hash write))
    (fun request => (Spec.query (.record request) : OracleComp Spec _))
    (fun request => (Spec.query (.sealing request) : OracleComp Spec _))
    (fun transcript => (Spec.query (.commitment transcript) : OracleComp Spec _))
    (fun request => (Spec.query (.writing request) : OracleComp Spec _)) pending
  simpa only [simulateQ_spec_query, implementation] using translated

theorem stateful {State : Type}
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT State ProbComp))
    (sealing : record_effects.AeadSealRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT State ProbComp RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) (output : RustM RegistrationServerRecordExecutor.Result)
    (before after : State)
    (supported : (output, after) ∈ support ((fromInitialWithHash record sealing hash write pending).run before)) :
    Post (fun hashed : registration.ServerResponseHash => hashed.candidate.previous_state) pending.candidate.previous_state output := by
  rw [← interpret record sealing hash write pending] at supported
  apply fromInitial_post pending output
  apply OracleComp.support_simulateQ_run'_subset (implementation record sealing hash write) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationServerRecordRollback

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromWrite_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromWrite_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromCommitment_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromCommitment_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromAead_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromAead_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromRatchet_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromRatchet_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromInitial_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordRollback.fromInitial_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordRollback.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordRollback.interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordRollback.stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordRollback.stateful
