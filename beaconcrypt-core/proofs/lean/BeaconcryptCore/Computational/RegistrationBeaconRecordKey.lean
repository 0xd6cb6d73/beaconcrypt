-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRecordNormal
/-! Every rejected first-record outcome carries the original agreement candidate Server identifier. The proof follows actual source normalization, HKDF, commitment and AEAD continuations, including failed admission after plaintext opening. It supplies the endpoint abort-control equality needed by the source Beacon lifecycle relation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconRecordKey
open RegistrationBeaconRecordExecutor
open RegistrationRecordPrimitives (Spec)
open BeaconcryptCore.PanicFreedom
open BeaconcryptCore.PanicFreedom.RegistrationPublication
open BeaconcryptCore.Refinement.RegistrationInputs

def phaseId : registration.BeaconInitialOpen → U64
  | .KdfRequested pending => pending.agreement.candidate.server_binding.identity_key_id
  | .CommitmentRequested pending => pending.agreement.candidate.server_binding.identity_key_id
  | .AeadRequested pending => pending.agreement.candidate.server_binding.identity_key_id

def ResumeKey (keyId : U64) : core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted → Prop
  | .Err aborted => aborted.server_key_id = keyId
  | .Ok phase => phaseId phase = keyId

theorem normalized_key (agreed : agreement.BeaconAgreement) (effect : record_effects.RecordReceiveEffect)
    (result : core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted)
    (returned : registration.normalize_beacon_open agreed effect = .ok result) :
    ResumeKey agreed.candidate.server_binding.identity_key_id result := by
  cases effect <;> simp only [registration.normalize_beacon_open, pqxdh.beacon_abort_candidate, bind_tc_ok] at returned
  all_goals cases RustM.ok.inj returned
  all_goals rfl

theorem kdf_key (pending : registration.BeaconRecordKdf) (reply : core.option.Option ratchet.RatchetKdfResponse)
    (result : core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted)
    (returned : pending.resume reply = .ok result) :
    ResumeKey pending.agreement.candidate.server_binding.identity_key_id result := by
  cases reply with
  | none =>
      simp only [registration.BeaconRecordKdf.resume, pqxdh.beacon_abort_candidate, bind_tc_ok] at returned
      cases RustM.ok.inj returned
      rfl
  | some response =>
      obtain ⟨effect, resumed⟩ := RecordEffects.RecordReceiveKdf_resume_total pending.pending response
      simp only [registration.BeaconRecordKdf.resume, resumed, bind_tc_ok] at returned
      exact normalized_key pending.agreement effect result returned

theorem commitment_key (pending : registration.BeaconRecordCommitment) (matched : Bool)
    (result : core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted)
    (returned : pending.resume matched = .ok result) :
    ResumeKey pending.agreement.candidate.server_binding.identity_key_id result := by
  obtain ⟨effect, resumed⟩ := RecordEffects.RecordReceiveCommitment_resume_total pending.pending matched
  simp only [registration.BeaconRecordCommitment.resume, resumed, bind_tc_ok] at returned
  exact normalized_key pending.agreement effect result returned

theorem initial_key (pending : registration.BeaconInitialKdf) (reply : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse)
    (result : core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted)
    (returned : pending.resume reply = .ok result) :
    ResumeKey pending.agreement.candidate.server_binding.identity_key_id result := by
  cases reply with
  | none =>
      simp only [registration.BeaconInitialKdf.resume, pqxdh.beacon_abort_candidate, bind_tc_ok] at returned
      cases RustM.ok.inj returned
      rfl
  | some response =>
      obtain ⟨kernel, kernelRun⟩ := resume_initial_ratchet_kdf_ok pending.pending response
      obtain ⟨effect, effectRun⟩ := RecordEffects.begin_record_receive_total kernel 1#u64
        pending.agreement.application_ciphertext pending.agreement.binding.associated_data
        pending.agreement.candidate.server_binding.identity_key_id
      simp only [registration.BeaconInitialKdf.resume, kernelRun, session.CompletedRegistrationBinding.impl.associated_data,
        pqxdh.BeaconRegistrationCandidate.server_key_id, effectRun, bind_tc_ok] at returned
      exact normalized_key pending.agreement effect result returned

theorem aead_rejected_key (pending : registration.BeaconRecordAead) (plaintext : core.option.Option (Slice U8))
    (aborted : pqxdh.BeaconAborted) (returned : pending.finish plaintext = .ok (.Err aborted)) :
    aborted.server_key_id = pending.agreement.candidate.server_binding.identity_key_id := by
  obtain ⟨⟨kernel, opened⟩, openedRun⟩ := Record.finish_total pending.pending.pending plaintext
  cases opened <;> simp only [registration.BeaconRecordAead.finish,
    pqxdh.BeaconRegistrationCandidate.server_key_id, pqxdh.BeaconAborted.new,
    record_effects.RecordReceiveAead.finish, openedRun, bind_tc_ok] at returned
  · cases RustM.ok.inj returned
    rfl
  · dsimp! only at returned
    simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok] at returned
    split at returned
    · cases RustM.ok.inj returned
      rfl
    · rename_i opened lengthGood
      have inside : 8 ≤ opened.plaintext.val.length := by
        have large : 8 < opened.plaintext.val.length := by
          simpa [pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE] using lengthGood
        omega
      obtain ⟨⟨boundPart, applicationPart⟩, splitRun⟩ : ∃ parts,
          core.slice.Slice.split_at opened.plaintext pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE = .ok parts := by
        simp [core.slice.Slice.split_at, rust_primitives.slice.slice_split_at,
          Aeneas.Std.core.slice.Slice.split_at, pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE, Slice.length, inside]
      obtain ⟨converted, convertedRun⟩ := copied_slice_total 8#usize boundPart
      cases converted with
      | Err error =>
          simp [splitRun, convertedRun] at returned
          cases returned
          rfl
      | Ok bound =>
          obtain ⟨authenticated, authRun⟩ := authenticate_registration_key_id_binding_ok pending.agreement.candidate opened.key_id bound
          cases authenticated <;>
            simp [splitRun, convertedRun, authRun, pqxdh.AuthenticatedBeaconRegistration.assigned_key_id,
              session.CompletedRegistrationBinding.finish, pqxdh.beacon_commit] at returned
          cases returned
          rfl

theorem program_rejected_key (phase : registration.BeaconInitialOpen) (aborted : pqxdh.BeaconAborted)
    (supported : .ok (.Err aborted) ∈ support (program phase)) : aborted.server_key_id = phaseId phase := by
  cases shape : phase with
  | KdfRequested pending =>
      rw [shape] at supported
      obtain ⟨request, requested⟩ := BeaconRecordKdf_request_total pending
      rw [program.eq_def] at supported
      simp only [requested, continueWith, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      obtain ⟨result, resumed⟩ := BeaconRecordKdf_resume_total pending reply
      rw [resumed] at continued
      cases result with
      | Err rejected =>
          simp only [support_pure, Set.mem_singleton_iff, RustM.ok.injEq, core.result.Result.Err.injEq] at continued
          rw [continued]
          exact kdf_key pending reply (.Err rejected) resumed
      | Ok next => exact (program_rejected_key next aborted continued).trans (kdf_key pending reply (.Ok next) resumed)
  | CommitmentRequested pending =>
      rw [shape] at supported
      obtain ⟨transcript, requested⟩ := BeaconRecordCommitment_transcript_total pending
      obtain ⟨supplied, suppliedRun⟩ := BeaconRecordCommitment_supplied_commitment_total pending
      rw [program.eq_def] at supported
      simp only [requested, continueWith, mem_support_bind_iff] at supported
      obtain ⟨digest, _, continued⟩ := supported
      simp only [suppliedRun] at continued
      obtain ⟨result, resumed⟩ := BeaconRecordCommitment_resume_total pending (commitmentMatches digest supplied)
      rw [resumed] at continued
      cases result with
      | Err rejected =>
          simp only [support_pure, Set.mem_singleton_iff, RustM.ok.injEq, core.result.Result.Err.injEq] at continued
          rw [continued]
          exact commitment_key pending (commitmentMatches digest supplied) (.Err rejected) resumed
      | Ok next => exact (program_rejected_key next aborted continued).trans (commitment_key pending (commitmentMatches digest supplied) (.Ok next) resumed)
  | AeadRequested pending =>
      rw [shape] at supported
      obtain ⟨request, requested⟩ := BeaconRecordAead_request_total pending
      rw [program.eq_def] at supported
      simp only [requested, continueWith] at supported
      cases request with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at supported
          exact aead_rejected_key pending .None aborted supported.symm
      | some request =>
          simp only [mem_support_bind_iff] at supported
          obtain ⟨plaintext, _, returned⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at returned
          exact aead_rejected_key pending plaintext aborted returned.symm
termination_by rank phase
decreasing_by
  · simpa only [shape] using kdf_rank pending reply next resumed
  · simpa only [shape] using commitment_rank pending (commitmentMatches digest supplied) next resumed

theorem initial_rejected_key (pending : registration.BeaconInitialKdf) (aborted : pqxdh.BeaconAborted)
    (supported : .ok (.Err aborted) ∈ support (fromInitial pending)) :
    aborted.server_key_id = pending.agreement.candidate.server_binding.identity_key_id := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitialKdf_request_total pending
  simp only [fromInitial, requested, continueWith, mem_support_bind_iff] at supported
  obtain ⟨reply, _, continued⟩ := supported
  obtain ⟨result, resumed⟩ := BeaconInitialKdf_resume_total pending reply
  rw [resumed] at continued
  cases result with
  | Err rejected =>
      simp only [support_pure, Set.mem_singleton_iff, RustM.ok.injEq, core.result.Result.Err.injEq] at continued
      rw [continued]
      exact initial_key pending reply (.Err rejected) resumed
  | Ok next => exact (program_rejected_key next aborted continued).trans (initial_key pending reply (.Ok next) resumed)

theorem begin_rejected_key (agreed : agreement.BeaconAgreement) (aborted : pqxdh.BeaconAborted)
    (supported : .ok (.Err aborted) ∈ support (begin agreed)) :
    aborted.server_key_id = agreed.candidate.server_binding.identity_key_id := by
  obtain ⟨pending, started⟩ := begin_beacon_completion_total agreed
  have agreementSame := initial_agreement agreed pending started
  simp only [begin, started, continueWith] at supported
  simpa only [agreementSame] using initial_rejected_key pending aborted supported

end BeaconcryptCore.Computational.RegistrationBeaconRecordKey

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.normalized_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.normalized_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.kdf_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.kdf_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.commitment_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.commitment_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.initial_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.initial_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.aead_rejected_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.aead_rejected_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.program_rejected_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.program_rejected_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.initial_rejected_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.initial_rejected_key

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordKey.begin_rejected_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordKey.begin_rejected_key
