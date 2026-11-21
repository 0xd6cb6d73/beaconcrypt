-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor
import BeaconcryptCore.PanicFreedom.RegistrationPublication
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
/-! Actual first-record normality follows the extracted Core getter, resume and finish totality theorems. Optional HKDF failure, missing or mismatched commitment and rejected AEAD all remain normal rejection results; no successful opening or whole-controller normality premise is added. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconRecordNormal
open RegistrationBeaconRecordExecutor
open RegistrationRecordPrimitives (Spec)
open BeaconcryptCore.PanicFreedom.RegistrationPublication
open BeaconcryptCore.PanicFreedom.RegistrationTrivial

def Normal (work : OracleComp Spec (RustM Result)) : Prop :=
  ∀ outcome, outcome ∈ support work → ∃ result, outcome = .ok result

private theorem pure_normal (result : Result) : Normal (pure (.ok result)) := by
  intro outcome supported
  exact ⟨result, by simpa only [support_pure, Set.mem_singleton_iff] using supported⟩

theorem program_normal (phase : registration.BeaconInitialOpen) : Normal (program phase) := by
  cases phase with
  | KdfRequested pending =>
      obtain ⟨request, requested⟩ := BeaconRecordKdf_request_total pending
      intro outcome supported
      rw [program.eq_def] at supported
      simp only [requested, continueWith, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      obtain ⟨result, resumed⟩ := BeaconRecordKdf_resume_total pending reply
      rw [resumed] at continued
      cases result with
      | Err aborted => exact pure_normal (.Err aborted) outcome continued
      | Ok next => exact program_normal next outcome continued
  | CommitmentRequested pending =>
      obtain ⟨transcript, requested⟩ := BeaconRecordCommitment_transcript_total pending
      obtain ⟨supplied, suppliedRun⟩ := BeaconRecordCommitment_supplied_commitment_total pending
      intro outcome supported
      rw [program.eq_def] at supported
      simp only [requested, continueWith, mem_support_bind_iff] at supported
      obtain ⟨digest, _, continued⟩ := supported
      simp only [suppliedRun] at continued
      obtain ⟨result, resumed⟩ := BeaconRecordCommitment_resume_total pending (commitmentMatches digest supplied)
      rw [resumed] at continued
      cases result with
      | Err aborted => exact pure_normal (.Err aborted) outcome continued
      | Ok next => exact program_normal next outcome continued
  | AeadRequested pending =>
      obtain ⟨request, requested⟩ := BeaconRecordAead_request_total pending
      intro outcome supported
      rw [program.eq_def] at supported
      simp only [requested, continueWith] at supported
      cases request with
      | none =>
          obtain ⟨result, finished⟩ := BeaconRecordAead_finish_total pending .None
          rw [finished] at supported
          exact pure_normal result outcome supported
      | some request =>
          simp only [mem_support_bind_iff] at supported
          obtain ⟨plaintext, _, returned⟩ := supported
          obtain ⟨result, finished⟩ := BeaconRecordAead_finish_total pending plaintext
          rw [finished] at returned
          exact pure_normal result outcome returned
termination_by rank phase
decreasing_by
  · exact kdf_rank pending reply next resumed
  · exact commitment_rank pending (commitmentMatches digest supplied) next resumed

theorem initial_normal (pending : registration.BeaconInitialKdf) : Normal (fromInitial pending) := by
  obtain ⟨request, requested⟩ := BeaconInitialKdf_request_total pending
  intro outcome supported
  simp only [fromInitial, requested, continueWith, mem_support_bind_iff] at supported
  obtain ⟨reply, _, continued⟩ := supported
  obtain ⟨result, resumed⟩ := BeaconInitialKdf_resume_total pending reply
  rw [resumed] at continued
  cases result with
  | Err aborted => exact pure_normal (.Err aborted) outcome continued
  | Ok next => exact program_normal next outcome continued

theorem begin_normal (agreed : agreement.BeaconAgreement) : Normal (begin agreed) := by
  obtain ⟨pending, started⟩ := begin_beacon_completion_total agreed
  simp only [begin, started, continueWith]
  exact initial_normal pending

end BeaconcryptCore.Computational.RegistrationBeaconRecordNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordNormal.program_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordNormal.program_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordNormal.initial_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordNormal.initial_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordNormal.begin_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordNormal.begin_normal
