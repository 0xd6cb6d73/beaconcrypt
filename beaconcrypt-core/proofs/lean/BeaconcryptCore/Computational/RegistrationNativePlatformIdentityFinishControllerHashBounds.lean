-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRecordNormal
import BeaconcryptCore.Computational.RegistrationResponseExecutor
import BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishPrimitiveHashBounds
/-! Source control bounds for corrected Beacon finish. Response authentication has one hash position; the actual ranked receive controller crosses its commitment position at most once, even with arbitrary receive-KDF continuations and optional primitive replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds
open RegistrationNativePlatformIdentityFinishPrimitiveHashBounds (IsRecordHash)
open BeaconcryptCore.PanicFreedom.RegistrationPublication
open BeaconcryptCore.PanicFreedom.RegistrationTrivial
open RegistrationBeaconRecordExecutor

def potential : registration.BeaconInitialOpen → Nat
  | .AeadRequested _ => 0
  | _ => 1
private theorem potential_le (phase : registration.BeaconInitialOpen) : potential phase ≤ 1 := by cases phase <;> simp [potential]
private theorem potential_terminal (phase : registration.BeaconInitialOpen) (small : rank phase < 2) : potential phase = 0 := by
  cases phase <;> simp only [rank, potential] at *
  all_goals omega

/-- The actual ranked first-open controller reaches at most one commitment hash, regardless of the number of receive-KDF continuations. -/
theorem record_program (phase : registration.BeaconInitialOpen) : (program phase).IsQueryBoundP IsRecordHash (potential phase) := by
  cases phase with
  | KdfRequested pending =>
      obtain ⟨request, requested⟩ := BeaconRecordKdf_request_total pending
      rw [program.eq_def]
      simp only [requested, continueWith, potential]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by simp [IsRecordHash]), ?_⟩
      intro reply
      obtain ⟨result, resumed⟩ := BeaconRecordKdf_resume_total pending reply
      rw [resumed]
      cases result with
      | Err aborted => exact isQueryBoundP_pure _ _ _
      | Ok next =>
          simpa only [IsRecordHash, ite_false] using (record_program next).mono (potential_le next)
  | CommitmentRequested pending =>
      obtain ⟨transcript, requested⟩ := BeaconRecordCommitment_transcript_total pending
      obtain ⟨supplied, suppliedRun⟩ := BeaconRecordCommitment_supplied_commitment_total pending
      rw [program.eq_def]
      simp only [requested, continueWith, potential]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by decide), ?_⟩
      intro digest
      simp only [suppliedRun]
      obtain ⟨result, resumed⟩ := BeaconRecordCommitment_resume_total pending (commitmentMatches digest supplied)
      rw [resumed]
      cases result with
      | Err aborted => exact isQueryBoundP_pure _ _ _
      | Ok next =>
          have terminal := potential_terminal next (commitment_rank pending (commitmentMatches digest supplied) next resumed)
          simpa only [IsRecordHash, ite_true, Nat.sub_self, terminal] using record_program next
  | AeadRequested pending =>
      obtain ⟨request, requested⟩ := BeaconRecordAead_request_total pending
      rw [program.eq_def]
      simp only [requested, continueWith, potential]
      cases request with
      | none => exact isQueryBoundP_pure _ _ _
      | some request =>
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [IsRecordHash]), fun _ => isQueryBoundP_pure _ _ _⟩
termination_by rank phase
decreasing_by
  · exact kdf_rank pending reply next resumed
  · exact commitment_rank pending (commitmentMatches digest supplied) next resumed

/-- Initial HKDF and all ranked record continuations retain the one-hash allowance on every actual optional primitive reply. -/
theorem record_begin (agreed : agreement.BeaconAgreement) : (begin agreed).IsQueryBoundP IsRecordHash 1 := by
  obtain ⟨initial, started⟩ := begin_beacon_completion_total agreed
  obtain ⟨request, requested⟩ := BeaconInitialKdf_request_total initial
  simp only [begin, started, continueWith, fromInitial, requested]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [IsRecordHash]), ?_⟩
  intro reply
  obtain ⟨result, resumed⟩ := BeaconInitialKdf_resume_total initial reply
  rw [resumed]
  cases result with
  | Err aborted => exact isQueryBoundP_pure _ _ _
  | Ok next => simpa only [IsRecordHash, ite_false] using (record_program next).mono (potential_le next)

private theorem response_continue {Input : Type} (result : RustM (core.result.Result Input pqxdh.BeaconAborted))
    (next : Input → OracleComp RegistrationAuthenticationExecutor.Spec (RustM RegistrationResponseExecutor.ResponseResult))
    (cap : Nat) (bounded : ∀ value, (next value).IsQueryBoundP RegistrationAuthenticationHashBounds.IsHash cap) :
    (RegistrationResponseExecutor.continueResult result next).IsQueryBoundP RegistrationAuthenticationHashBounds.IsHash cap := by
  cases result with
  | fail error | div => exact isQueryBoundP_pure _ _ _
  | ok result => cases result with
    | Err aborted => exact isQueryBoundP_pure _ _ _
    | Ok value => exact bounded value
private theorem response_with {Input : Type} (result : RustM Input)
    (next : Input → OracleComp RegistrationAuthenticationExecutor.Spec (RustM RegistrationResponseExecutor.ResponseResult))
    (cap : Nat) (bounded : ∀ value, (next value).IsQueryBoundP RegistrationAuthenticationHashBounds.IsHash cap) :
    (RegistrationAuthenticationExecutor.continueWith result next).IsQueryBoundP RegistrationAuthenticationHashBounds.IsHash cap := by
  cases result with
  | fail error | div => exact isQueryBoundP_pure _ _ _
  | ok value => exact bounded value

/-- Literal response authentication has one hash position and a hash-free ML verification, with every malformed/getter/resume failure retained. -/
theorem response_begin (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket) :
    (RegistrationResponseExecutor.begin pending packet).IsQueryBoundP RegistrationAuthenticationHashBounds.IsHash 1 := by
  unfold RegistrationResponseExecutor.begin
  apply response_continue _ _ 1
  intro hashing
  apply response_with _ _ 1
  intro request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), ?_⟩
  intro digest
  apply response_continue _ _ 0
  intro verification
  apply response_with _ _ 0
  intro verify
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [RegistrationAuthenticationHashBounds.IsHash]), fun _ => isQueryBoundP_pure _ _ _⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds.record_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds.record_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds.record_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds.record_begin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds.response_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds.response_begin
