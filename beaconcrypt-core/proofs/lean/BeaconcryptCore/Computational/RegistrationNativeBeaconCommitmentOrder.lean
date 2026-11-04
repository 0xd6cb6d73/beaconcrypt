-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt

/-! The original Beacon controller cannot reach an AEAD phase before its commitment check. Initial and ongoing receive-KDF normalization produce only pre-commitment phases; successful commitment continuation is exactly the checked AEAD phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder
open BeaconcryptCore.Refinement.RegistrationRecords

def BeforeHash : registration.BeaconInitialOpen → Prop
  | .KdfRequested _ | .CommitmentRequested _ => True
  | .AeadRequested _ => False

private theorem normalize_old (agreement : agreement.BeaconAgreement)
    (effect : ratchet.concrete.ReceiveEffect record.OpenFrameContext) (next : registration.BeaconInitialOpen)
    (actual : (do let current ← record_effects.normalize_receive effect; registration.normalize_beacon_open agreement current) = .ok (.Ok next)) :
    BeforeHash next := by
  cases effect with
  | ReceiveRejected kernel context =>
    simp [record_effects.normalize_receive, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate] at actual
  | ReceiveKdfRequested pending =>
    simp only [record_effects.normalize_receive, registration.normalize_beacon_open, bind_tc_ok,
      RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
    cases actual
    trivial
  | ReceiveOpenRequested opening =>
    cases opened : record.begin_open opening with
    | fail error | div => simp [record_effects.normalize_receive, opened] at actual
    | ok result => cases result with
      | OpenRejected kernel =>
        simp [record_effects.normalize_receive, opened, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate] at actual
      | OpenCommitmentRequested pending =>
        simp only [record_effects.normalize_receive, opened, registration.normalize_beacon_open, bind_tc_ok,
          RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
        cases actual
        trivial

/-- The actual initial receive continuation cannot bypass the record commitment phase. -/
theorem initial (pending : registration.BeaconInitialKdf)
    (reply : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse) (next : registration.BeaconInitialOpen)
    (actual : pending.resume reply = .ok (.Ok next)) : BeforeHash next := by
  cases reply with
  | none => simp [registration.BeaconInitialKdf.resume, pqxdh.beacon_abort_candidate] at actual
  | some response =>
    rw [beacon_initial_request_refines] at actual
    obtain ⟨kernel, kernelRun⟩ := BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok pending.pending response
    rw [kernelRun, bind_tc_ok] at actual
    unfold record_effects.begin_record_receive at actual
    cases framed : record.OpenFrameContext.from_frame pending.agreement.application_ciphertext pending.agreement.binding.associated_data
        pending.agreement.candidate.server_binding.identity_key_id with
    | fail error | div => simp [framed] at actual
    | ok entry => cases entry with
      | none => simp [framed, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate] at actual
      | some context =>
        simp only [framed, bind_tc_ok] at actual
        cases received : ratchet.concrete.begin_receive kernel 1#u64 context with
        | fail error | div => simp [received] at actual
        | ok effect =>
          simp only [received, bind_tc_ok] at actual
          exact normalize_old pending.agreement effect next actual

/-- Every successful receive-KDF continuation is still before commitment verification. -/
theorem kdf (pending : registration.BeaconRecordKdf)
    (reply : core.option.Option ratchet.RatchetKdfResponse) (next : registration.BeaconInitialOpen)
    (actual : pending.resume reply = .ok (.Ok next)) : BeforeHash next := by
  cases reply with
  | none => simp [registration.BeaconRecordKdf.resume, pqxdh.beacon_abort_candidate] at actual
  | some response =>
    rw [beacon_kdf_reply_refines] at actual
    simp only [record_effects.RecordReceiveKdf.resume] at actual
    cases resumed : ratchet.concrete.ReceiveKdf.resume pending.pending.pending response with
    | fail error | div => simp [resumed] at actual
    | ok effect =>
      simp only [resumed, bind_tc_ok] at actual
      exact normalize_old pending.agreement effect next actual

/-- A successful commitment continuation must have matched and supplies exactly its AEAD source capability. -/
theorem commitment (pending : registration.BeaconRecordCommitment) (matched : Bool)
    (next : registration.BeaconInitialOpen) (actual : pending.resume matched = .ok (.Ok next)) :
    matched = true ∧ ∃ aead : registration.BeaconRecordAead, next = .AeadRequested aead := by
  cases matched with
  | false =>
    simp [beacon_commitment_reply_refines, record_effects.RecordReceiveCommitment.resume, record.OpenCommitment.resume,
      ratchet.concrete.ReceiveOpen.reject, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate] at actual
  | true =>
    simp only [beacon_commitment_reply_refines, record_effects.RecordReceiveCommitment.resume, record.OpenCommitment.resume,
      registration.normalize_beacon_open, ite_true, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
    exact ⟨rfl, _, actual.symm⟩

end BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder.kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder.kdf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder.commitment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder.commitment
