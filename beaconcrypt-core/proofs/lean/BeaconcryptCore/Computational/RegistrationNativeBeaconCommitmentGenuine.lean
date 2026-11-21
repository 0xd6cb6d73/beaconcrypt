-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconRecordTrace
import BeaconcryptCore.Refinement.NativeRecordWrapper

/-! Initial and receive-KDF source normalization create genuine CTX transcripts from the exact selected material and opening context. The actual pre-commitment trace carries this construction witness to the checked hash phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.NativeRecordWrapper
open BeaconcryptCore.Refinement.CommitmentSurface

/-- The transcript was constructed by the source builder using this opening's actual selected material and sequence. -/
def Genuine : registration.BeaconInitialOpen → Prop
  | .KdfRequested _ | .AeadRequested _ => True
  | .CommitmentRequested pending =>
    ∃ (material : RatchetMaterial) (sequence : U64),
      pending.pending.pending.opening.material = .ok (.Some material) ∧
      pending.pending.pending.opening.sequence = .ok sequence ∧
      pending.pending.pending.transcript.bytes = productionInput (selectedFields pending.pending.pending.opening material sequence)

private theorem normalize_old (agreement : agreement.BeaconAgreement)
    (effect : ReceiveEffect record.OpenFrameContext) (next : registration.BeaconInitialOpen)
    (actual : (do let current ← record_effects.normalize_receive effect; registration.normalize_beacon_open agreement current) = .ok (.Ok next)) :
    Genuine next := by
  cases effect with
  | ReceiveRejected kernel context =>
    simp [record_effects.normalize_receive, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate] at actual
  | ReceiveKdfRequested pending =>
    simp only [record_effects.normalize_receive, registration.normalize_beacon_open, bind_tc_ok,
      RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
    cases actual
    trivial
  | ReceiveOpenRequested opening =>
    obtain ⟨material, materialRun⟩ := (getters_normal opening).1
    cases material with
    | none =>
      simp [record_effects.normalize_receive, begin_missing opening materialRun, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate] at actual
    | some material =>
      obtain ⟨sequence, sequenceRun⟩ := (getters_normal opening).2
      simp only [record_effects.normalize_receive, begin_selected opening material sequence materialRun sequenceRun,
        registration.normalize_beacon_open, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
      cases actual
      exact ⟨material, sequence, materialRun, sequenceRun, rfl⟩

/-- The actual initial source continuation constructs a genuine transcript whenever it reaches commitment verification. -/
theorem initial (pending : registration.BeaconInitialKdf)
    (reply : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse) (next : registration.BeaconInitialOpen)
    (actual : pending.resume reply = .ok (.Ok next)) : Genuine next := by
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

/-- Every actual source KDF continuation constructs a genuine transcript whenever it reaches commitment verification. -/
theorem kdf (pending : registration.BeaconRecordKdf)
    (reply : core.option.Option ratchet.RatchetKdfResponse) (next : registration.BeaconInitialOpen)
    (actual : pending.resume reply = .ok (.Ok next)) : Genuine next := by
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

/-- The actual recorded KDF prefix retains source transcript genuineness until the reached hash phase. -/
theorem along_prefix {S : Type} (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    {first last : registration.BeaconInitialOpen} {before after : S}
    (actual : RegistrationNativeBeaconRecordTrace.Prefix implementation first before last after)
    (prior : Genuine first) : Genuine last := by
  induction actual with
  | refl => exact prior
  | step pending request reply next before middle after last requested called resumed following ih =>
    exact ih (kdf pending reply next resumed)

end BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine.kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine.kdf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine.along_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine.along_prefix
