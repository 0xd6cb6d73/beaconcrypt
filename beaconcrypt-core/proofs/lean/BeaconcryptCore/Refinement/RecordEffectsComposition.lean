-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs

/-! Exact equations expose the extracted record controller's composition of the existing send/open operations. Byte and control specifications are proved separately in `RecordEffects`. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RecordEffectsComposition

/-- Normalization preserves the exact kernel of a rejected old receive effect. -/
theorem normalize_rejected_exact (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record.OpenFrameContext) :
    record_effects.normalize_receive (.ReceiveRejected kernel context) = ok (.Rejected kernel) := rfl

/-- An old KDF capability is retained whole, without interpreting any primitive. -/
theorem normalize_kdf_exact (pending : ratchet.concrete.ReceiveKdf record.OpenFrameContext) :
    record_effects.normalize_receive (.ReceiveKdfRequested pending) = ok (.KdfRequested ⟨pending⟩) := rfl

/-- Opening normalization invokes the actual old opening operation before selecting its next effect. -/
theorem normalize_open_exact (opening : ratchet.concrete.ReceiveOpen record.OpenFrameContext) :
    record_effects.normalize_receive (.ReceiveOpenRequested opening) = (do
      let next ← record.begin_open opening
      match next with
      | .OpenRejected kernel => ok (.Rejected kernel)
      | .OpenCommitmentRequested pending => ok (.CommitmentRequested ⟨pending⟩)) := rfl

theorem send_kdf_request_exact (pending : record_effects.RecordSendKdf) :
    pending.request = ratchet.concrete.SendKdf.impl.request pending.pending := rfl

theorem send_kdf_cancel_exact (pending : record_effects.RecordSendKdf) :
    pending.cancel = ok pending.pending.entry := rfl

theorem send_kdf_resume_exact (pending : record_effects.RecordSendKdf)
    (response : ratchet.RatchetKdfResponse) :
    pending.resume response = (do
      let sealed ← ratchet.concrete.SendKdf.resume pending.pending response
      ok ⟨sealed⟩) := rfl

theorem receive_kdf_request_exact (pending : record_effects.RecordReceiveKdf) :
    pending.request = ratchet.concrete.ReceiveKdf.impl.request pending.pending := rfl

theorem receive_kdf_cancel_exact (pending : record_effects.RecordReceiveKdf) :
    pending.cancel = ok pending.pending.entry := rfl

/-- The actual receive KDF reply is resumed on its retained capability and then normalized. -/
theorem receive_kdf_resume_exact (pending : record_effects.RecordReceiveKdf)
    (response : ratchet.RatchetKdfResponse) :
    pending.resume response = (do
      let next ← ratchet.concrete.ReceiveKdf.resume pending.pending response
      record_effects.normalize_receive next) := rfl

/-- Commitment checking delegates the actual reply to the retained opening before selecting AEAD. -/
theorem receive_commitment_resume_exact (pending : record_effects.RecordReceiveCommitment)
    (matched : Bool) :
    pending.resume matched = (do
      let next ← record.OpenCommitment.resume pending.pending matched
      match next with
      | .OpenCommitmentRejected kernel => ok (.Rejected kernel)
      | .OpenAeadRequested opening => ok (.AeadRequested ⟨opening⟩)) := rfl

theorem receive_aead_request_exact (pending : record_effects.RecordReceiveAead) :
    pending.request = record.OpenAead.request pending.pending := rfl

/-- The actual optional plaintext is finished on the same retained receive capability. -/
theorem receive_aead_finish_exact {Plaintext : Type} (pending : record_effects.RecordReceiveAead)
    (plaintext : core.option.Option Plaintext) :
    pending.finish plaintext = record.OpenAead.finish pending.pending plaintext := rfl

end BeaconcryptCore.Refinement.RecordEffectsComposition

/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.normalize_rejected_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.normalize_rejected_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.normalize_kdf_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.normalize_kdf_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.normalize_open_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.normalize_open_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.send_kdf_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.send_kdf_request_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.send_kdf_cancel_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.send_kdf_cancel_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.send_kdf_resume_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.send_kdf_resume_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.receive_kdf_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.receive_kdf_request_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.receive_kdf_cancel_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.receive_kdf_cancel_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.receive_kdf_resume_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.receive_kdf_resume_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.receive_commitment_resume_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.receive_commitment_resume_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.receive_aead_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.receive_aead_request_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffectsComposition.receive_aead_finish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffectsComposition.receive_aead_finish_exact
