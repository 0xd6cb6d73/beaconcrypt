-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RecordEffects
import BeaconcryptCore.PanicFreedom.Record
import BeaconcryptCore.PanicFreedom.Pqxdh

/-! Unconditional normal returns for every composed record-controller operation, including arbitrary represented states and all typed primitive or writer replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.RecordEffects

/-- Every rejected, KDF or opening effect normalizes without a validity or primitive-success premise. -/
theorem normalize_receive_total (effect : ratchet.concrete.ReceiveEffect record.OpenFrameContext) :
    ∃ result, record_effects.normalize_receive effect = ok result := by
  cases effect with
  | ReceiveRejected kernel context => exact ⟨_, rfl⟩
  | ReceiveKdfRequested pending => exact ⟨_, rfl⟩
  | ReceiveOpenRequested opening =>
    obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.Record.begin_total opening
    cases next <;> simp [record_effects.normalize_receive, nextRun]

theorem SealFrameContext_new_total (plaintext : Slice Std.U8) (target_kid : Std.U64) (sender_kid : Std.U64)
  (associated_data : Array Std.U8 281#usize)
  (encoding : record_effects.RecordEncoding) :
    ∃ result, record_effects.SealFrameContext.new plaintext target_kid sender_kid associated_data encoding = ok result :=
  ⟨_, rfl⟩

theorem RecordSendKdf_request_total (self : record_effects.RecordSendKdf) :
    ∃ result, record_effects.RecordSendKdf.request self = ok result :=
  ⟨_, rfl⟩

theorem RecordSendKdf_cancel_total (self : record_effects.RecordSendKdf) :
    ∃ result, record_effects.RecordSendKdf.cancel self = ok result :=
  ⟨_, rfl⟩

theorem SealCommitment_impl_transcript_total (self : record_effects.SealCommitment) :
    ∃ result, record_effects.SealCommitment.impl.transcript self = ok result :=
  ⟨_, rfl⟩

theorem SealCommitment_transcript_mut_total (self : record_effects.SealCommitment) :
    ∃ result, record_effects.SealCommitment.transcript_mut self = ok result :=
  ⟨_, rfl⟩

theorem RecordReceiveKdf_request_total (self : record_effects.RecordReceiveKdf) :
    ∃ result, record_effects.RecordReceiveKdf.request self = ok result :=
  ⟨_, rfl⟩

theorem RecordReceiveKdf_cancel_total (self : record_effects.RecordReceiveKdf) :
    ∃ result, record_effects.RecordReceiveKdf.cancel self = ok result :=
  ⟨_, rfl⟩

theorem RecordReceiveCommitment_transcript_total (self : record_effects.RecordReceiveCommitment) :
    ∃ result, record_effects.RecordReceiveCommitment.transcript self = ok result :=
  ⟨_, rfl⟩

theorem RecordReceiveCommitment_transcript_mut_total (self : record_effects.RecordReceiveCommitment) :
    ∃ result, record_effects.RecordReceiveCommitment.transcript_mut self = ok result :=
  ⟨_, rfl⟩

theorem RecordReceiveCommitment_supplied_commitment_total (self : record_effects.RecordReceiveCommitment) :
    ∃ result, record_effects.RecordReceiveCommitment.supplied_commitment self = ok result :=
  ⟨_, rfl⟩

theorem RecordEncoding_Insts_CoreCloneClone_clone_total (self : record_effects.RecordEncoding) :
    ∃ result, record_effects.RecordEncoding.Insts.CoreCloneClone.clone self = ok result :=
  match self with
  | .Raw => ⟨_, rfl⟩
  | .Frame => ⟨_, rfl⟩

theorem SealFrameContext_plaintext_request_total (self : record_effects.SealFrameContext) :
    ∃ result, record_effects.SealFrameContext.plaintext_request self = ok result :=
  match prefixEq : self.prefix with
  | .None => ⟨.Single self.plaintext, by simp only [record_effects.SealFrameContext.plaintext_request, prefixEq]⟩
  | .Some bytes => ⟨.Prefixed bytes self.plaintext, by simp only [record_effects.SealFrameContext.plaintext_request, prefixEq]⟩

theorem RecordSendKdf_resume_total (self : record_effects.RecordSendKdf) (response : ratchet.RatchetKdfResponse) :
    ∃ result, record_effects.RecordSendKdf.resume self response = ok result :=
  (ratchet.concrete.SendKdf.resume_total self.pending response).elim fun sealed run =>
    ⟨⟨sealed⟩, by simp only [record_effects.RecordSendKdf.resume, run, bind_tc_ok]⟩

theorem reject_send_total (pending : ratchet.concrete.SendSeal record_effects.SealFrameContext) :
    ∃ result, record_effects.reject_send pending = ok result :=
  ratchet.concrete.SendSeal.finish_total pending (.None : core.option.Option Unit)

theorem RecordReceiveKdf_resume_total (self : record_effects.RecordReceiveKdf)
  (response : ratchet.RatchetKdfResponse) :
    ∃ result, record_effects.RecordReceiveKdf.resume self response = ok result :=
  (ratchet.concrete.ReceiveKdf.resume_total self.pending response).elim fun next run =>
    (normalize_receive_total next).imp (fun _ normal => by
      simpa only [record_effects.RecordReceiveKdf.resume, run, bind_tc_ok] using normal)

theorem RecordReceiveCommitment_resume_total (self : record_effects.RecordReceiveCommitment) (commitment_matches : Bool) :
    ∃ result, record_effects.RecordReceiveCommitment.resume self commitment_matches = ok result :=
  (BeaconcryptCore.PanicFreedom.Record.resume_total self.pending commitment_matches).elim fun next run =>
    match next, run with
    | .OpenCommitmentRejected kernel, run =>
        ⟨.Rejected kernel, by simp only [record_effects.RecordReceiveCommitment.resume, run, bind_tc_ok]⟩
    | .OpenAeadRequested opening, run =>
        ⟨.AeadRequested ⟨opening⟩, by simp only [record_effects.RecordReceiveCommitment.resume, run, bind_tc_ok]⟩

theorem RecordReceiveAead_request_total (self : record_effects.RecordReceiveAead) :
    ∃ result, record_effects.RecordReceiveAead.request self = ok result :=
  BeaconcryptCore.PanicFreedom.Record.request_total self.pending

theorem RecordReceiveAead_finish_total {Plaintext : Type} (self : record_effects.RecordReceiveAead)
  (plaintext : core.option.Option Plaintext) :
    ∃ result, record_effects.RecordReceiveAead.finish (Plaintext := Plaintext) self plaintext = ok result :=
  BeaconcryptCore.PanicFreedom.Record.finish_total self.pending plaintext

theorem begin_record_receive_total (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
  (ciphertext : Slice Std.U8) (associated_data : Array Std.U8 281#usize)
  (sender : Std.U64) :
    ∃ result, record_effects.begin_record_receive kernel sequence ciphertext associated_data sender = ok result :=
  (BeaconcryptCore.PanicFreedom.Record.payload_total ciphertext associated_data sender).elim fun context admitted =>
    match context, admitted with
    | .None, admitted =>
        ⟨.Rejected kernel, by simp only [record_effects.begin_record_receive, admitted, bind_tc_ok]⟩
    | .Some context, admitted =>
        (ratchet.concrete.begin_receive_total kernel sequence context).elim fun effect begun =>
          (normalize_receive_total effect).imp (fun _ normal => by
            simpa only [record_effects.begin_record_receive, admitted, begun, bind_tc_ok] using normal)

theorem SealFrameContext_registration_total (application : Slice Std.U8) (assigned_kid : Std.U64) (sender_kid : Std.U64)
  (associated_data : Array Std.U8 281#usize) :
    ∃ result, record_effects.SealFrameContext.registration application assigned_kid sender_kid associated_data = ok result :=
  (BeaconcryptCore.PanicFreedom.registration_key_id_binding_ok assigned_kid).elim fun bound run =>
    ⟨⟨application, .Some bound.bytes, associated_data, assigned_kid, sender_kid, .Raw⟩,
      by simp only [record_effects.SealFrameContext.registration, run,
        pqxdh.RegistrationKeyIdBinding.as_bytes, bind_tc_ok]⟩

theorem SealAead_request_total (self : record_effects.SealAead) :
    ∃ result, record_effects.SealAead.request self = ok result :=
  (SealFrameContext_plaintext_request_total self.seal.context).elim fun plaintext run =>
    ⟨⟨self.seal.material.key.bytes, self.seal.material.nonce.bytes,
      self.seal.context.associated_data, plaintext⟩, by
      simp only [record_effects.SealAead.request, ratchet.concrete.SendSeal.impl.material,
        ratchet.concrete.SendSeal.impl.context, ratchet.RatchetMaterial.impl.key,
        ratchet.RatchetMaterial.impl.nonce, ratchet.RatchetKey.as_bytes,
        ratchet.RatchetNonce.as_bytes, run, bind_tc_ok]⟩

theorem SealAead_resume_total (self : record_effects.SealAead)
  (detached : core.option.Option ((Slice Std.U8) × (Array Std.U8 16#usize))) :
    ∃ result, record_effects.SealAead.resume self detached = ok result :=
  match detached with
  | .None => ⟨_, BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact self⟩
  | .Some (ciphertext, tag) =>
      (BeaconcryptCore.Refinement.RecordEffects.seal_aead_supplied_exact self ciphertext tag).elim
        (fun _next facts => ⟨_, facts.1⟩)

theorem SealCommitment_resume_total (self : record_effects.SealCommitment)
  (commitment1 : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, record_effects.SealCommitment.resume self commitment1 = ok result :=
  match commitment1 with
  | .None => ⟨_, BeaconcryptCore.Refinement.RecordEffects.seal_commitment_missing_exact self⟩
  | .Some commitment =>
      ⟨_, BeaconcryptCore.Refinement.RecordEffects.seal_commitment_supplied_exact self commitment⟩

theorem SealWrite_finish_total {Output : Type} (self : record_effects.SealWrite)
  (written : core.option.Option Output) :
    ∃ result, record_effects.SealWrite.finish (Output := Output) self written = ok result :=
  ⟨_, BeaconcryptCore.Refinement.RecordEffects.seal_write_finish_exact self written⟩

end BeaconcryptCore.PanicFreedom.RecordEffects

/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.normalize_receive_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.normalize_receive_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealFrameContext_new_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealFrameContext_new_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordSendKdf_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordSendKdf_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordSendKdf_cancel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordSendKdf_cancel_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealCommitment_impl_transcript_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealCommitment_impl_transcript_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealCommitment_transcript_mut_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealCommitment_transcript_mut_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_cancel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_cancel_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_transcript_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_transcript_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_transcript_mut_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_transcript_mut_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_supplied_commitment_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_supplied_commitment_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordEncoding_Insts_CoreCloneClone_clone_total' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordEncoding_Insts_CoreCloneClone_clone_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealFrameContext_plaintext_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealFrameContext_plaintext_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordSendKdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordSendKdf_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.reject_send_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.reject_send_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveCommitment_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_finish_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.begin_record_receive_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.begin_record_receive_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealFrameContext_registration_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealFrameContext_registration_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealAead_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealAead_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealAead_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealAead_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealCommitment_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealCommitment_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RecordEffects.SealWrite_finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RecordEffects.SealWrite_finish_total
