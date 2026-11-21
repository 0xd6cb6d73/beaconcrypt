-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordSendExtraction.Funs
import BeaconcryptCore.PanicFreedom.RecordEffects
import BeaconcryptCore.PanicFreedom.RecordEffectsSend
import BeaconcryptCore.PanicFreedom.AdapterNormal

/-! Safety of the extracted send driver under normal-return contracts for its four external leaves. Optional sealing, hashing and writer rejection are included, and the whole returned kernel is retained. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterRecordSend
variable [operations : beaconcrypt_record_send.ratchet.Operations]

structure Contracts : Prop where
  kdf : ∀ request, ∃ result, operations.kdf request = ok result
  sealing : ∀ request, ∃ result, operations.sealing request = ok result
  hash : ∀ transcript, ∃ result, operations.hash transcript = ok result
  writer : ∀ request, ∃ result, operations.writer request = ok result

omit operations in
theorem output_call_once_total
    (c : beaconcrypt_record_send.ratchet.execute_record_send.closure)
    (args : record_effects.SealedRecord (alloc.vec.Vec U8)) :
    ∃ result, beaconcrypt_record_send.ratchet.execute_record_send.closure.Insts.CoreOpsFunctionFnOnceTupleSealedRecordVecU8Encrypted.call_once c args = ok result :=
  ⟨_, rfl⟩

omit operations in
private theorem output_map_total (opened : core.option.Option (record_effects.SealedRecord (alloc.vec.Vec U8))) :
    ∃ result, core.option.Option.map
      beaconcrypt_record_send.ratchet.execute_record_send.closure.Insts.CoreOpsFunctionFnOnceTupleSealedRecordVecU8Encrypted
      opened () = ok result := by
  cases opened <;> exact ⟨_, rfl⟩

private def write (writer : record_effects.SealWrite) :
    RustM (ratchet.concrete.ConcreteRatchetKernel × core.option.Option beaconcrypt_record_send.shared.Encrypted) := do
  let request ← writer.request
  let written ← beaconcrypt_record_send.ratchet.execute_write_request request
  let (kernel, output) ← writer.finish written
  let mapped ← core.option.Option.map
    beaconcrypt_record_send.ratchet.execute_record_send.closure.Insts.CoreOpsFunctionFnOnceTupleSealedRecordVecU8Encrypted output ()
  ok (kernel, mapped)

private theorem write_total (contracts : Contracts) (writer : record_effects.SealWrite) :
    ∃ result, write writer = ok result := by
  exact (RecordEffectsSend.SealWrite_request_total writer).elim fun request requested =>
    (contracts.writer request).elim fun written writtenRun =>
    (RecordEffects.SealWrite_finish_total writer written).elim fun result finished =>
    (output_map_total result.2).elim fun mapped mappedRun =>
    ⟨(result.1, mapped), by cases result; simp! only [write, requested,
      beaconcrypt_record_send.ratchet.execute_write_request, writtenRun, finished, mappedRun, bind_tc_ok]⟩

theorem execute_record_send_total (contracts : Contracts)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) :
    ∃ result, beaconcrypt_record_send.ratchet.execute_record_send kernel context = ok result := by
  obtain ⟨start, started⟩ := RecordEffectsSend.begin_record_send_total kernel context
  cases start with
  | Rejected next =>
    exact ⟨(next, .None), by simp only [beaconcrypt_record_send.ratchet.execute_record_send, started, bind_tc_ok]⟩
  | KdfRequested pending =>
    exact (RecordEffects.RecordSendKdf_request_total pending).elim fun request requested =>
      (contracts.kdf request).elim fun reply replied =>
      (RecordEffects.RecordSendKdf_resume_total pending reply).elim fun aead resumed =>
      (RecordEffects.SealAead_request_total aead).elim fun sealRequest sealRequested =>
      (contracts.sealing sealRequest).elim fun detached sealed => by
        cases detached
        all_goals try (rename_i detached; rcases detached with ⟨body, tag⟩)
        all_goals simp only [beaconcrypt_record_send.ratchet.execute_record_send, started, requested,
          beaconcrypt_record_send.ratchet.ratchet_hkdf, replied, resumed, sealRequested,
          beaconcrypt_record_send.ratchet.execute_seal_request, sealed,
          core.option.Option.as_ref, alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice, bind_tc_ok]
        all_goals apply AdapterNormal.normal_bind _ _ (RecordEffects.SealAead_resume_total aead _)
        all_goals intro next
        all_goals cases next with
        | Rejected nextKernel => exact ⟨_, rfl⟩
        | CommitmentRequested nextPending =>
          apply AdapterNormal.normal_bind _ _ (RecordEffects.SealCommitment_transcript_mut_total nextPending)
          rintro ⟨ct, back⟩
          apply AdapterNormal.normal_bind _ _ (contracts.hash ct)
          rintro ⟨digest, changed⟩
          apply AdapterNormal.normal_bind _ _ (RecordEffects.SealCommitment_resume_total (back changed) digest)
          intro next
          cases next with
          | Rejected nextKernel => exact ⟨_, rfl⟩
          | WriteRequested writer => exact write_total contracts writer

end BeaconcryptCore.PanicFreedom.AdapterRecordSend
