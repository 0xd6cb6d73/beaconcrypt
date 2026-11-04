-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordReceive
import BeaconcryptCore.PanicFreedom.AdapterNormal

/-! Normal native receive execution under four external-leaf normal-return contracts. The safety rank includes the commitment and AEAD phases as well as the source-derived KDF rank, and permits every optional rejection. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterRecordReceive
variable [operations : beaconcrypt.ratchet.Operations]

structure Contracts : Prop where
  kdf : ∀ request, ∃ result, operations.kdf request = ok result
  hash : ∀ transcript, ∃ result, operations.hash transcript = ok result
  aead : ∀ request, ∃ result, operations.aead request = ok result
  compare : ∀ left right, ∃ result, operations.compare left right = ok result

omit operations in
theorem output_call_once_total (c : beaconcrypt.ratchet.execute_record_receive.closure)
    (args : record.OpenedRecord (alloc.vec.Vec U8)) :
    ∃ result, beaconcrypt.ratchet.execute_record_receive.closure.Insts.CoreOpsFunctionFnOnceTupleOpenedRecordVecU8Decrypted.call_once c args = ok result :=
  ⟨_, rfl⟩

theorem execute_record_receive_loop_body_total (contracts : Contracts) (effect : record_effects.RecordReceiveEffect) :
    ∃ result, beaconcrypt.ratchet.execute_record_receive_loop.body effect = ok result := by
  cases effect with
  | Rejected kernel => exact ⟨_, rfl⟩
  | KdfRequested pending =>
    exact (RecordEffects.RecordReceiveKdf_request_total pending).elim fun request requested =>
      (contracts.kdf request).elim fun reply replied =>
      (RecordEffects.RecordReceiveKdf_resume_total pending reply).elim fun next resumed =>
      ⟨.cont next, by simp only [beaconcrypt.ratchet.execute_record_receive_loop.body, requested,
        beaconcrypt.ratchet.ratchet_hkdf, replied, resumed, bind_tc_ok]⟩
  | CommitmentRequested pending =>
    simp only [beaconcrypt.ratchet.execute_record_receive_loop.body]
    apply AdapterNormal.normal_bind _ _ (RecordEffects.RecordReceiveCommitment_transcript_mut_total pending)
    rintro ⟨ct, back⟩
    apply AdapterNormal.normal_bind _ _ (contracts.hash ct)
    rintro ⟨actual, changed⟩
    cases actual with
    | none =>
      simp! only [bind_tc_ok]
      exact AdapterNormal.normal_bind _ _ (RecordEffects.RecordReceiveCommitment_resume_total (back changed) false)
        (fun next => ⟨.cont next, rfl⟩)
    | some actual =>
      simp! only [lift, bind_tc_ok]
      refine AdapterNormal.normal_bind _ _ ?_ ?_
      · exact (RecordEffects.RecordReceiveCommitment_supplied_commitment_total (back changed)).elim fun supplied requested =>
          (contracts.compare actual.to_slice supplied.to_slice).elim fun matched compared =>
          ⟨(back changed, matched), by simp only [requested, beaconcrypt_crypto.utils.memcmp, compared, bind_tc_ok]⟩
      · rintro ⟨nextPending, matched⟩
        exact AdapterNormal.normal_bind _ _ (RecordEffects.RecordReceiveCommitment_resume_total nextPending matched)
          (fun next => ⟨.cont next, rfl⟩)
  | AeadRequested pending =>
    exact (RecordEffects.RecordReceiveAead_request_total pending).elim fun request requested =>
      (contracts.aead request).elim fun plaintext opened =>
      (RecordEffects.RecordReceiveAead_finish_total pending plaintext).elim fun result finished =>
      ⟨.done (result.1, Option.map Refinement.AdapterRecordReceive.publicOpened result.2), by
        cases result
        simp! only [beaconcrypt.ratchet.execute_record_receive_loop.body, requested,
          beaconcrypt.ratchet.execute_open_request, opened, finished,
          Refinement.AdapterRecordReceive.output_map, bind_tc_ok]⟩

/-- The KDF counter decreases across ratchet catch-up; the last two units account for commitment and AEAD. -/
def rank (effect : record_effects.RecordReceiveEffect) : Nat :=
  3 * Computational.RecordEffectsReceiveRank.rank effect +
    match effect with
    | .CommitmentRequested _ => 2
    | .AeadRequested _ => 1
    | _ => 0

omit operations in
private theorem rank_bound (effect : record_effects.RecordReceiveEffect) :
    rank effect ≤ 3 * Computational.RecordEffectsReceiveRank.rank effect + 2 := by
  cases effect <;> simp only [rank] <;> omega

omit operations in
private theorem bind_ok_parts {A B : Type} {work : RustM A} {next : A → RustM B} {result : B}
    (returned : (work >>= next) = ok result) :
    ∃ value, work = ok value ∧ next value = ok result := by
  cases work with
  | ok value => exact ⟨value, rfl, returned⟩
  | fail error => cases returned
  | div => cases returned

omit operations in
private theorem commitment_rank (pending : record_effects.RecordReceiveCommitment) (matched : Bool)
    (next : record_effects.RecordReceiveEffect) (resumed : pending.resume matched = ok next) :
    rank next ≤ 1 := by
  obtain ⟨opening, opened⟩ := Record.resume_total pending.pending matched
  simp only [record_effects.RecordReceiveCommitment.resume, opened, bind_tc_ok] at resumed
  cases opening <;> cases resumed <;> simp only [rank, Computational.RecordEffectsReceiveRank.rank] <;> omega

/-- Every continued actual source iteration decreases a structural rank, independently of the external implementation. -/
theorem body_progress (before after : record_effects.RecordReceiveEffect)
    (actual : beaconcrypt.ratchet.execute_record_receive_loop.body before = ok (.cont after)) :
    rank after < rank before := by
  cases before with
  | Rejected kernel => cases actual
  | KdfRequested pending =>
    simp only [beaconcrypt.ratchet.execute_record_receive_loop.body] at actual
    obtain ⟨request, _requested, actual⟩ := bind_ok_parts actual
    obtain ⟨reply, _replied, actual⟩ := bind_ok_parts actual
    obtain ⟨next, resumed, actual⟩ := bind_ok_parts actual
    have same : next = after := ControlFlow.cont.inj (RustM.ok.inj actual)
    subst after
    have decreasing := Computational.RecordEffectsReceiveRank.resume_decreasing pending reply next resumed
    have bounded := rank_bound next
    change rank next < 3 * Computational.RecordEffectsReceiveRank.rank (.KdfRequested pending)
    omega
  | CommitmentRequested pending =>
    simp only [beaconcrypt.ratchet.execute_record_receive_loop.body] at actual
    obtain ⟨⟨ct, back⟩, _requested, actual⟩ := bind_ok_parts actual
    obtain ⟨⟨digest, changed⟩, _hashed, actual⟩ := bind_ok_parts actual
    obtain ⟨⟨selected, matched⟩, _compared, actual⟩ := bind_ok_parts actual
    obtain ⟨next, resumed, actual⟩ := bind_ok_parts actual
    have same : next = after := ControlFlow.cont.inj (RustM.ok.inj actual)
    subst after
    have bounded := commitment_rank selected matched next resumed
    change rank next < 2
    omega
  | AeadRequested pending =>
    simp only [beaconcrypt.ratchet.execute_record_receive_loop.body] at actual
    obtain ⟨request, _requested, actual⟩ := bind_ok_parts actual
    obtain ⟨plaintext, _opened, actual⟩ := bind_ok_parts actual
    obtain ⟨⟨kernel, output⟩, _finished, actual⟩ := bind_ok_parts actual
    obtain ⟨mapped, _mapped, actual⟩ := bind_ok_parts actual
    cases actual

theorem execute_record_receive_loop_total (contracts : Contracts) (effect : record_effects.RecordReceiveEffect) :
    ∃ result, beaconcrypt.ratchet.execute_record_receive_loop effect = ok result :=
  AdapterNormal.normal_loop beaconcrypt.ratchet.execute_record_receive_loop.body rank
    (execute_record_receive_loop_body_total contracts) body_progress effect

theorem execute_record_receive_total (contracts : Contracts) (effect : record_effects.RecordReceiveEffect) :
    ∃ result, beaconcrypt.ratchet.execute_record_receive effect = ok result :=
  execute_record_receive_loop_total contracts effect

end BeaconcryptCore.PanicFreedom.AdapterRecordReceive
