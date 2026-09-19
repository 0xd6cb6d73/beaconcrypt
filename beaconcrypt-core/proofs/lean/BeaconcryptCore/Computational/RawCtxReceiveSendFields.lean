import BeaconcryptCore.Computational.RawCtxSourceSendPath
import BeaconcryptCore.Refinement.RatchetCachedPreparation
import BeaconcryptCore.Refinement.RatchetCachedPublication
import BeaconcryptCore.Refinement.RatchetFuturePublication

/-!
The original receive machine preserves the sender's chain and sequence under arbitrary stateful callback replies. The property is derived from the actual cached preparation, future validation and publication code, including failed openings and malformed original kernels. It does not assume a fixed KDF function, successful authentication or a supplied callback preservation law.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete ratchet.control
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxReceiveSendFields
variable {Context Plaintext State ι : Type} {base : OracleSpec ι}

def OpenGood (pending : ReceiveOpen Context) : Prop :=
  match pending.prepared with
  | .PreparedReceiveCachedCase prepared => prepared.committed_control.send_sequence = pending.entry.refined.control.send_sequence
  | .PreparedReceiveFutureCase prepared => prepared.committed_control.send_sequence = pending.entry.refined.control.send_sequence

def EffectGood : ReceiveEffect Context → Prop
  | .ReceiveOpenRequested pending => OpenGood pending
  | _ => True

private theorem valid_send (entry : ConcreteRatchetKernel)
    (pending : PendingReceive RatchetChain RatchetMaterial) (target : Std.U64)
    (valid : pending_receive_is_valid entry.refined pending target = ok true) :
    pending.committed_control.send_sequence = entry.refined.control.send_sequence := by
  by_contra different
  simp [pending_receive_is_valid, RatchetState.impl.receive_sequence,
    RatchetState.impl.send_sequence, RatchetState.receive_cache_len, different] at valid

private theorem control_send (state : RatchetState) (target : Std.U64) (slot : Std.U8)
    (result : ReceiveFinishWithRemoval)
    (finished : finish_receive_with_removal state target slot true = ok result) :
    result.state.send_sequence = state.send_sequence := by
  by_cases capacity : 50 < state.receive_cache.len.val
  · rw [finish_receive_with_removal_over_capacity state target slot true capacity] at finished
    cases finished
    rfl
  · have valid : state.Wf := by simp only [RatchetState.Wf, SequenceCache.Wf]; omega
    by_cases live : slot.val < state.receive_cache.len.val
    · by_cases same : state.receive_cache.entries.val[slot.val]! = target
      · obtain ⟨actual, run, _, _, retained, _⟩ := finish_receive_consumed state target slot valid live same
        cases RustM.ok.inj (run.symm.trans finished)
        exact retained
      · rw [finish_receive_with_removal_mismatch state target slot true valid live same] at finished
        cases finished
        rfl
    · rw [finish_receive_with_removal_out_of_range state target slot true (by omega)] at finished
      cases finished
      rfl

/-- Every last-step opening emitted by the actual resumption has the original sender sequence; other effects are inert for this property. -/
theorem resume_good (pending : ReceiveKdf Context) (response : RatchetKdfResponse) :
    EffectGood (RawCtxOwnerOracle.resume pending response) := by
  have actual := RawCtxOwnerOracle.resume_exact pending response
  generalize effectEq : RawCtxOwnerOracle.resume pending response = effect at actual ⊢
  clear effectEq
  by_cases zero : pending.remaining = 0#u8
  · simp only [ReceiveKdf.resume, zero, if_true, receive_rejected, RustM.ok.injEq] at actual
    subst effect
    trivial
  · simp only [ReceiveKdf.resume, zero, if_false] at actual
    split at actual
    · obtain ⟨advanced, advancedEq⟩ := advance_receive_target_total pending.working_control
      cases seqEq : advanced.sequence <;> simp only [advancedEq, seqEq, bind_tc_ok, receive_rejected] at actual
      · cases RustM.ok.inj actual
        trivial
      · rename_i sequence
        obtain ⟨stepped, steppedEq⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
        obtain ⟨valid, validEq⟩ := pending_receive_is_valid_ok pending.entry.refined
          { committed_control := advanced.state, final_receive_chain := stepped.chain,
            staged_slots := pending.staged_slots, target_sequence := sequence,
            target_material := stepped.material, first_slot := pending.first_slot, skipped := pending.skipped }
          pending.target
        simp only [steppedEq, validEq, bind_tc_ok] at actual
        split at actual
        · cases valid <;> simp only [Bool.false_eq_true, if_false, if_true, RustM.ok.injEq] at actual
          · subst effect
            trivial
          · subst effect
            exact valid_send pending.entry _ pending.target validEq
        · cases RustM.ok.inj actual
          trivial
    · obtain ⟨advanced, advancedEq⟩ := advance_receive_ok pending.working_control
      cases seqEq : advanced.sequence <;> cases slotEq : advanced.slot <;>
        simp only [advancedEq, seqEq, slotEq, lift, bind_tc_ok, receive_rejected] at actual
      all_goals first | (cases RustM.ok.inj actual; trivial) | skip
      rename_i sequence slot
      obtain ⟨logical, logicalEq⟩ := RatchetState.receive_key_at_total advanced.state slot
      obtain ⟨nextSlot, nextSlotEq, _⟩ := uscalar_add_eq_ok
        (UScalar.cast UScalarTy.Usize pending.first_slot) (UScalar.cast UScalarTy.Usize pending.skipped)
        (by scalar_tac)
      cases logical <;> simp only [logicalEq, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.U64.Insts.CoreCmpPartialEqU64, capacity_eq_ok, nextSlotEq, bind_tc_ok,
        Bool.false_eq_true, if_false] at actual
      all_goals first | (cases RustM.ok.inj actual; trivial) | skip
      repeat' first | (solve | cases RustM.ok.inj actual; trivial) | split at actual
      all_goals simp only [array_index_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
        (by scalar_tac), core.option.Option.is_some, bind_tc_ok, ite_self] at actual
      all_goals first | (cases RustM.ok.inj actual; trivial) | skip
      obtain ⟨skipped, skippedEq, _⟩ := uscalar_add_eq_ok pending.skipped 1#u8 (by scalar_tac)
      obtain ⟨remaining, remainingEq, _⟩ := uscalar_sub_eq_ok pending.remaining 1#u8 (by scalar_tac)
      obtain ⟨stepped, steppedEq⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
      simp only [steppedEq, skippedEq, remainingEq, RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
        array_update_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
          (.Some ⟨sequence, stepped.material⟩) (by scalar_tac), bind_tc_ok] at actual
      split at actual <;> cases RustM.ok.inj actual <;> trivial

/-- Original admission emits only a cached opening with the original sender sequence or a pending/rejected effect. -/
theorem begin_good (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context) :
    EffectGood (RawCtxOwnerOracle.begin entry target context) := by
  have actual := RawCtxOwnerOracle.begin_exact entry target context
  generalize effectEq : RawCtxOwnerOracle.begin entry target context = effect at actual ⊢
  clear effectEq
  obtain ⟨plan, planEq⟩ := plan_receive_until_total entry.refined.control target
  cases seqEq : plan.sequence <;> simp only [begin_receive, planEq, bind_tc_ok, seqEq, receive_rejected] at actual
  · cases RustM.ok.inj actual
    trivial
  · rename_i sequence
    split at actual
    · obtain ⟨prepared, preparedEq⟩ := prepare_cached_receive_total entry.refined sequence
      cases prepared with
      | none =>
          simp only [preparedEq, bind_tc_ok] at actual
          cases RustM.ok.inj actual
          trivial
      | some prepared =>
          simp only [preparedEq, bind_tc_ok] at actual
          cases RustM.ok.inj actual
          have facts := prepare_cached_receive_success_inv entry.refined sequence prepared preparedEq
          exact control_send entry.refined.control sequence prepared.target_slot _ facts.finish
    · obtain ⟨skipped, skippedEq, _⟩ := uscalar_sub_eq_ok plan.derivations 1#u64 (by scalar_tac)
      obtain ⟨empty, emptyEq⟩ := refined_receive_slots_are_empty_ok entry.refined
        entry.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped)
      cases empty <;> by_cases gap : skipped > RATCHET_MAX_GAP <;>
        simp only [skippedEq, lift, RatchetState.receive_cache_len, emptyEq, gap,
          RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, empty_material_slots,
          bind_tc_ok, Bool.false_eq_true, if_false, if_true] at actual
      all_goals cases RustM.ok.inj actual; trivial

private theorem cached_fields (entry : ConcreteRatchetKernel) (prepared : PreparedCachedReceive)
    (same : prepared.committed_control.send_sequence = entry.refined.control.send_sequence)
    (result : RefinedRatchet RatchetChain RatchetChain RatchetMaterial)
    (published : publish_cached_receive entry.refined prepared = ok result) :
    result.send_chain = entry.refined.send_chain ∧ result.control.send_sequence = entry.refined.control.send_sequence := by
  by_cases targetBound : prepared.target_slot.val < 50
  · by_cases lastBound : prepared.last_slot.val < 50
    · obtain ⟨actual, actualEq, controlEq, chainEq, _⟩ := publish_cached_receive_exact entry.refined prepared targetBound lastBound
      cases RustM.ok.inj (actualEq.symm.trans published)
      exact ⟨chainEq, controlEq ▸ same⟩
    · simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok,
        if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize prepared.target_slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
        if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.last_slot ≥ UScalar.cast UScalarTy.Usize 50#u64)] at published
      cases RustM.ok.inj published
      exact ⟨rfl, rfl⟩
  · simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok,
      if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.target_slot ≥ UScalar.cast UScalarTy.Usize 50#u64)] at published
    cases RustM.ok.inj published
    exact ⟨rfl, rfl⟩

private theorem future_fields (entry : ConcreteRatchetKernel) (prepared : PendingReceive RatchetChain RatchetMaterial)
    (same : prepared.committed_control.send_sequence = entry.refined.control.send_sequence)
    (result : RefinedRatchet RatchetChain RatchetChain RatchetMaterial)
    (published : publish_future_receive entry.refined prepared = ok result) :
    result.send_chain = entry.refined.send_chain ∧ result.control.send_sequence = entry.refined.control.send_sequence := by
  by_cases bound : prepared.first_slot.val + prepared.skipped.val ≤ 50
  · obtain ⟨actual, actualEq, controlEq, chainEq, _⟩ := publish_future_receive_exact entry.refined prepared bound
    cases RustM.ok.inj (actualEq.symm.trans published)
    exact ⟨chainEq, controlEq ▸ same⟩
  · simp only [publish_future_receive, lift, capacity_eq_ok, bind_tc_ok] at published
    by_cases firstBound : 50 < prepared.first_slot.val
    · rw [if_pos (by scalar_tac)] at published
      cases RustM.ok.inj published
      exact ⟨rfl, rfl⟩
    · rw [if_neg (by scalar_tac)] at published
      obtain ⟨available, availableEq, availableVal⟩ := uscalar_sub_eq_ok
        (UScalar.cast UScalarTy.Usize 50#u64) (UScalar.cast UScalarTy.Usize prepared.first_slot) (by scalar_tac)
      simp only [availableEq, bind_tc_ok,
        if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.skipped > available)] at published
      cases RustM.ok.inj published
      exact ⟨rfl, rfl⟩

/-- Actual publication keeps both send fields on success and failure, including defensive publication rejection. -/
theorem finish_fields (pending : ReceiveOpen Context) (good : OpenGood pending)
    (reply : core.option.Option Plaintext) :
    (RawCtxOwnerOracle.finish pending reply).1.refined.send_chain = pending.entry.refined.send_chain ∧
    (RawCtxOwnerOracle.finish pending reply).1.refined.control.send_sequence = pending.entry.refined.control.send_sequence := by
  cases reply with
  | none => rw [RawCtxOwnerOracle.finish_none]; exact ⟨rfl, rfl⟩
  | some value =>
      have actual := RawCtxOwnerOracle.finish_exact pending (.Some value)
      cases preparedEq : pending.prepared with
      | PreparedReceiveCachedCase prepared =>
          obtain ⟨published, publishedEq⟩ := publish_cached_receive_ok pending.entry.refined prepared
          simp only [ReceiveOpen.finish, preparedEq, publishedEq, bind_tc_ok, RustM.ok.injEq] at actual
          rw [← actual]
          exact cached_fields pending.entry prepared (by simpa only [OpenGood, preparedEq] using good) published publishedEq
      | PreparedReceiveFutureCase prepared =>
          obtain ⟨published, publishedEq⟩ := publish_future_receive_ok pending.entry.refined prepared
          simp only [ReceiveOpen.finish, preparedEq, publishedEq, bind_tc_ok, RustM.ok.injEq] at actual
          rw [← actual]
          exact future_fields pending.entry prepared (by simpa only [OpenGood, preparedEq] using good) published publishedEq

/-- Arbitrary supported callback effects retain the sender fields through the complete original finite receive execution. -/
theorem program_fields
    (impl : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) (StateT State (OracleComp base)))
    (state : State) (effect : ReceiveEffect Context) (good : EffectGood effect)
    (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × State)
    (supported : result ∈ support ((simulateQ impl (RawCtxOwnerOracle.program effect)).run state)) :
    result.1.1.refined.send_chain = (effectEntry effect).refined.send_chain ∧
    result.1.1.refined.control.send_sequence = (effectEntry effect).refined.control.send_sequence := by
  obtain ⟨qKdf, qOpen, run⟩ := RawCtxOwnerOracle.supported_execution impl state effect result supported
  suffices ∀ (entry : State × ReceiveEffect Context)
      (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × State) (qKdf qOpen : Nat),
      RawCtxOwnerOracle.SupportedExecution impl entry result qKdf qOpen → EffectGood entry.2 →
      result.1.1.refined.send_chain = (effectEntry entry.2).refined.send_chain ∧
      result.1.1.refined.control.send_sequence = (effectEntry entry.2).refined.control.send_sequence by
    exact this (state, effect) result qKdf qOpen run good
  intro entry result qKdf qOpen run good
  induction run with
  | rejected => exact ⟨rfl, rfl⟩
  | opened state pending reply nextState reached => exact finish_fields pending good reply
  | resume state pending response nextState result qKdf qOpen reached tail ih =>
      have preserved := ih (resume_good pending response)
      change result.1.1.refined.send_chain = (effectEntry (RawCtxOwnerOracle.resume pending response)).refined.send_chain ∧
        result.1.1.refined.control.send_sequence = (effectEntry (RawCtxOwnerOracle.resume pending response)).refined.control.send_sequence at preserved
      rw [RawCtxOwnerOracle.resume_entry] at preserved
      exact preserved

/-- Every supported original receive keeps the exact sender chain and sequence, with no assumptions on the callback's private state or responses. -/
theorem receive_fields
    (impl : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) (StateT State (OracleComp base)))
    (state : State) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × State)
    (supported : result ∈ support ((simulateQ impl (RawCtxOwnerOracle.receive entry target context)).run state)) :
    result.1.1.refined.send_chain = entry.refined.send_chain ∧
    result.1.1.refined.control.send_sequence = entry.refined.control.send_sequence := by
  have preserved := program_fields impl state (RawCtxOwnerOracle.begin entry target context)
    (begin_good entry target context) result supported
  rwa [RawCtxOwnerOracle.begin_entry] at preserved

end BeaconcryptCore.Computational.RawCtxReceiveSendFields

/-- info: 'BeaconcryptCore.Computational.RawCtxReceiveSendFields.resume_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveSendFields.resume_good

/-- info: 'BeaconcryptCore.Computational.RawCtxReceiveSendFields.begin_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveSendFields.begin_good

/-- info: 'BeaconcryptCore.Computational.RawCtxReceiveSendFields.finish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveSendFields.finish_fields

/-- info: 'BeaconcryptCore.Computational.RawCtxReceiveSendFields.program_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveSendFields.program_fields

/-- info: 'BeaconcryptCore.Computational.RawCtxReceiveSendFields.receive_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveSendFields.receive_fields
