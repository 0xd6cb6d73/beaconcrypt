import BeaconcryptCore.Refinement.RatchetEffect
import BeaconcryptCore.PanicFreedom.Bytes
import BeaconcryptCore.PanicFreedom.Control
import BeaconcryptCore.PanicFreedom.RatchetReceive

/-! Totality of the production ratchet effect API. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.refined

/-- Cached receive preparation validates arbitrary represented state before accessing either slot. -/
theorem prepare_cached_receive_total {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (sequence : Std.U64) :
    ∃ result, prepare_cached_receive state sequence = ok result := by
  obtain ⟨lookup, hlookup⟩ := control.lookup_receive_key_total state.control sequence
  cases lookup <;> simp only [prepare_cached_receive, hlookup, bind_tc_ok, lift, control.capacity_eq_ok]
  all_goals first | exact ⟨_, rfl⟩ | skip
  rename_i targetSlot
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨logical, hlogical⟩ := control.RatchetState.receive_key_at_total state.control targetSlot
    cases logical <;> simp only [hlogical, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64, bind_tc_ok, Bool.false_eq_true, if_false]
    all_goals first | exact ⟨_, rfl⟩ | skip
    simp only [control.array_index_eq_ok state.receive_slots (UScalar.cast UScalarTy.Usize targetSlot)
      (by scalar_tac), core.option.Option.as_ref, bind_tc_ok, control.RatchetState.receive_cache_len]
    (repeat' first | exact ⟨_, rfl⟩ | split) <;> simp_all only [bind_tc_ok, ite_self, RustM.ok.injEq, exists_eq']
    obtain ⟨lastSlot, hlastSlot, _⟩ := control.uscalar_sub_eq_ok state.control.receive_cache.len 1#u8 (by scalar_tac)
    simp only [hlastSlot, bind_tc_ok]
    repeat' first | exact ⟨_, rfl⟩ | split
    obtain ⟨lastLogical, hlastLogical⟩ := control.RatchetState.receive_key_at_total state.control lastSlot
    obtain ⟨finished, hfinished⟩ := control.finish_receive_with_removal_ok state.control sequence targetSlot true
    simp only [hlastLogical, hfinished, bind_tc_ok,
      control.array_index_eq_ok state.receive_slots (UScalar.cast UScalarTy.Usize lastSlot) (by scalar_tac)]
    (repeat' first | exact ⟨_, rfl⟩ | split) <;> simp_all only [bind_tc_ok]
    all_goals split <;> exact ⟨_, rfl⟩

end beaconcrypt_core.ratchet.refined

namespace beaconcrypt_core.ratchet.concrete

theorem begin_send_total {Context : Type}
    (kernel : ConcreteRatchetKernel) (context : Context) :
    ∃ result, begin_send kernel context = ok result := by
  by_cases hmax : kernel.refined.control.send_sequence = core.num.U64.MAX
  · exact ⟨_, begin_send_exhausted_restores_entry kernel context hmax⟩
  · obtain ⟨pending, hbegin, _⟩ := begin_send_nonexhausted_exact kernel context hmax
    exact ⟨_, hbegin⟩

theorem ReceiveOpen.sequence_total {Context : Type} (pending : ReceiveOpen Context) :
    ∃ result, pending.sequence = ok result := by
  cases hprepared : pending.prepared <;> simp [ReceiveOpen.sequence, hprepared]

theorem ReceiveOpen.material_total {Context : Type} (pending : ReceiveOpen Context) :
    ∃ result, pending.material = ok result := by
  cases hprepared : pending.prepared <;>
    simp only [ReceiveOpen.material, hprepared, lift, control.capacity_eq_ok, bind_tc_ok]
  case PreparedReceiveCachedCase prepared =>
    split
    · exact ⟨_, rfl⟩
    · rw [control.array_index_eq_ok _ _ (by scalar_tac)]
      simp only [bind_tc_ok, core.option.Option.as_ref]
      split <;> simp_all only [bind_tc_ok]
      all_goals first | exact ⟨_, rfl⟩ | split <;> exact ⟨_, rfl⟩
  case PreparedReceiveFutureCase future =>
    exact ⟨_, rfl⟩

theorem SendKdf.resume_total {Context : Type} (pending : SendKdf Context)
    (response : RatchetKdfResponse) : ∃ result, pending.resume response = ok result := by
  obtain ⟨stepped, hstep⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
  exact ⟨_, SendKdf.resume_exact pending response stepped hstep⟩

theorem SendSeal.finish_total {Context Output : Type} (pending : SendSeal Context)
    (sealed : core.option.Option Output) :
    ∃ result, pending.finish sealed = ok result :=
  ⟨_, SendSeal.finish_returns_interpreter_result pending sealed⟩

/-- Receive admission returns normally for arbitrary persisted counters, slots, and targets. -/
theorem begin_receive_total {Context : Type} (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    ∃ result, begin_receive kernel target context = ok result := by
  obtain ⟨plan, hplan⟩ := control.plan_receive_until_total kernel.refined.control target
  cases hseq : plan.sequence <;> simp only [begin_receive, hplan, bind_tc_ok, hseq, receive_rejected]
  all_goals first | exact ⟨_, rfl⟩ | skip
  rename_i sequence
  split
  · obtain ⟨prepared, hprepared⟩ := refined.prepare_cached_receive_total kernel.refined sequence
    cases prepared <;> simp [hprepared]
  · obtain ⟨skipped, hskipped, _⟩ := control.uscalar_sub_eq_ok plan.derivations 1#u64 (by scalar_tac)
    obtain ⟨empty, hempty⟩ := refined.refined_receive_slots_are_empty_ok kernel.refined
      kernel.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped)
    cases empty <;> by_cases hgap : skipped > control.RATCHET_MAX_GAP <;>
      simp only [hskipped, lift, control.RatchetState.receive_cache_len, hempty, hgap,
        RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, refined.empty_material_slots,
        bind_tc_ok, Bool.false_eq_true, if_false, if_true, RustM.ok.injEq, exists_eq']

/-- Receive completion always returns normally, including interpreter rejection and malformed prepared states. -/
theorem ReceiveOpen.finish_total {Context Plaintext : Type} (pending : ReceiveOpen Context)
    (opened : core.option.Option Plaintext) :
    ∃ result, pending.finish opened = ok result :=
  match opened with
  | .None => ⟨_, rfl⟩
  | .Some plaintext =>
    match hprepared : pending.prepared with
    | .PreparedReceiveCachedCase prepared =>
      (refined.publish_cached_receive_ok pending.entry.refined prepared).elim fun _ hpublished =>
        by simp [ReceiveOpen.finish, hprepared, hpublished]
    | .PreparedReceiveFutureCase prepared =>
      (refined.publish_future_receive_ok pending.entry.refined prepared).elim fun _ hpublished =>
        by simp [ReceiveOpen.finish, hprepared, hpublished]

/-- Every KDF resumption is total for arbitrary response bytes and represented pending state. -/
theorem ReceiveKdf.resume_total {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) :
    ∃ result, pending.resume response = ok result := by
  by_cases hzero : pending.remaining = 0#u8
  · simp [ReceiveKdf.resume, hzero, receive_rejected]
  · simp only [ReceiveKdf.resume, hzero, if_false]
    split
    · obtain ⟨advanced, hadvanced⟩ := control.advance_receive_target_total pending.working_control
      cases hseq : advanced.sequence <;> simp only [hadvanced, hseq, bind_tc_ok, receive_rejected]
      all_goals first | exact ⟨_, rfl⟩ | skip
      rename_i sequence
      obtain ⟨stepped, hstepped⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
      obtain ⟨valid, hvalid⟩ := refined.pending_receive_is_valid_ok pending.entry.refined
        { committed_control := advanced.state, final_receive_chain := stepped.chain,
          staged_slots := pending.staged_slots, target_sequence := sequence,
          target_material := stepped.material, first_slot := pending.first_slot, skipped := pending.skipped }
        pending.target
      simp only [hstepped, hvalid, bind_tc_ok]
      repeat' first | exact ⟨_, rfl⟩ | split
    · obtain ⟨advanced, hadvanced⟩ := control.advance_receive_ok pending.working_control
      cases hseq : advanced.sequence <;> cases hslot : advanced.slot <;>
        simp only [hadvanced, hseq, hslot, lift, bind_tc_ok, receive_rejected]
      all_goals first | exact ⟨_, rfl⟩ | skip
      rename_i sequence slot
      obtain ⟨logical, hlogical⟩ := control.RatchetState.receive_key_at_total advanced.state slot
      obtain ⟨nextSlot, hnextSlot, hnextSlotVal⟩ := control.uscalar_add_eq_ok
        (UScalar.cast UScalarTy.Usize pending.first_slot) (UScalar.cast UScalarTy.Usize pending.skipped)
        (by scalar_tac)
      cases logical <;> simp only [hlogical, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.U64.Insts.CoreCmpPartialEqU64, control.capacity_eq_ok, hnextSlot, bind_tc_ok,
        Bool.false_eq_true, if_false]
      all_goals first | exact ⟨_, rfl⟩ | skip
      repeat' first | exact ⟨_, rfl⟩ | split
      all_goals simp only [control.array_index_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
        (by scalar_tac), core.option.Option.is_some, bind_tc_ok, ite_self, RustM.ok.injEq, exists_eq']
      obtain ⟨skipped, hskipped, _⟩ := control.uscalar_add_eq_ok pending.skipped 1#u8 (by scalar_tac)
      obtain ⟨remaining, hremaining, _⟩ := control.uscalar_sub_eq_ok pending.remaining 1#u8 (by scalar_tac)
      obtain ⟨stepped, hstepped⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
      simp only [hstepped, hskipped, hremaining, RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
        control.array_update_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
          (.Some ⟨sequence, stepped.material⟩) (by scalar_tac), bind_tc_ok]
      split <;> exact ⟨_, rfl⟩

end beaconcrypt_core.ratchet.concrete
