import BeaconcryptCore.Refinement.RatchetReceiveDriver
import BeaconcryptCore.PanicFreedom.Effects

/-! Exact entry ownership, decreasing continuations, and rollback for arbitrary represented receive states. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- Every phase retains its operation's original kernel. -/
def effectEntry {Context : Type} : ReceiveEffect Context → ConcreteRatchetKernel
  | .ReceiveRejected entry _ => entry
  | .ReceiveKdfRequested pending => pending.entry
  | .ReceiveOpenRequested pending => pending.entry

/-- Each resumption keeps ownership and either terminates or strictly decreases the continuation count. -/
def ResumeProgress {Context : Type} (pending : ReceiveKdf Context) (effect : ReceiveEffect Context) : Prop :=
  effectEntry effect = pending.entry ∧ match effect with
    | .ReceiveKdfRequested next => next.remaining.val < pending.remaining.val
    | _ => True

theorem begin_receive_entry_exact {Context : Type} (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    ∃ result, begin_receive kernel target context = ok result ∧ effectEntry result = kernel := by
  obtain ⟨plan, hplan⟩ := control.plan_receive_until_total kernel.refined.control target
  cases hseq : plan.sequence <;> simp only [begin_receive, hplan, bind_tc_ok, hseq, receive_rejected]
  all_goals first | exact ⟨_, rfl, rfl⟩ | skip
  rename_i sequence
  split
  · obtain ⟨prepared, hprepared⟩ := refined.prepare_cached_receive_total kernel.refined sequence
    cases prepared <;> simp [hprepared, effectEntry]
  · obtain ⟨skipped, hskipped, _⟩ := control.uscalar_sub_eq_ok plan.derivations 1#u64 (by scalar_tac)
    obtain ⟨empty, hempty⟩ := refined.refined_receive_slots_are_empty_ok kernel.refined
      kernel.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped)
    cases empty <;> by_cases hgap : skipped > control.RATCHET_MAX_GAP <;>
      simp only [hskipped, lift, control.RatchetState.receive_cache_len, hempty, hgap,
        RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, refined.empty_material_slots,
        bind_tc_ok, Bool.false_eq_true, if_false, if_true, RustM.ok.injEq, effectEntry]
    all_goals exact ⟨_, rfl, rfl⟩


theorem ReceiveKdf.resume_progress {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) :
    ∃ result, pending.resume response = ok result ∧ ResumeProgress pending result := by
  by_cases hzero : pending.remaining = 0#u8
  · simp [ReceiveKdf.resume, hzero, receive_rejected, ResumeProgress, effectEntry]
  · simp only [ReceiveKdf.resume, hzero, if_false]
    split
    · obtain ⟨advanced, hadvanced⟩ := control.advance_receive_target_total pending.working_control
      cases hseq : advanced.sequence <;> simp only [hadvanced, hseq, bind_tc_ok, receive_rejected]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      rename_i sequence
      obtain ⟨stepped, hstepped⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
      obtain ⟨valid, hvalid⟩ := refined.pending_receive_is_valid_ok pending.entry.refined
        { committed_control := advanced.state, final_receive_chain := stepped.chain,
          staged_slots := pending.staged_slots, target_sequence := sequence,
          target_material := stepped.material, first_slot := pending.first_slot, skipped := pending.skipped }
        pending.target
      simp only [hstepped, hvalid, bind_tc_ok]
      repeat' first | exact ⟨_, rfl, rfl, True.intro⟩ | split
    · obtain ⟨advanced, hadvanced⟩ := control.advance_receive_ok pending.working_control
      cases hseq : advanced.sequence <;> cases hslot : advanced.slot <;>
        simp only [hadvanced, hseq, hslot, lift, bind_tc_ok, receive_rejected]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      rename_i sequence slot
      obtain ⟨logical, hlogical⟩ := control.RatchetState.receive_key_at_total advanced.state slot
      obtain ⟨nextSlot, hnextSlot, hnextSlotVal⟩ := control.uscalar_add_eq_ok
        (UScalar.cast UScalarTy.Usize pending.first_slot) (UScalar.cast UScalarTy.Usize pending.skipped)
        (by scalar_tac)
      cases logical <;> simp only [hlogical, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.U64.Insts.CoreCmpPartialEqU64, control.capacity_eq_ok, hnextSlot, bind_tc_ok,
        Bool.false_eq_true, if_false]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      repeat' first | exact ⟨_, rfl, rfl, True.intro⟩ | split
      all_goals simp only [control.array_index_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
        (by scalar_tac), core.option.Option.is_some, bind_tc_ok, ite_self, RustM.ok.injEq, ResumeProgress, effectEntry]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      obtain ⟨skipped, hskipped, _⟩ := control.uscalar_add_eq_ok pending.skipped 1#u8 (by scalar_tac)
      obtain ⟨remaining, hremaining, hremainingval⟩ := control.uscalar_sub_eq_ok pending.remaining 1#u8 (by scalar_tac)
      obtain ⟨stepped, hstepped⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
      simp only [hstepped, hskipped, hremaining, RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
        control.array_update_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
          (.Some ⟨sequence, stepped.material⟩) (by scalar_tac), bind_tc_ok]
      split <;> refine ⟨_, rfl, rfl, ?_⟩
      all_goals first | exact True.intro | (dsimp; scalar_tac)

/-- Finish always returns the supplied optional result unchanged. -/
theorem ReceiveOpen.finish_result_exact {Context Output : Type} (pending : ReceiveOpen Context)
    (opened : core.option.Option Output) :
    ∃ result, pending.finish opened = ok (result, opened) := by
  cases opened with
  | none => exact ⟨pending.entry, rfl⟩
  | some plaintext =>
      cases hprepared : pending.prepared with
      | PreparedReceiveCachedCase prepared =>
          obtain ⟨published, hpublish⟩ := refined.publish_cached_receive_ok pending.entry.refined prepared
          exact ⟨{ refined := published }, by simp only [ReceiveOpen.finish, hprepared, hpublish, bind_tc_ok]⟩
      | PreparedReceiveFutureCase prepared =>
          obtain ⟨published, hpublish⟩ := refined.publish_future_receive_ok pending.entry.refined prepared
          exact ⟨{ refined := published }, by simp only [ReceiveOpen.finish, hprepared, hpublish, bind_tc_ok]⟩

/-- Every represented failed execution returns its original entry, with no state-validity or cryptographic premise. -/
theorem ReceiveExecution.failure_entry {Context Output : Type} {execute : KdfInterpreter}
    {openReply : ReceiveOpen Context → core.option.Option Output} {effect : ReceiveEffect Context}
    {result : ConcreteRatchetKernel} {output : core.option.Option Output}
    (run : ReceiveExecution execute openReply effect result output) (hfailure : output = .None) :
    result = effectEntry effect := by
  induction run with
  | rejected => rfl
  | opened pending result output hfinish =>
      obtain ⟨next, hnext⟩ := pending.finish_result_exact (openReply pending)
      have hpair := Prod.mk.inj (RustM.ok.inj (hnext.symm.trans hfinish))
      have hreply : openReply pending = .None := hpair.2.trans hfailure
      rw [hreply, ReceiveOpen.finish] at hfinish
      exact (Prod.mk.inj (RustM.ok.inj hfinish)).1.symm
  | resume pending next result output hresume tail ih =>
      obtain ⟨next', hnext, hprogress⟩ := pending.resume_progress (execute pending.request)
      have heq : next' = next := RustM.ok.inj (hnext.symm.trans hresume)
      exact (ih hfailure).trans (heq ▸ hprogress.1)

/-- Only KDF phases require another iteration, with a strictly decreasing finite counter. -/
def effectDepth {Context : Type} : ReceiveEffect Context → Nat
  | .ReceiveKdfRequested pending => pending.remaining.val + 1
  | _ => 0

/-- Every represented phase has a complete execution, including malformed pending states. -/
theorem receiveExecution_exists {Context Output : Type} (execute : KdfInterpreter)
    (openReply : ReceiveOpen Context → core.option.Option Output) (effect : ReceiveEffect Context) :
    ∃ result output, ReceiveExecution execute openReply effect result output := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | ReceiveRejected entry context => exact ⟨entry, .None, .rejected entry context⟩
      | ReceiveOpenRequested pending =>
          obtain ⟨result, hfinish⟩ := pending.finish_result_exact (openReply pending)
          exact ⟨result, openReply pending, .opened pending result _ hfinish⟩
      | ReceiveKdfRequested pending =>
          obtain ⟨next, hresume, hprogress⟩ := pending.resume_progress (execute pending.request)
          have hlt : effectDepth next < depth := by
            cases next with
            | ReceiveRejected => simp only [effectDepth] at hdepth ⊢; omega
            | ReceiveOpenRequested => simp only [effectDepth] at hdepth ⊢; omega
            | ReceiveKdfRequested later =>
                have hremaining := hprogress.2
                simp only [effectDepth] at hdepth ⊢
                change later.remaining.val < pending.remaining.val at hremaining
                omega
          obtain ⟨result, output, tail⟩ := ih (effectDepth next) hlt next rfl
          exact ⟨result, output, .resume pending next result output hresume tail⟩

/-- Every complete receive operation terminates for arbitrary represented input, not just canonical kernels. -/
theorem receiveRun_exists {Context Output : Type} (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output) :
    ∃ result output, ReceiveRun execute openReply entry target context result output := by
  obtain ⟨started, hbegin, _⟩ := begin_receive_entry_exact entry target context
  obtain ⟨result, output, run⟩ := receiveExecution_exists execute openReply started
  exact ⟨result, output, started, hbegin, run⟩

/-- The composed unbounded receive driver is panic-free on arbitrary represented inputs. -/
theorem receiveNext_total {Context Output : Type} (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output) :
    ∃ result output, receiveNext execute entry target context openReply = ok (result, output) := by
  obtain ⟨result, output, run⟩ := receiveRun_exists execute entry target context openReply
  exact ⟨result, output, run.driver_eq⟩

/-- Any failed complete run is exactly entry-neutral, even for malformed states and arbitrary callbacks. -/
theorem ReceiveRun.failure_entry {Context Output : Type} {execute : KdfInterpreter}
    {entry result : ConcreteRatchetKernel} {target : Std.U64} {context : Context}
    {openReply : ReceiveOpen Context → core.option.Option Output}
    (run : ReceiveRun execute openReply entry target context result .None) : result = entry := by
  obtain ⟨started, hbegin, execution⟩ := run
  obtain ⟨other, hother, hentry⟩ := begin_receive_entry_exact entry target context
  have heq : other = started := RustM.ok.inj (hother.symm.trans hbegin)
  exact (execution.failure_entry rfl).trans (heq ▸ hentry)

/-- The actual synchronous driver returns the original kernel whenever it returns no plaintext. -/
theorem receiveNext_failure_entry {Context Output : Type} (execute : KdfInterpreter)
    (entry result : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hfailure : receiveNext execute entry target context openReply = ok (result, .None)) :
    result = entry := by
  obtain ⟨next, output, run⟩ := receiveRun_exists execute entry target context openReply
  have hpair := Prod.mk.inj (RustM.ok.inj (run.driver_eq.symm.trans hfailure))
  have hrun : ReceiveRun execute openReply entry target context result .None := by
    simpa only [hpair.1, hpair.2] using run
  exact hrun.failure_entry

/-- Repeat a complete receive operation a finite number of times, retaining each actual returned state. -/
def repeatedReceiveState {Context Output : Type} (execute : KdfInterpreter)
    (target : Std.U64) (context : Context) (openReply : ReceiveOpen Context → core.option.Option Output) :
    Nat → ConcreteRatchetKernel → RustM ConcreteRatchetKernel
  | 0, entry => ok entry
  | count + 1, entry => do
      let (next, _) ← receiveNext execute entry target context openReply
      repeatedReceiveState execute target context openReply count next

/-- Any finite number of identical rejected attempts preserves the exact entry state. -/
theorem repeated_rejection_preserves_entry {Context Output : Type} (execute : KdfInterpreter)
    (entry result : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hfailure : receiveNext execute entry target context openReply = ok (result, .None))
    (count : Nat) : repeatedReceiveState execute target context openReply count entry = ok entry := by
  have heq := receiveNext_failure_entry execute entry result target context openReply hfailure
  rw [heq] at hfailure
  induction count with
  | zero => rfl
  | succ count ih => simpa! only [repeatedReceiveState, hfailure, bind_tc_ok] using ih

/-- Retrying after any finite rejected prefix gives exactly the same state and plaintext as direct retry, even with a different interpreter, target, context type, and result type. -/
theorem retry_after_rejection_eq_direct {Context Output RetryContext RetryOutput : Type}
    (execute retryExecute : KdfInterpreter) (entry result : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) (openReply : ReceiveOpen Context → core.option.Option Output)
    (hfailure : receiveNext execute entry target context openReply = ok (result, .None))
    (count : Nat) (retryTarget : Std.U64) (retryContext : RetryContext)
    (retryReply : ReceiveOpen RetryContext → core.option.Option RetryOutput) :
    (do let restart ← repeatedReceiveState execute target context openReply count entry
        receiveNext retryExecute restart retryTarget retryContext retryReply) =
      receiveNext retryExecute entry retryTarget retryContext retryReply := by
  rw [repeated_rejection_preserves_entry execute entry result target context openReply hfailure count]
  rfl

/-- Failed authentication preserves every capacity-bearing field and material slot exactly. -/
theorem receiveNext_failure_preserves_capacity {Context Output : Type} (execute : KdfInterpreter)
    (entry result : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hfailure : receiveNext execute entry target context openReply = ok (result, .None)) :
    result.refined.control.receive_cache = entry.refined.control.receive_cache ∧
      result.refined.receive_slots = entry.refined.receive_slots := by
  rw [receiveNext_failure_entry execute entry result target context openReply hfailure]
  exact ⟨rfl, rfl⟩

end beaconcrypt_core.ratchet.concrete
