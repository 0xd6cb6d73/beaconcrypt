import BeaconcryptCore.Refinement.RatchetCachedPreparation
import BeaconcryptCore.Refinement.RatchetReceiveRollback
import BeaconcryptCore.Refinement.RatchetPlannerSurface

/-! Raw cached admission and completion corollaries for arbitrary represented state. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core

set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.refined

/-- A stale target material tag causes cached preparation to reject. -/
theorem prepare_cached_receive_mismatched_target {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (sequence : Std.U64)
    (slot : Std.U8) (cached : CachedReceiveKey Material)
    (hlookup : control.lookup_receive_key state.control sequence = ok (core.option.Option.Some slot))
    (hslot : state.receive_slots.val[slot.val]! = core.option.Option.Some cached)
    (hmismatch : cached.sequence ≠ sequence) :
    prepare_cached_receive state sequence = ok core.option.Option.None := by
  obtain ⟨result, hresult⟩ := prepare_cached_receive_total state sequence
  cases result with
  | none => exact hresult
  | some prepared =>
    have h := prepare_cached_receive_success_inv state sequence prepared hresult
    have hslotEq : prepared.target_slot = slot := by simpa using RustM.ok.inj (h.lookup.symm.trans hlookup)
    obtain ⟨material, hmaterial⟩ := h.target_material
    have hrecord : cached = (⟨sequence, material⟩ : CachedReceiveKey Material) := by
      simpa only [hslotEq, hslot, core.option.Option.Some, Option.some.injEq] using hmaterial
    exact False.elim (hmismatch (congrArg CachedReceiveKey.sequence hrecord))

/-- A stale old-last tag prevents cached preparation from publishing logical removal. -/
theorem prepare_cached_receive_mismatched_last {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (sequence lastSequence : Std.U64)
    (targetSlot lastSlot : Std.U8) (lastCached : CachedReceiveKey Material)
    (finished : control.ReceiveFinishWithRemoval)
    (hlookup : control.lookup_receive_key state.control sequence = ok (core.option.Option.Some targetSlot))
    (hfinish : control.finish_receive_with_removal state.control sequence targetSlot true = ok finished)
    (hremoval : finished.removal = core.option.Option.Some { target_slot := targetSlot, last_slot := lastSlot })
    (hkey : control.RatchetState.receive_key_at state.control lastSlot = ok (core.option.Option.Some lastSequence))
    (hslot : state.receive_slots.val[lastSlot.val]! = core.option.Option.Some lastCached)
    (hmismatch : lastCached.sequence ≠ lastSequence) :
    prepare_cached_receive state sequence = ok core.option.Option.None := by
  obtain ⟨result, hresult⟩ := prepare_cached_receive_total state sequence
  cases result with
  | none => exact hresult
  | some prepared =>
    have h := prepare_cached_receive_success_inv state sequence prepared hresult
    have htargetEq : prepared.target_slot = targetSlot := by simpa using RustM.ok.inj (h.lookup.symm.trans hlookup)
    have hfinished := h.finish
    rw [htargetEq, hfinish] at hfinished
    have hlastEq : lastSlot = prepared.last_slot := by
      simpa only [hremoval, core.option.Option.Some, Option.some.injEq, control.ReceiveRemoval.mk.injEq, true_and] using
        congrArg control.ReceiveFinishWithRemoval.removal (RustM.ok.inj hfinished)
    obtain ⟨validated, hvalidated, hvalidatedKey⟩ := h.last_material
    have hrecord : lastCached = validated := by
      simpa only [← hlastEq, hslot, core.option.Option.Some, Option.some.injEq] using hvalidated
    have hsequence : lastSequence = lastCached.sequence := by
      simpa only [← hlastEq, hkey, ← hrecord, RustM.ok.injEq, core.option.Option.Some, Option.some.injEq] using hvalidatedKey
    exact False.elim (hmismatch hsequence.symm)

end beaconcrypt_core.ratchet.refined

namespace beaconcrypt_core.ratchet.control

/-- Detailed successful removal preserves every other surviving physical logical slot. -/
theorem finish_receive_with_removal_preserves_other_physical_slot
    (state : RatchetState) (sequence : Std.U64) (slot : Std.U8)
    (hvalid : ValidControl state) (hlive : slot.val < state.receive_cache.len.val)
    (hentry : state.receive_cache.entries.val[slot.val]! = sequence) :
    ∃ result, finish_receive_with_removal state sequence slot true = ok result ∧
      ∀ i, i < result.state.receive_cache.len.val → i ≠ slot.val →
        result.state.receive_cache.entries.val[i]! = state.receive_cache.entries.val[i]! := by
  obtain ⟨result, hresult, _, _, _, _, _, hentries⟩ := finish_receive_consumed state sequence slot hvalid.capacity hlive hentry
  exact ⟨result, hresult, fun i hi hne => by simpa only [if_neg hne] using hentries i hi⟩

end beaconcrypt_core.ratchet.control

namespace beaconcrypt_core.ratchet.concrete

/-- A returned cached phase came from the exact requested zero-cost plan and cached helper result. -/
theorem begin_receive_cached_result_shape {Context : Type}
    (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (opened : ReceiveOpen Context) (prepared : ratchet.refined.PreparedCachedReceive)
    (hbegin : begin_receive kernel target context = ok (.ReceiveOpenRequested opened))
    (hphase : opened.prepared = .PreparedReceiveCachedCase prepared) :
    control.plan_receive_until kernel.refined.control target = ok { sequence := core.option.Option.Some target, derivations := 0#u64 } ∧
      ratchet.refined.prepare_cached_receive kernel.refined target = ok (core.option.Option.Some prepared) ∧
      opened.entry = kernel ∧ opened.context = context := by
  obtain ⟨plan, hplan, _, hshape⟩ := control.plan_receive_shape kernel.refined.control target
  cases hseq : plan.sequence <;> simp only [begin_receive, hplan, hseq, bind_tc_ok, receive_rejected, RustM.ok.injEq, reduceCtorEq] at hbegin
  rename_i planned
  simp only [hseq] at hshape
  obtain ⟨rfl, _, _⟩ := hshape
  split at hbegin
  · rename_i hzero
    obtain ⟨result, hresult⟩ := refined.prepare_cached_receive_total kernel.refined planned
    cases result <;> simp only [hresult, bind_tc_ok, RustM.ok.injEq, reduceCtorEq] at hbegin
    rename_i result
    have hopen : (⟨kernel, context, .PreparedReceiveCachedCase result⟩ : ReceiveOpen Context) = opened := by simpa using hbegin
    subst opened
    have hpreparedEq : result = prepared := by simpa using hphase
    refine ⟨?_, by simpa only [hpreparedEq] using hresult, rfl, rfl⟩
    have hplanEq : plan = { sequence := core.option.Option.Some planned, derivations := 0#u64 } := by
      cases plan
      simp_all
    exact hplan.trans (congrArg RustM.ok hplanEq)
  · obtain ⟨skipped, hskipped, _⟩ := control.uscalar_sub_eq_ok plan.derivations 1#u64 (by scalar_tac)
    obtain ⟨empty, hempty⟩ := refined.refined_receive_slots_are_empty_ok kernel.refined
      kernel.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped)
    cases empty <;> by_cases hgap : skipped > control.RATCHET_MAX_GAP <;>
      simp only [hskipped, lift, control.RatchetState.receive_cache_len, hempty, hgap,
        RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, refined.empty_material_slots,
        bind_tc_ok, Bool.false_eq_true, if_false, if_true, RustM.ok.injEq, reduceCtorEq] at hbegin

/-- A cached helper rejection returns the original complete entry through the synchronous driver. -/
theorem receiveNext_cached_rejected {Context Output : Type}
    (execute : KdfInterpreter) (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hplan : control.plan_receive_until kernel.refined.control target = ok { sequence := core.option.Option.Some target, derivations := 0#u64 })
    (hprepare : refined.prepare_cached_receive kernel.refined target = ok core.option.Option.None) :
    begin_receive kernel target context = ok (.ReceiveRejected kernel context) ∧
      receiveNext execute kernel target context openReply = ok (kernel, core.option.Option.None) := by
  have hbegin : begin_receive kernel target context = ok (.ReceiveRejected kernel context) := by
    simp only [begin_receive, hplan, hprepare, bind_tc_ok, if_true, receive_rejected]
  exact ⟨hbegin, (show ReceiveRun execute openReply kernel target context kernel core.option.Option.None from
    ⟨_, hbegin, .rejected kernel context⟩).driver_eq⟩

/-- Rejected admission is independent of every KDF interpreter and open callback. -/
theorem receiveNext_rejected_admission {Context Output : Type}
    (execute : KdfInterpreter) (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output) (derivations : Std.U64)
    (hplan : control.plan_receive_until kernel.refined.control target = ok { sequence := core.option.Option.None, derivations := derivations }) :
    begin_receive kernel target context = ok (.ReceiveRejected kernel context) ∧
      receiveNext execute kernel target context openReply = ok (kernel, core.option.Option.None) := by
  have hbegin := begin_receive_rejected_plan_restores_entry kernel target context derivations hplan
  exact ⟨hbegin, (show ReceiveRun execute openReply kernel target context kernel core.option.Option.None from
    ⟨_, hbegin, .rejected kernel context⟩).driver_eq⟩

/-- A valid cached phase publishes precisely its prepared removal on any successful callback result. -/
theorem ReceiveOpen.finish_cached_publication {Context Output : Type}
    (opened : ReceiveOpen Context) (sequence : Std.U64) (prepared : refined.PreparedCachedReceive)
    (hphase : opened.prepared = .PreparedReceiveCachedCase prepared)
    (h : refined.CachedPreparationFacts opened.entry.refined sequence prepared) (plaintext : Output) :
    ∃ published, refined.publish_cached_receive opened.entry.refined prepared = ok published ∧
      opened.finish (core.option.Option.Some plaintext) = ok ({ refined := published }, core.option.Option.Some plaintext) := by
  obtain ⟨published, hpublish, _, _, _, _⟩ := refined.publish_cached_receive_exact opened.entry.refined prepared h.target_bound h.last_bound
  exact ⟨published, hpublish, by simp only [ReceiveOpen.finish, hphase, hpublish, bind_tc_ok]⟩

end beaconcrypt_core.ratchet.concrete
