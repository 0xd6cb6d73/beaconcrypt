import BeaconcryptCore.PanicFreedom.Restore

/-!
# Atomic material restoration

These exact equations apply to arbitrary chain and material types. Rejection returns the original builder, while a successful logical append to an empty physical slot publishes the supplied sequence and material together.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.refined

private theorem array_index_bang {α : Type} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (h : i.val < v.length) :
    v.index_usize i = ok v.val[i.val]! := by
  simpa only [getElem!_pos v.val i.val (by simpa using h)] using array_index_eq_ok v i h

/-- A successful logical append and an empty returned slot publish sequence and material together. -/
theorem refined_restore_receive_key_of_append {SendChain ReceiveChain Material : Type}
    (r : RefinedRatchetRestore SendChain ReceiveChain Material)
    (sequence : Std.U64) (material : Material) (step : ReceiveRestoreStep)
    (hstep : restore_receive_key_with_slot r.logical sequence = ok (core.option.Option.Some step))
    (hslot : step.slot.val < 50)
    (hempty : r.receive_slots.val[step.slot.val]! = core.option.Option.None) :
    refined_restore_receive_key r sequence material = ok (true,
      { r with
          logical := step.restore
          receive_slots := r.receive_slots.set (UScalar.cast UScalarTy.Usize step.slot)
            (core.option.Option.Some { sequence, material }) }) := by
  simp only [refined_restore_receive_key, hstep,
    lift, capacity_eq_ok, bind_tc_ok,
    if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize step.slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
    array_index_bang r.receive_slots (UScalar.cast UScalarTy.Usize step.slot) (by scalar_tac),
    show (UScalar.cast UScalarTy.Usize step.slot).val = step.slot.val by simp_scalar,
    hempty, core.option.Option.is_some, Std.core.option.Option.is_some, Option.isSome,
    core.option.Option.None, Bool.false_eq_true, if_false, Bool.false_or,
    massert, decide_eq_true (by scalar_tac : UScalar.cast UScalarTy.Usize step.slot < 50#usize), if_true]
  simp only [Array.index_mut_usize,
    array_index_bang r.receive_slots (UScalar.cast UScalarTy.Usize step.slot) (by scalar_tac),
    bind_tc_ok]
  dsimp! only
  rw [Array.set_getElem!_eq, array_update_eq_ok _ _ _ (by scalar_tac)]
  rfl

/-- Every rejected restoration step returns the complete input builder unchanged. -/
theorem refined_restore_receive_key_rejected {SendChain ReceiveChain Material : Type}
    (r next : RefinedRatchetRestore SendChain ReceiveChain Material)
    (sequence : Std.U64) (material : Material)
    (hrun : refined_restore_receive_key r sequence material = ok (false, next)) : next = r := by
  obtain ⟨step, hstep⟩ := restore_receive_key_with_slot_total r.logical sequence
  simp only [refined_restore_receive_key, hstep, bind_tc_ok] at hrun
  cases step with
  | none => simpa using hrun.symm
  | some step =>
    simp only [lift, capacity_eq_ok, bind_tc_ok] at hrun
    split_ifs at hrun with hcap
    · simpa using hrun.symm
    · simp only [array_index_bang r.receive_slots (UScalar.cast UScalarTy.Usize step.slot) (by scalar_tac),
        bind_tc_ok, core.option.Option.is_some, Std.core.option.Option.is_some,
        massert, decide_eq_true (by scalar_tac : UScalar.cast UScalarTy.Usize step.slot < 50#usize),
        Bool.or_true, if_true] at hrun
      cases hslot : r.receive_slots.val[(UScalar.cast UScalarTy.Usize step.slot).val]! with
      | none =>
        simp only [hslot, Option.isSome, Bool.false_eq_true, if_false] at hrun
        simp only [Array.index_mut_usize,
          array_index_bang r.receive_slots (UScalar.cast UScalarTy.Usize step.slot) (by scalar_tac),
          bind_tc_ok] at hrun
        dsimp! only at hrun
        rw [Array.set_getElem!_eq, array_update_eq_ok _ _ _ (by scalar_tac)] at hrun
        simp only [bind_tc_ok, RustM.ok.injEq, Prod.mk.injEq, Bool.true_eq_false, false_and] at hrun
      | some cached => simpa only [hslot, Option.isSome, if_true, RustM.ok.injEq,
          Prod.mk.injEq, true_and] using hrun.symm

/-- Logical restoration rejects exactly when a required order, counter, or capacity condition fails. -/
theorem restore_logical_rejects (r : RatchetRestore) (sequence : Std.U64)
    (hbad : ¬(0 < sequence.val ∧ sequence.val ≤ r.state.receive_sequence.val ∧
      r.last_sequence.val < sequence.val ∧ r.state.receive_cache.len.val < 50)) :
    restore_receive_key_with_slot r sequence = ok core.option.Option.None := by
  simp only [restore_receive_key_with_slot]
  split_ifs with hzero hahead hlast
  · rfl
  · rfl
  · rfl
  · have hfull : 50 ≤ r.state.receive_cache.len.val := by scalar_tac
    simp only [SequenceCache.append_eq_none_of_full _ sequence hfull, bind_tc_ok]

/-- A rejected logical restoration changes no material state. -/
theorem refined_restore_receive_key_logical_rejection {SendChain ReceiveChain Material : Type}
    (r : RefinedRatchetRestore SendChain ReceiveChain Material) (sequence : Std.U64) (material : Material)
    (hreject : restore_receive_key_with_slot r.logical sequence = ok core.option.Option.None) :
    refined_restore_receive_key r sequence material = ok (false, r) := by
  simp only [refined_restore_receive_key, hreject, bind_tc_ok]

end beaconcrypt_core.ratchet.refined
