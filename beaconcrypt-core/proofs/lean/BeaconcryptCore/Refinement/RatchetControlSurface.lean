import BeaconcryptCore.Refinement.RatchetStructural
import BeaconcryptCore.Refinement.RatchetReceiveCompatibility

/-! Exact low-level control contracts completing the historical receive surface. These statements use only structural cache validity and include arbitrary malformed inputs for neutral outcomes. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.control

/-- A raw result that does not consume a capability preserves the complete state and has no removal descriptor, even for malformed caches. -/
theorem finish_receive_with_removal_neutral
    (state : RatchetState) (target : Std.U64) (slot : Std.U8) (authenticated : Bool)
    (result : ReceiveFinishWithRemoval)
    (hrun : finish_receive_with_removal state target slot authenticated = ok result)
    (hneutral : result.disposition ≠ ReceiveDisposition.Consumed) :
    result.removal = core.option.Option.None ∧ result.state = state := by
  by_cases hcap : 50 < state.receive_cache.len.val
  · have heq := RustM.ok.inj (hrun.symm.trans (finish_receive_with_removal_over_capacity state target slot authenticated hcap))
    simp only [heq, and_self]
  · by_cases hslot : slot.val < state.receive_cache.len.val
    · by_cases hentry : state.receive_cache.entries.val[slot.val]! = target
      · cases authenticated with
        | false =>
            have heq := RustM.ok.inj (hrun.symm.trans (finish_receive_with_removal_retained state target slot (Nat.le_of_not_gt hcap) hslot hentry))
            simp only [heq, and_self]
        | true =>
            obtain ⟨finished, hfinish, hconsumed, _⟩ := finish_receive_consumed state target slot (by exact Nat.le_of_not_gt hcap) hslot hentry
            exact False.elim (hneutral ((congrArg ReceiveFinishWithRemoval.disposition (RustM.ok.inj (hrun.symm.trans hfinish))).trans hconsumed))
      · have heq := RustM.ok.inj (hrun.symm.trans (finish_receive_with_removal_mismatch state target slot authenticated (Nat.le_of_not_gt hcap) hslot hentry))
        simp only [heq, and_self]
    · have heq := RustM.ok.inj (hrun.symm.trans (finish_receive_with_removal_out_of_range state target slot authenticated (Nat.le_of_not_gt hslot)))
      simp only [heq, and_self]

/-- Every raw missing result is neutral and has no removal descriptor. -/
theorem finish_receive_with_removal_missing_result_is_neutral
    (state : RatchetState) (target : Std.U64) (slot : Std.U8) (authenticated : Bool)
    (result : ReceiveFinishWithRemoval)
    (hrun : finish_receive_with_removal state target slot authenticated = ok result)
    (hmissing : result.disposition = ReceiveDisposition.Missing) :
    result.removal = core.option.Option.None ∧ result.state = state := by
  exact finish_receive_with_removal_neutral state target slot authenticated result hrun (by simp only [hmissing, ne_eq, reduceCtorEq, not_false_eq_true])

/-- Every raw retained result is neutral and has no removal descriptor. -/
theorem finish_receive_with_removal_retained_result_is_neutral
    (state : RatchetState) (target : Std.U64) (slot : Std.U8) (authenticated : Bool)
    (result : ReceiveFinishWithRemoval)
    (hrun : finish_receive_with_removal state target slot authenticated = ok result)
    (hretained : result.disposition = ReceiveDisposition.Retained) :
    result.removal = core.option.Option.None ∧ result.state = state := by
  exact finish_receive_with_removal_neutral state target slot authenticated result hrun (by simp only [hretained, ne_eq, reduceCtorEq, not_false_eq_true])

/-- The compatibility wrapper is precisely the state and disposition projection for every raw result. -/
theorem finish_receive_wrapper_matches_detailed
    (state : RatchetState) (target : Std.U64) (slot : Std.U8) (authenticated : Bool)
    (result : ReceiveFinishWithRemoval)
    (hrun : finish_receive_with_removal state target slot authenticated = ok result) :
    finish_receive state target slot authenticated = ok { state := result.state, disposition := result.disposition } := by
  simp only [finish_receive, hrun, bind_tc_ok]

/-- A live physical slot exposes its exact logical tag without any global cache invariant. -/
theorem receive_key_at_matches_cache_slot
    (state : RatchetState) (target : Std.U64) (slot : Std.U8)
    (hlive : slot.val < state.receive_cache.len.val) (hbound : slot.val < 50)
    (hentry : state.receive_cache.entries.val[slot.val]! = target) :
    RatchetState.receive_key_at state slot = ok (core.option.Option.Some target) := by
  exact concrete.receive_key_at_some state slot target hlive hbound hentry

/-- A consumed detailed result removes exactly the target from the logical cache and preserves structural validity. -/
theorem ValidControl.finish_receive_exact
    {state : RatchetState} (h : ValidControl state) (target : Std.U64) (slot : Std.U8)
    (hlive : slot.val < state.receive_cache.len.val)
    (hentry : state.receive_cache.entries.val[slot.val]! = target) :
    ∃ result : ReceiveFinishWithRemoval,
      control.finish_receive_with_removal state target slot true = ok result ∧
      result.disposition = ReceiveDisposition.Consumed ∧ ValidControl result.state ∧
      (cacheSeqs result.state.receive_cache).Perm ((cacheSeqs state.receive_cache).erase target.val) := by
  obtain ⟨result, hrun, hconsumed, _⟩ := finish_receive_consumed state target slot h.capacity hlive hentry
  obtain ⟨wrapped, hwrapped, _, _, _, _, hperm⟩ := finish_receive_consumed_cacheSeqs state target slot h.capacity hlive hentry
  have hstate : wrapped.state = result.state := congrArg ReceiveFinish.state (RustM.ok.inj (hwrapped.symm.trans (finish_receive_wrapper_matches_detailed state target slot true result hrun)))
  obtain ⟨validResult, hvalidRun, hvalid⟩ := h.finish_receive_with_removal target slot true
  exact ⟨result, hrun, hconsumed, (RustM.ok.inj (hvalidRun.symm.trans hrun)) ▸ hvalid, hstate ▸ hperm⟩

/-- Detailed completion consumes the target and preserves every other capability in exactly one active slot. -/
theorem ValidControl.finish_receive_with_removal_capabilities
    {state : RatchetState} (h : ValidControl state) (target : Std.U64) (slot : Std.U8)
    (hlive : slot.val < state.receive_cache.len.val)
    (hentry : state.receive_cache.entries.val[slot.val]! = target) :
    ∃ result : ReceiveFinishWithRemoval,
      control.finish_receive_with_removal state target slot true = ok result ∧
      target.val ∉ cacheSeqs result.state.receive_cache ∧
      ∀ other : Std.U64, other ≠ target → other.val ∈ cacheSeqs state.receive_cache →
        other.val ∈ cacheSeqs result.state.receive_cache ∧
        ∀ i j, i < result.state.receive_cache.len.val → j < result.state.receive_cache.len.val →
          result.state.receive_cache.entries.val[i]! = other →
          result.state.receive_cache.entries.val[j]! = other → i = j := by
  obtain ⟨result, hrun, _, hvalid, hperm⟩ := h.finish_receive_exact target slot hlive hentry
  refine ⟨result, hrun, ?_, ?_⟩
  · exact fun hmem => h.unique.not_mem_erase (hperm.mem_iff.mp hmem)
  · intro other hne hmem
    exact ⟨hperm.mem_iff.mpr ((List.mem_erase_of_ne (fun heq => hne (UScalar.eq_of_val_eq heq))).mpr hmem),
      fun i j hi hj hiother hjother => hvalid.slot_unique i j hi hj (hiother.trans hjother.symm)⟩

/-- Every wrong logical/physical slot pair is rejected neutrally, including malformed cache lengths. -/
theorem finish_receive_with_removal_invalid_slot
    (state : RatchetState) (target : Std.U64) (slot : Std.U8) (authenticated : Bool)
    (hinvalid : ¬ (slot.val < state.receive_cache.len.val ∧ slot.val < 50 ∧
      state.receive_cache.entries.val[slot.val]! = target)) :
    finish_receive_with_removal state target slot authenticated =
      ok { state, disposition := ReceiveDisposition.Missing, removal := core.option.Option.None } := by
  by_cases hcap : 50 < state.receive_cache.len.val
  · exact finish_receive_with_removal_over_capacity state target slot authenticated hcap
  · by_cases hslot : slot.val < state.receive_cache.len.val
    · exact finish_receive_with_removal_mismatch state target slot authenticated (Nat.le_of_not_gt hcap) hslot
        (fun heq => hinvalid ⟨hslot, Nat.lt_of_lt_of_le hslot (Nat.le_of_not_gt hcap), heq⟩)
    · exact finish_receive_with_removal_out_of_range state target slot authenticated (Nat.le_of_not_gt hslot)

/-- The generated bounded lookup is exact over its searched window for arbitrary cache lengths. -/
theorem lookup_receive_key_loop_exact (state : RatchetState) (sequence : Std.U64) :
    ∀ (n : Nat) (slot remaining : Std.U8), remaining.val = n →
      ∃ result, lookup_receive_key_loop (UScalar.cast UScalarTy.Usize 50#u64)
          state sequence slot remaining = ok result ∧
        (∀ found, result = core.option.Option.Some found →
          slot.val ≤ found.val ∧ found.val < slot.val + n ∧
          found.val < state.receive_cache.len.val ∧ found.val < 50 ∧
          state.receive_cache.entries.val[found.val]! = sequence) ∧
        (result = core.option.Option.None → ∀ i, i < 50 → slot.val ≤ i →
          i < state.receive_cache.len.val → i < slot.val + n →
          state.receive_cache.entries.val[i]! ≠ sequence) := by
  intro n
  induction n with
  | zero =>
    intro slot remaining hrem
    have hzero : remaining = 0#u8 := by scalar_tac
    rw [hzero, lookup_receive_key_loop, loop.eq_def]
    simp [lookup_receive_key_loop.body]
    omega
  | succ m ih =>
    intro slot remaining hrem
    have hpos : remaining > 0#u8 := by scalar_tac
    rw [lookup_receive_key_loop, loop.eq_def]
    simp only [lookup_receive_key_loop.body, hpos, if_true, lift, bind_tc_ok]
    by_cases hcap : 50 ≤ slot.val
    · rw [if_pos (by scalar_tac)]
      exact ⟨_, rfl, by simp, by intro _ i hi hlo _ _; omega⟩
    · rw [if_neg (by scalar_tac)]
      by_cases hlen : state.receive_cache.len.val ≤ slot.val
      · rw [if_pos (by scalar_tac)]
        exact ⟨_, rfl, by simp, by intro _ i _ hlo hhi _; omega⟩
      · rw [if_neg (by scalar_tac), entries_index_eq_ok state.receive_cache slot (by omega)]
        simp only [bind_tc_ok]
        by_cases hhit : state.receive_cache.entries.val[slot.val]! = sequence
        · rw [if_pos hhit]
          exact ⟨_, rfl, fun found hfound => by cases hfound; exact ⟨le_refl _, by omega, by omega, by omega, hhit⟩, by simp⟩
        · obtain ⟨slot', hslot', hslotval⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
          obtain ⟨rem', hrem', hremval⟩ := uscalar_sub_eq_ok remaining 1#u8 (by scalar_tac)
          obtain ⟨result, hrun, hsound, hnone⟩ := ih slot' rem' (by simp at hremval; omega)
          refine ⟨result, ?_, ?_, ?_⟩
          · simpa only [if_neg hhit, hslot', hrem', bind_tc_ok, lookup_receive_key_loop, lookup_receive_key_loop.body, lift] using hrun
          · intro found hfound
            have hs := hsound found hfound
            exact ⟨by omega, by scalar_tac, hs.2.2⟩
          · intro hresult i hibound histart hilive hirange
            by_cases hi : i = slot.val
            · exact hi ▸ hhit
            · exact hnone hresult i hibound (by scalar_tac) hilive (by scalar_tac)

/-- A missing public lookup excludes the target from the logical cache. -/
theorem lookup_receive_key_none_is_absent
    (state : RatchetState) (target : Std.U64) (hstate : state.Wf)
    (hrun : lookup_receive_key state target = ok core.option.Option.None) :
    target.val ∉ cacheSeqs state.receive_cache := by
  intro hmem
  obtain ⟨slot, hfound, _, _⟩ := lookup_receive_key_of_mem state target hstate hmem
  simp only [hrun, RustM.ok.injEq, reduceCtorEq] at hfound

/-- A successful public lookup identifies the unique physical slot holding the target. -/
theorem ValidControl.lookup_receive_key_returns_unique_slot
    {state : RatchetState} (h : ValidControl state) (target : Std.U64) (slot : Std.U8)
    (hrun : lookup_receive_key state target = ok (core.option.Option.Some slot)) :
    slot.val < state.receive_cache.len.val ∧ state.receive_cache.entries.val[slot.val]! = target ∧
      ∀ other : Std.U8, other.val < state.receive_cache.len.val →
        state.receive_cache.entries.val[other.val]! = target → other = slot := by
  obtain ⟨hlive, hentry⟩ := lookup_receive_key_sound state target slot h.capacity hrun
  exact ⟨hlive, hentry, fun other hother heq => UScalar.eq_of_val_eq (h.slot_unique other.val slot.val hother hlive (heq.trans hentry.symm))⟩

end beaconcrypt_core.ratchet.control
