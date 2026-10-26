import BeaconcryptCore.Refinement.RatchetReceiveBehavior

/-! Exact compatibility laws for the extracted low-level receive completion API. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.control

private theorem finish_receive_lookup_missing (state : RatchetState) (target : Std.U64)
    (slot : Std.U8) (hstate : state.Wf)
    (hlookup : lookup_receive_key state target = ok core.option.Option.None) :
    finish_receive state target slot true = ok { state, disposition := ReceiveDisposition.Missing } := by
  apply finish_receive_missing_state_neutral state target slot true ?_ hstate
  by_cases hslot : slot.val < state.receive_cache.len.val
  · refine Or.inr ?_
    intro heq
    obtain ⟨found, hfound, _, _⟩ := lookup_receive_key_complete state target slot.val hstate hslot heq
    simp only [hlookup, RustM.ok.injEq, reduceCtorEq] at hfound
  · exact Or.inl (Nat.le_of_not_gt hslot)

/-- A retained cached completion can be retried once; the successful retry consumes the key and any later completion is missing. -/
theorem cached_receive_failure_retry_consumes_once
    (state : RatchetState) (target : Std.U64) (slot : Std.U8)
    (hstate : state.Wf) (hslot : slot.val < state.receive_cache.len.val)
    (hentry : state.receive_cache.entries.val[slot.val]! = target)
    (hpast : target.val ≤ state.receive_sequence.val)
    (hunique : ∀ i, i < state.receive_cache.len.val →
      state.receive_cache.entries.val[i]! = target → i = slot.val) :
    ∃ consumed : RatchetState,
      finish_receive state target slot false = ok { state, disposition := ReceiveDisposition.Retained } ∧
      plan_receive_until state target = ok { sequence := core.option.Option.Some target, derivations := 0#u64 } ∧
      finish_receive state target slot true = ok { state := consumed, disposition := ReceiveDisposition.Consumed } ∧
      lookup_receive_key consumed target = ok core.option.Option.None ∧
      finish_receive consumed target slot true = ok { state := consumed, disposition := ReceiveDisposition.Missing } := by
  obtain ⟨finished, hfinish, hdisposition, hlength, _, _, _, _⟩ :=
    finish_receive_consumed state target slot hstate hslot hentry
  have hlookup := lookup_receive_key_consumed_absent state target slot hstate hslot hentry hunique finished hfinish
  have hfinished : finished.state.Wf := by
    simpa only [RatchetState.Wf, SequenceCache.Wf, hlength] using Nat.le_trans (Nat.sub_le state.receive_cache.len.val 1) hstate
  exact ⟨finished.state,
    by simp only [finish_receive, finish_receive_with_removal_retained state target slot hstate hslot hentry, bind_tc_ok],
    plan_receive_until_replay state target hpast,
    by simp only [finish_receive, hfinish, bind_tc_ok, hdisposition],
    hlookup, finish_receive_lookup_missing finished.state target slot hfinished hlookup⟩

/-- Consuming from a full cache frees exactly one slot and admits the next future target with one derivation. -/
theorem successful_receive_releases_capacity_for_next_future
    (state : RatchetState) (target : Std.U64) (slot : Std.U8) (nextTarget : Std.U64)
    (hstate : state.Wf) (hslot : slot.val < state.receive_cache.len.val)
    (hentry : state.receive_cache.entries.val[slot.val]! = target)
    (hfull : state.receive_cache.len.val = 50)
    (hnext : nextTarget.val = state.receive_sequence.val + 1) :
    ∃ consumed : RatchetState,
      finish_receive state target slot true = ok { state := consumed, disposition := ReceiveDisposition.Consumed } ∧
      consumed.receive_cache.len.val = 49 ∧ consumed.receive_sequence = state.receive_sequence ∧
      plan_receive_until consumed nextTarget = ok { sequence := core.option.Option.Some nextTarget, derivations := 1#u64 } := by
  obtain ⟨finished, hfinish, hdisposition, hlength, _, hreceive, _, _⟩ :=
    finish_receive_consumed state target slot hstate hslot hentry
  obtain ⟨derivations, hplan, hderivations⟩ := plan_receive_until_accept finished.state nextTarget
    (by scalar_tac) (by scalar_tac)
  have hone : derivations = 1#u64 := by scalar_tac
  exact ⟨finished.state, by simp only [finish_receive, hfinish, bind_tc_ok, hdisposition],
    by omega, hreceive, by simpa only [hone] using hplan⟩

end beaconcrypt_core.ratchet.control
