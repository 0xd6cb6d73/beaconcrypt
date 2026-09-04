import BeaconcryptCore.PanicFreedom.RatchetLoops

/-!
# Totality of material receive validation and publication

Malformed pending transactions and publication indices are ordinary defensive rejections. These proofs establish normal return independently of the logical and cryptographic invariants.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.refined

variable {SendChain ReceiveChain Material : Type}

/-- Future publication returns normally whether the window is accepted or rejected. -/
theorem publish_future_receive_ok
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) :
    ∃ result, publish_future_receive state pending = ok result := by
  simp only [publish_future_receive, lift, capacity_eq_ok, bind_tc_ok]
  by_cases hfirst : 50 < pending.first_slot.val
  · simp [hfirst]
  · rw [if_neg (by scalar_tac)]
    obtain ⟨remaining, hremaining, _⟩ := uscalar_sub_eq_ok (UScalar.cast UScalarTy.Usize 50#u64) (UScalar.cast UScalarTy.Usize pending.first_slot) (by scalar_tac)
    obtain ⟨result, hresult⟩ := publish_future_receive_slots_ok state pending.staged_slots pending.first_slot pending.skipped
    simp only [hremaining, hresult, bind_tc_ok]
    split_ifs <;> exact ⟨_, rfl⟩

/-- Cached publication returns normally for arbitrary prepared indices and states. -/
theorem publish_cached_receive_ok
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (prepared : PreparedCachedReceive) :
    ∃ result, publish_cached_receive state prepared = ok result := by
  simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok]
  by_cases htarget : 50 ≤ prepared.target_slot.val
  · simp [htarget]
  · rw [if_neg (by scalar_tac)]
    by_cases hlast : 50 ≤ prepared.last_slot.val
    · simp [hlast]
    · rw [if_neg (by scalar_tac)]
      simp! only [array_index_mut_eq_ok state.receive_slots (UScalar.cast UScalarTy.Usize prepared.last_slot) (by scalar_tac), core.option.Option.take, Std.core.option.Option.take, bind_tc_ok, massert, if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.target_slot < 50#usize)]
      simp! only [array_index_mut_eq_ok (state.receive_slots.set (UScalar.cast UScalarTy.Usize prepared.last_slot) none) (UScalar.cast UScalarTy.Usize prepared.target_slot) (by scalar_tac), bind_tc_ok]
      rw [array_update_eq_ok _ _ _ (by scalar_tac)]
      split_ifs <;> exact ⟨_, rfl⟩

/-- Complete pending-transaction validation returns a Boolean for every typed transaction. -/
theorem pending_receive_is_valid_ok
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) (requested : Std.U64) :
    ∃ result, pending_receive_is_valid state pending requested = ok result := by
  simp only [pending_receive_is_valid, RatchetState.impl.receive_sequence,
    RatchetState.impl.send_sequence, RatchetState.receive_cache_len, lift, bind_tc_ok]
  by_cases hrequested : requested.val ≤ state.control.receive_sequence.val
  · simp [show requested ≤ state.control.receive_sequence by scalar_tac]
  · simp only [if_neg (show ¬requested ≤ state.control.receive_sequence by scalar_tac)]
    obtain ⟨derivations, hderivations, _⟩ := uscalar_sub_eq_ok requested state.control.receive_sequence (by omega)
    obtain ⟨skipped_plus_one, hskipped, _⟩ := uscalar_add_eq_ok (UScalar.cast UScalarTy.U64 pending.skipped) 1#u64 (by scalar_tac)
    obtain ⟨committed_len, hlen, _⟩ := uscalar_add_eq_ok (UScalar.cast UScalarTy.Usize pending.first_slot) (UScalar.cast UScalarTy.Usize pending.skipped) (by scalar_tac)
    obtain ⟨expected, hexpected, _⟩ := uscalar_add_eq_ok state.control.receive_sequence 1#u64 (by scalar_tac)
    obtain ⟨key, hkey⟩ := lookup_receive_key_total pending.committed_control requested
    obtain ⟨prefix_matches, hprefix⟩ := receive_control_prefix_matches_ok state.control pending.committed_control 0#u8 pending.first_slot
    obtain ⟨valid_slots, hslots⟩ := pending_receive_slots_are_valid_ok state pending pending.first_slot expected pending.skipped
    simp only [hderivations, hskipped, hlen, hexpected, hkey, hprefix, hslots, capacity_eq_ok, core.option.Option.is_some, bind_tc_ok]
    by_cases hidx : committed_len.val < 50
    · simp only [if_pos (show committed_len < UScalar.cast UScalarTy.Usize 50#u64 by scalar_tac), array_index_eq_ok state.receive_slots committed_len (by scalar_tac), array_index_eq_ok pending.staged_slots committed_len (by scalar_tac), bind_tc_ok]
      simp only [← apply_ite (f := RustM.ok), RustM.ok.injEq, exists_eq']
    · simp only [if_neg (show ¬committed_len < UScalar.cast UScalarTy.Usize 50#u64 by scalar_tac)]
      simp only [← apply_ite (f := RustM.ok), RustM.ok.injEq, exists_eq']

end beaconcrypt_core.ratchet.refined
