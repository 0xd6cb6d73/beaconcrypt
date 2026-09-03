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

end beaconcrypt_core.ratchet.refined
