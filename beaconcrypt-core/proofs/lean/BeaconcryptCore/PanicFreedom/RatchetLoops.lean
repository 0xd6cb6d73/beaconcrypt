import BeaconcryptCore.Refinement.RatchetControl

/-!
# Totality of the material receive loops

The extracted receive helpers terminate normally for every typed input, including malformed control states and defensive rejection paths. No cryptographic or successful-validation premise is required.
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

/-- Publishing staged slots always terminates normally, even when its input window exceeds the cache capacity. -/
theorem publish_future_receive_slots_loop_ok
    (n : Nat) :
    ∀ (state : RefinedRatchet SendChain ReceiveChain Material)
      (staged : Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
      (slot left : Std.U8), left.val = n →
      ∃ result, publish_future_receive_slots_loop state staged slot left = ok result := by
  induction n with
  | zero =>
    intro state staged slot left hleft
    have hz : left = 0#u8 := by scalar_tac
    simp [publish_future_receive_slots_loop, loop.eq_def, publish_future_receive_slots_loop.body, hz]
  | succ n ih =>
    intro state staged slot left hleft
    rw [publish_future_receive_slots_loop, loop.eq_def]
    have hpos : left > 0#u8 := by scalar_tac
    simp only [publish_future_receive_slots_loop.body, hpos, if_true, lift, capacity_eq_ok, bind_tc_ok]
    by_cases hcap : 50 ≤ slot.val
    · simp [hcap]
    · rw [if_neg (by scalar_tac)]
      have hidx : (UScalar.cast UScalarTy.Usize slot).val < staged.length := by scalar_tac
      simp only [Array.index_mut_usize, array_index_eq_ok staged _ hidx, bind_tc_ok, core.option.Option.take]
      simp only [Std.core.option.Option.take, massert, if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize slot < 50#usize), bind_tc_ok, array_index_eq_ok state.receive_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac)]
      dsimp! only
      rw [array_update_eq_ok _ _ _ (by scalar_tac)]
      obtain ⟨slot', hslot, hslotval⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
      obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
      simp only [hslot, hnext, bind_tc_ok]
      simp! only [publish_future_receive_slots_loop, publish_future_receive_slots_loop.body, lift, capacity_eq_ok, bind_tc_ok, Array.index_mut_usize, core.option.Option.take, Std.core.option.Option.take, massert] at ih
      exact ih _ _ _ _ (by scalar_tac)

/-- The publication wrapper has no additional preconditions. -/
theorem publish_future_receive_slots_ok
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (staged : Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
    (slot left : Std.U8) :
    ∃ result, publish_future_receive_slots state staged slot left = ok result := by
  exact publish_future_receive_slots_loop_ok left.val state staged slot left rfl

/-- Empty-slot validation terminates normally for every window. -/
theorem refined_receive_slots_are_empty_loop_ok
    (state : RefinedRatchet SendChain ReceiveChain Material) (n : Nat) :
    ∀ (slot left : Std.U8), left.val = n →
      ∃ result, refined_receive_slots_are_empty_loop state slot left = ok result := by
  induction n with
  | zero =>
    intro slot left hleft
    simp [refined_receive_slots_are_empty_loop, loop.eq_def, refined_receive_slots_are_empty_loop.body, show left = 0#u8 by scalar_tac]
  | succ n ih =>
    intro slot left hleft
    rw [refined_receive_slots_are_empty_loop, loop.eq_def]
    simp only [refined_receive_slots_are_empty_loop.body, if_pos (by scalar_tac : left > 0#u8), lift, capacity_eq_ok, bind_tc_ok]
    by_cases hcap : 50 ≤ slot.val
    · simp [hcap]
    · rw [if_neg (by scalar_tac)]
      simp only [array_index_eq_ok state.receive_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac), core.option.Option.is_some, bind_tc_ok]
      by_cases hsome : Std.core.option.Option.is_some (state.receive_slots.val[(UScalar.cast UScalarTy.Usize slot).val]'(by scalar_tac)) = true
      · exact ⟨false, by simp only [if_pos hsome]⟩
      · rw [if_neg hsome]
        obtain ⟨slot', hslot, _⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
        obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
        simpa only [refined_receive_slots_are_empty_loop, refined_receive_slots_are_empty_loop.body, lift, capacity_eq_ok, core.option.Option.is_some, hslot, hnext, bind_tc_ok] using ih slot' left' (by scalar_tac)

/-- Empty-slot validation is total on arbitrary typed states. -/
theorem refined_receive_slots_are_empty_ok
    (state : RefinedRatchet SendChain ReceiveChain Material) (slot left : Std.U8) :
    ∃ result, refined_receive_slots_are_empty state slot left = ok result := by
  exact refined_receive_slots_are_empty_loop_ok state left.val slot left rfl

end beaconcrypt_core.ratchet.refined
