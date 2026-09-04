import BeaconcryptCore.PanicFreedom.Control

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

/-- Comparing optional sequence numbers has no failing branch. -/
theorem optional_sequence_eq_ok (a b : core.option.Option Std.U64) :
    ∃ result, core.option.Option.Insts.CoreCmpPartialEqOption.eq core.U64.Insts.CoreCmpPartialEqU64 a b = ok result := by
  cases a <;> cases b <;> simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64]

/-- Prefix validation terminates normally for arbitrary logical states and windows. -/
theorem receive_control_prefix_matches_loop_ok
    (entry committed : ratchet.control.RatchetState) (n : Nat) :
    ∀ (slot left : Std.U8), left.val = n →
      ∃ result, receive_control_prefix_matches_loop entry committed slot left = ok result := by
  induction n with
  | zero =>
    intro slot left hleft
    simp [receive_control_prefix_matches_loop, loop.eq_def, receive_control_prefix_matches_loop.body, show left = 0#u8 by scalar_tac]
  | succ n ih =>
    intro slot left hleft
    rw [receive_control_prefix_matches_loop, loop.eq_def]
    simp only [receive_control_prefix_matches_loop.body, if_pos (by scalar_tac : left > 0#u8), lift, capacity_eq_ok, bind_tc_ok]
    by_cases hcap : 50 ≤ slot.val
    · simp [hcap]
    · rw [if_neg (by scalar_tac)]
      obtain ⟨a, ha⟩ := RatchetState.receive_key_at_total entry slot
      obtain ⟨b, hb⟩ := RatchetState.receive_key_at_total committed slot
      obtain ⟨same, hsame⟩ := optional_sequence_eq_ok a b
      obtain ⟨slot', hslot, _⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
      obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
      obtain ⟨result, hresult⟩ := ih slot' left' (by scalar_tac)
      simp only [receive_control_prefix_matches_loop, receive_control_prefix_matches_loop.body, lift, capacity_eq_ok, bind_tc_ok] at hresult
      cases same <;> simp only [ha, hb, hsame, hslot, hnext, bind_tc_ok, Bool.false_eq_true, if_false, if_true, hresult, RustM.ok.injEq, exists_eq']

/-- Prefix validation is total on arbitrary typed states. -/
theorem receive_control_prefix_matches_ok
    (entry committed : ratchet.control.RatchetState) (slot left : Std.U8) :
    ∃ result, receive_control_prefix_matches entry committed slot left = ok result := by
  exact receive_control_prefix_matches_loop_ok entry committed left.val slot left rfl

/-- Staged material validation terminates normally for every expected sequence and window. -/
theorem pending_receive_slots_are_valid_loop_ok
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) (n : Nat) :
    ∀ (slot : Std.U8) (expected : Std.U64) (left : Std.U8), left.val = n →
      ∃ result, pending_receive_slots_are_valid_loop state pending slot expected left = ok result := by
  induction n with
  | zero =>
    intro slot expected left hleft
    simp [pending_receive_slots_are_valid_loop, loop.eq_def, pending_receive_slots_are_valid_loop.body, show left = 0#u8 by scalar_tac]
  | succ n ih =>
    intro slot expected left hleft
    rw [pending_receive_slots_are_valid_loop, loop.eq_def]
    simp only [pending_receive_slots_are_valid_loop.body, if_pos (by scalar_tac : left > 0#u8), lift, capacity_eq_ok, bind_tc_ok]
    by_cases hcap : 50 ≤ slot.val
    · simp [hcap]
    · rw [if_neg (by scalar_tac)]
      simp only [array_index_eq_ok state.receive_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac), array_index_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac), core.option.Option.is_some, core.option.Option.as_ref, bind_tc_ok]
      by_cases hsome : Std.core.option.Option.is_some (state.receive_slots.val[(UScalar.cast UScalarTy.Usize slot).val]'(by scalar_tac)) = true
      · exact ⟨false, by simp only [if_pos hsome]⟩
      · rw [if_neg hsome]
        cases hs : pending.staged_slots.val[(UScalar.cast UScalarTy.Usize slot).val]'(by scalar_tac) with
        | none => exact ⟨false, rfl⟩
        | some staged =>
          simp only [bind_tc_ok]
          obtain ⟨key, hkey⟩ := RatchetState.receive_key_at_total pending.committed_control slot
          obtain ⟨same, hsame⟩ := optional_sequence_eq_ok key (core.option.Option.Some expected)
          obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
          simp only [hkey, hsame, hnext, bind_tc_ok]
          split_ifs with hseq heq hz hmax <;> try exact ⟨_, rfl⟩
          obtain ⟨slot', hslot, _⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
          have hval : expected.val ≠ (core.num.U64.MAX).val := fun hc => hmax (UScalar.eq_of_val_eq hc)
          simp [core.num.U64.MAX, U64.rMax] at hval
          obtain ⟨expected', hexpected, _⟩ := uscalar_add_eq_ok expected 1#u64 (by scalar_tac)
          simpa only [pending_receive_slots_are_valid_loop, pending_receive_slots_are_valid_loop.body, lift, capacity_eq_ok, core.option.Option.is_some, core.option.Option.as_ref, hslot, hexpected, bind_tc_ok] using ih slot' expected' left' (by scalar_tac)

/-- The staged-slot validation wrapper is total on arbitrary typed inputs. -/
theorem pending_receive_slots_are_valid_ok
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material)
    (slot : Std.U8) (expected : Std.U64) (left : Std.U8) :
    ∃ result, pending_receive_slots_are_valid state pending slot expected left = ok result := by
  exact pending_receive_slots_are_valid_loop_ok state pending left.val slot expected left rfl

end beaconcrypt_core.ratchet.refined
