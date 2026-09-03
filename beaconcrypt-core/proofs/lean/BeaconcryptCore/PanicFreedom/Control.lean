import BeaconcryptCore.Refinement.RatchetControlRestore

/-!
# Unconditional panic freedom of the ratchet control operations

The defensive capacity checks make normal return independent of the logical state invariants. These theorems quantify over arbitrary values of the extracted state types; an ordinary rejection is a normal return.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

namespace beaconcrypt_core.ratchet.control

/-- The bounded lookup terminates without a representation invariant. -/
theorem lookup_receive_key_loop_total (st : RatchetState) (sequence : Std.U64) :
    ∀ (n : Nat) (slot remaining : Std.U8), remaining.val = n →
      ∃ r, lookup_receive_key_loop (UScalar.cast UScalarTy.Usize 50#u64)
        st sequence slot remaining = ok r := by
  intro n
  induction n with
  | zero =>
    intro slot remaining hrem
    have hzero : remaining = 0#u8 := by scalar_tac
    rw [hzero, lookup_receive_key_loop, loop.eq_def]
    simp [lookup_receive_key_loop.body]
  | succ m ih =>
    intro slot remaining hrem
    have hpos : remaining > 0#u8 := by scalar_tac
    rw [lookup_receive_key_loop, loop.eq_def]
    simp only [lookup_receive_key_loop.body, hpos, if_true, lift, bind_tc_ok]
    by_cases hcap : 50 ≤ slot.val
    · simpa only [if_pos (show UScalar.cast UScalarTy.Usize slot ≥
          UScalar.cast UScalarTy.Usize 50#u64 by scalar_tac), RustM.ok.injEq]
        using Exists.intro core.option.Option.None rfl
    · rw [if_neg (by scalar_tac)]
      by_cases hlen : st.receive_cache.len.val ≤ slot.val
      · simpa only [if_pos (show slot ≥ st.receive_cache.len by scalar_tac), RustM.ok.injEq]
          using Exists.intro core.option.Option.None rfl
      · rw [if_neg (by scalar_tac), entries_index_eq_ok st.receive_cache slot (by omega)]
        simp only [bind_tc_ok]
        by_cases hhit : st.receive_cache.entries.val[slot.val]! = sequence
        · simp only [if_pos hhit, RustM.ok.injEq, exists_eq']
        · obtain ⟨slot', hslot', hslotval⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
          obtain ⟨rem', hrem', hremval⟩ := uscalar_sub_eq_ok remaining 1#u8 (by scalar_tac)
          obtain ⟨r, hr⟩ := ih slot' rem' (by simp at hremval; omega)
          simpa only [if_neg hhit, hslot', hrem', bind_tc_ok, lookup_receive_key_loop,
            lookup_receive_key_loop.body, lift] using Exists.intro r hr

/-- Lookup is safe for every extracted state, including an excessive cache length. -/
theorem lookup_receive_key_total (st : RatchetState) (sequence : Std.U64) :
    ∃ r, lookup_receive_key st sequence = ok r := by
  simpa only [lookup_receive_key_unfold] using
    lookup_receive_key_loop_total st sequence 50 0#u8 50#u8 (by simp)

end beaconcrypt_core.ratchet.control
