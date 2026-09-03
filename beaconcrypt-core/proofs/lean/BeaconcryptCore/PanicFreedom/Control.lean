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

/-- Planning a receive returns normally for all counters and cache lengths. -/
theorem plan_receive_until_total (st : RatchetState) (target : Std.U64) :
    ∃ p, plan_receive_until st target = ok p :=
  if hle : target.val ≤ st.receive_sequence.val then
    ⟨_, plan_receive_until_replay st target hle⟩
  else if hgap : st.receive_sequence.val + 51 < target.val then
    ⟨_, plan_receive_until_reject_of_gap_gt st target hgap⟩
  else if hfull : 50 < st.receive_cache.len.val + (target.val - st.receive_sequence.val - 1) then
    ⟨_, plan_receive_until_reject_of_cache_full st target (by omega) (by omega) hfull⟩
  else
    (plan_receive_until_accept st target (by omega) (by omega)).elim fun _ h => ⟨_, h.1⟩

/-- Send advancement also returns normally at sequence exhaustion. -/
theorem advance_send_total (st : RatchetState) : ∃ r, advance_send st = ok r :=
  if h : st.send_sequence = core.num.U64.MAX then ⟨_, advance_send_max st h⟩
  else (advance_send_ok st h).imp fun _ h => h.1

/-- Target advancement also returns normally at sequence exhaustion. -/
theorem advance_receive_target_total (st : RatchetState) :
    ∃ r, advance_receive_target st = ok r :=
  if h : st.receive_sequence = core.num.U64.MAX then ⟨_, advance_receive_target_max st h⟩
  else (advance_receive_target_ok st h).imp fun _ h => h.1

/-- The empty cache constructor returns normally. -/
theorem SequenceCache.empty_total : ∃ r, SequenceCache.empty = ok r := ⟨_, rfl⟩

/-- Counter-based initialization returns normally for arbitrary persisted counters. -/
theorem RatchetState.from_counters_total (send receive : Std.U64) :
    ∃ r, RatchetState.from_counters send receive = ok r := ⟨_, rfl⟩

/-- Initialization returns normally. -/
theorem RatchetState.new_total (send : Std.U64) :
    ∃ r, RatchetState.new send = ok r := ⟨_, rfl⟩

/-- Default initialization returns normally. -/
theorem RatchetState.default_total :
    ∃ r, RatchetState.Insts.CoreDefaultDefault.default = ok r := ⟨_, rfl⟩

/-- Constructing the exhausted send key returns normally. -/
theorem SendKey.unavailable_total : ∃ r, SendKey.unavailable = ok r := ⟨_, rfl⟩

/-- Availability queries return normally. -/
theorem SendKey.is_available_total (key : SendKey) :
    ∃ r, SendKey.is_available key = ok r := ⟨_, rfl⟩

/-- Sequence queries return normally for available and unavailable keys. -/
theorem SendKey.sequence_total (key : SendKey) :
    ∃ r, SendKey.impl.sequence key = ok r := by
  cases h : key.available <;> simp [SendKey.impl.sequence, h]

/-- Finishing a send returns normally for available and unavailable keys. -/
theorem finish_send_total (key : SendKey) : ∃ r, finish_send key = ok r :=
  if h : key.available then ⟨_, finish_send_available key h⟩
  else ⟨_, finish_send_unavailable key h⟩

/-- The receive completion wrapper inherits the guarded removal's totality. -/
theorem finish_receive_total (st : RatchetState) (target : Std.U64) (slot : Std.U8)
    (authenticated : Bool) : ∃ r, finish_receive st target slot authenticated = ok r := by
  obtain ⟨r, hr⟩ := finish_receive_with_removal_ok st target slot authenticated
  simp [finish_receive, hr]

/-- Restoring a key through the wrapper returns normally. -/
theorem restore_receive_key_total (restore : RatchetRestore) (sequence : Std.U64) :
    ∃ r, restore_receive_key restore sequence = ok r := by
  obtain ⟨r, hr⟩ := restore_receive_key_with_slot_total restore sequence
  cases r <;> simp [restore_receive_key, hr, core.option.Option.map,
    restore_receive_key.closure.Insts.CoreOpsFunctionFnOnceTupleReceiveRestoreStepRatchetRestore.call_once]

/-- Peer replacement returns normally whether or not the peer matches. -/
theorem replace_ratchet_for_peer_total (requested_peer : Std.U64) (peer : PeerRatchetState)
    (replacement : RatchetState) :
    ∃ r, replace_ratchet_for_peer requested_peer peer replacement = ok r :=
  if h : requested_peer = peer.peer_id then
    ⟨_, replace_ratchet_for_peer_match requested_peer peer replacement h⟩
  else ⟨_, replace_ratchet_for_peer_other requested_peer peer replacement h⟩

/-- Peer send dispatch returns normally for every state. -/
theorem advance_send_for_peer_total (requested_peer : Std.U64) (peer : PeerRatchetState) :
    ∃ r, advance_send_for_peer requested_peer peer = ok r := by
  obtain ⟨r, hr⟩ := advance_send_total peer.ratchet
  by_cases h : requested_peer = peer.peer_id <;>
    simp [advance_send_for_peer, replace_ratchet_for_peer, SendKey.unavailable, hr, h]

/-- A bounded mutable array access returns a value and its update continuation. -/
theorem array_index_mut_eq_ok {α : Type} {n : Std.Usize} (v : Std.Array α n)
    (i : Std.Usize) (h : i.val < v.length) :
    v.index_mut_usize i = ok (v.val[i.val], v.set i) := by
  simp only [Std.Array.index_mut_usize, array_index_eq_ok v i h, bind_tc_ok]

end beaconcrypt_core.ratchet.control
