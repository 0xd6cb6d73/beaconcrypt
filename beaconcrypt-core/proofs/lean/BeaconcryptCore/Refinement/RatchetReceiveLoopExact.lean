import BeaconcryptCore.PanicFreedom.RatchetReceive

/-!
# Exact material receive loop behavior

The lemmas in this file describe the validated array windows and the exact copy-and-clear behavior of future material publication. They reason about the extracted loops without changing the ideal ratchet model.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.refined

variable {SendChain ReceiveChain Material : Type}

private theorem array_index_bang {α : Type} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (h : i.val < v.length) :
    v.index_usize i = ok v.val[i.val]! := by
  simpa only [getElem!_pos v.val i.val (by simpa using h)] using array_index_eq_ok v i h

private theorem array_set_bang {α : Type} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (x : α) (j : Nat) (h : j < v.length) :
    (v.set i x).val[j]! = if i.val = j then x else v.val[j]! := by
  by_cases heq : i.val = j
  · simpa only [if_pos heq, Array.getElem!_Nat_eq] using
      Array.getElem!_Nat_set_eq v i j x ⟨heq, h⟩
  · simpa only [if_neg heq, Array.getElem!_Nat_eq] using
      Array.getElem!_Nat_set_ne v i j x heq

/-- Publication copies precisely its bounded window and clears precisely the same staged slots. -/
theorem publish_future_receive_slots_loop_exact (n : Nat) :
    ∀ (state : RefinedRatchet SendChain ReceiveChain Material)
      (staged : Std.Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
      (slot left : Std.U8), left.val = n → slot.val + left.val ≤ 50 →
      ∃ out remaining, publish_future_receive_slots_loop state staged slot left = ok (out, remaining) ∧
        out.control = state.control ∧ out.send_chain = state.send_chain ∧
        out.receive_chain = state.receive_chain ∧
        (∀ i, i < 50 → out.receive_slots.val[i]! =
          if slot.val ≤ i ∧ i < slot.val + left.val then staged.val[i]! else state.receive_slots.val[i]!) ∧
        (∀ i, i < 50 → remaining.val[i]! =
          if slot.val ≤ i ∧ i < slot.val + left.val then core.option.Option.None else staged.val[i]!) := by
  induction n with
  | zero =>
    intro state staged slot left hleft hbound
    have hz : left = 0#u8 := by scalar_tac
    simp [hz, publish_future_receive_slots_loop, loop.eq_def,
      publish_future_receive_slots_loop.body]
  | succ n ih =>
    intro state staged slot left hleft hbound
    rw [publish_future_receive_slots_loop, loop.eq_def]
    simp only [publish_future_receive_slots_loop.body,
      if_pos (by scalar_tac : left > 0#u8), lift, capacity_eq_ok, bind_tc_ok,
      if_neg (by scalar_tac : ¬ UScalar.cast UScalarTy.Usize slot ≥ UScalar.cast UScalarTy.Usize 50#u64)]
    simp only [Array.index_mut_usize,
      array_index_bang staged (UScalar.cast UScalarTy.Usize slot) (by scalar_tac),
      array_index_bang state.receive_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac),
      bind_tc_ok, core.option.Option.take, Std.core.option.Option.take, massert,
      if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize slot < 50#usize)]
    dsimp! only
    rw [Array.set_getElem!_eq, array_update_eq_ok _ _ _ (by scalar_tac)]
    obtain ⟨slot', hslot, hslotval⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
    obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
    obtain ⟨out, remaining, hrun, hcontrol, hsend, hreceive, hslots, hremaining⟩ :=
      ih { state with receive_slots := (state.receive_slots.set (UScalar.cast UScalarTy.Usize slot)
          staged.val[(UScalar.cast UScalarTy.Usize slot).val]!) }
        (staged.set (UScalar.cast UScalarTy.Usize slot) core.option.Option.None)
        slot' left' (by scalar_tac) (by scalar_tac)
    simp! only [publish_future_receive_slots_loop, publish_future_receive_slots_loop.body,
      lift, capacity_eq_ok, bind_tc_ok, Array.index_mut_usize, core.option.Option.take,
      Std.core.option.Option.take, massert] at hrun
    refine ⟨out, remaining, by simpa only [hslot, hnext, bind_tc_ok] using hrun,
      hcontrol, hsend, hreceive, ?_, ?_⟩
    · intro i hi
      rw [hslots i hi, array_set_bang staged _ _ i (by scalar_tac),
        array_set_bang state.receive_slots _ _ i (by scalar_tac)]
      have hcast : (UScalar.cast UScalarTy.Usize slot).val = slot.val := by simp_scalar
      simp only [hcast]
      split_ifs <;> first | rfl | scalar_tac
    · intro i hi
      rw [hremaining i hi, array_set_bang staged _ _ i (by scalar_tac)]
      split_ifs <;> first | rfl | scalar_tac

/-- The public publication helper has the same exact copy-and-clear semantics. -/
theorem publish_future_receive_slots_exact
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (staged : Std.Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
    (slot left : Std.U8) (hbound : slot.val + left.val ≤ 50) :
    ∃ out remaining, publish_future_receive_slots state staged slot left = ok (out, remaining) ∧
      out.control = state.control ∧ out.send_chain = state.send_chain ∧
      out.receive_chain = state.receive_chain ∧
      (∀ i, i < 50 → out.receive_slots.val[i]! =
        if slot.val ≤ i ∧ i < slot.val + left.val then staged.val[i]! else state.receive_slots.val[i]!) ∧
      (∀ i, i < 50 → remaining.val[i]! =
        if slot.val ≤ i ∧ i < slot.val + left.val then core.option.Option.None else staged.val[i]!) :=
  publish_future_receive_slots_loop_exact left.val state staged slot left rfl hbound

private theorem receive_key_at_exact (state : ratchet.control.RatchetState) (slot : Std.U8)
    (hlen : slot.val < state.receive_cache.len.val) (hcap : slot.val < 50) :
    ratchet.control.RatchetState.receive_key_at state slot =
      ok (core.option.Option.Some state.receive_cache.entries.val[slot.val]!) := by
  simp only [ratchet.control.RatchetState.receive_key_at, SequenceCache.entry, lift, capacity_eq_ok,
    bind_tc_ok, if_pos (by scalar_tac : slot < state.receive_cache.len),
    if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize slot < UScalar.cast UScalarTy.Usize 50#u64),
    entries_index_eq_ok _ _ hcap]

/-- Exact staged sequence matches and empty destination slots make validation succeed. -/
theorem pending_receive_slots_are_valid_loop_true
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) (n : Nat) :
    ∀ (slot : Std.U8) (expected : Std.U64) (left : Std.U8), left.val = n →
      slot.val + left.val ≤ 50 →
      slot.val + left.val ≤ pending.committed_control.receive_cache.len.val →
      expected.val + left.val ≤ 2 ^ 64 →
      (∀ i, slot.val ≤ i → i < slot.val + left.val →
        state.receive_slots.val[i]! = core.option.Option.None) →
      (∀ j, j < left.val → ∃ cached,
        pending.staged_slots.val[slot.val + j]! = core.option.Option.Some cached ∧
        cached.sequence.val = expected.val + j ∧
        pending.committed_control.receive_cache.entries.val[slot.val + j]! = cached.sequence) →
      pending_receive_slots_are_valid_loop state pending slot expected left = ok true := by
  induction n with
  | zero =>
    intro slot expected left hleft hcap hlen hseq hempty hstaged
    simp only [pending_receive_slots_are_valid_loop, loop.eq_def,
      pending_receive_slots_are_valid_loop.body, if_neg (by scalar_tac : ¬left > 0#u8)]
  | succ n ih =>
    intro slot expected left hleft hcap hlen hseq hempty hstaged
    obtain ⟨cached, hcached, hcachedseq, hkey⟩ := hstaged 0 (by omega)
    have heq : cached.sequence = expected := by scalar_tac
    simp only [Nat.add_zero] at hcached hcachedseq hkey
    have hcast : (UScalar.cast UScalarTy.Usize slot).val = slot.val := by simp_scalar
    rw [pending_receive_slots_are_valid_loop, loop.eq_def]
    simp only [pending_receive_slots_are_valid_loop.body,
      if_pos (by scalar_tac : left > 0#u8), lift, capacity_eq_ok, bind_tc_ok,
      if_neg (by scalar_tac : ¬ UScalar.cast UScalarTy.Usize slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
      array_index_bang state.receive_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac),
      array_index_bang pending.staged_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac),
      hcast, hempty slot.val (by omega) (by omega), core.option.Option.is_some,
      Std.core.option.Option.is_some, hcached, core.option.Option.as_ref]
    simp only [Option.isSome, core.option.Option.None, Bool.false_eq_true, if_false, heq, if_true,
      receive_key_at_exact pending.committed_control slot (by omega) (by omega), hkey,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
      bind_tc_ok, beq_self_eq_true]
    obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
    by_cases hz : left' = 0#u8
    · simp only [hnext, bind_tc_ok, hz, if_true]
    · have hmax : expected ≠ core.num.U64.MAX := by simp only [core.num.U64.MAX, U64.rMax]; scalar_tac
      obtain ⟨slot', hslot, hslotval⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
      obtain ⟨expected', hexpected, hexpectedval⟩ := uscalar_add_eq_ok expected 1#u64 (by scalar_tac)
      have hrun := ih slot' expected' left' (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
        (fun i hi hj => hempty i (by scalar_tac) (by scalar_tac)) (by
          intro j hj
          obtain ⟨next, hnextcached, hnextseq, hnextkey⟩ := hstaged (j + 1) (by scalar_tac)
          exact ⟨next, by convert hnextcached using 2; scalar_tac,
            by scalar_tac, by convert hnextkey using 2; scalar_tac⟩)
      simp! only [pending_receive_slots_are_valid_loop, pending_receive_slots_are_valid_loop.body,
        lift, capacity_eq_ok, bind_tc_ok, core.option.Option.is_some, Std.core.option.Option.is_some,
        Option.isSome, core.option.Option.as_ref, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.U64.Insts.CoreCmpPartialEqU64] at hrun
      simp only [Option.isSome, core.option.Option.as_ref,
        core.option.Option.Insts.CoreCmpPartialEqOption.eq] at hrun
      simpa only [hnext, hslot, hexpected, bind_tc_ok, if_neg hz, if_neg hmax] using hrun

/-- Staged validation accepts a bounded consecutive sequence window with empty destinations. -/
theorem pending_receive_slots_are_valid_true
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material)
    (slot : Std.U8) (expected : Std.U64) (left : Std.U8)
    (hcap : slot.val + left.val ≤ 50)
    (hlen : slot.val + left.val ≤ pending.committed_control.receive_cache.len.val)
    (hseq : expected.val + left.val ≤ 2 ^ 64)
    (hempty : ∀ i, slot.val ≤ i → i < slot.val + left.val →
      state.receive_slots.val[i]! = core.option.Option.None)
    (hstaged : ∀ j, j < left.val → ∃ cached,
      pending.staged_slots.val[slot.val + j]! = core.option.Option.Some cached ∧
      cached.sequence.val = expected.val + j ∧
      pending.committed_control.receive_cache.entries.val[slot.val + j]! = cached.sequence) :
    pending_receive_slots_are_valid state pending slot expected left = ok true :=
  pending_receive_slots_are_valid_loop_true state pending left.val slot expected left rfl
    hcap hlen hseq hempty hstaged

/-- A bounded empty material window passes destination validation. -/
theorem refined_receive_slots_are_empty_loop_true
    (state : RefinedRatchet SendChain ReceiveChain Material) (n : Nat) :
    ∀ (slot left : Std.U8), left.val = n → slot.val + left.val ≤ 50 →
      (∀ i, slot.val ≤ i → i < slot.val + left.val →
        state.receive_slots.val[i]! = core.option.Option.None) →
      refined_receive_slots_are_empty_loop state slot left = ok true := by
  induction n with
  | zero =>
    intro slot left hleft hcap hempty
    simp only [refined_receive_slots_are_empty_loop, loop.eq_def,
      refined_receive_slots_are_empty_loop.body, if_neg (by scalar_tac : ¬left > 0#u8)]
  | succ n ih =>
    intro slot left hleft hcap hempty
    rw [refined_receive_slots_are_empty_loop, loop.eq_def]
    simp only [refined_receive_slots_are_empty_loop.body, if_pos (by scalar_tac : left > 0#u8),
      lift, capacity_eq_ok, bind_tc_ok,
      if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
      array_index_bang state.receive_slots (UScalar.cast UScalarTy.Usize slot) (by scalar_tac),
      show (UScalar.cast UScalarTy.Usize slot).val = slot.val by simp_scalar,
      hempty slot.val (by omega) (by omega), core.option.Option.is_some,
      Std.core.option.Option.is_some, Option.isSome, core.option.Option.None, Bool.false_eq_true, if_false]
    obtain ⟨slot', hslot, hslotval⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
    obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
    have hrun := ih slot' left' (by scalar_tac) (by scalar_tac)
      (fun i hi hj => hempty i (by scalar_tac) (by scalar_tac))
    simp only [refined_receive_slots_are_empty_loop, refined_receive_slots_are_empty_loop.body,
      lift, capacity_eq_ok, core.option.Option.is_some, Std.core.option.Option.is_some, Option.isSome,
      bind_tc_ok] at hrun
    simpa only [hslot, hnext, bind_tc_ok] using hrun

/-- The public destination validator accepts bounded empty windows. -/
theorem refined_receive_slots_are_empty_true
    (state : RefinedRatchet SendChain ReceiveChain Material) (slot left : Std.U8)
    (hcap : slot.val + left.val ≤ 50)
    (hempty : ∀ i, slot.val ≤ i → i < slot.val + left.val →
      state.receive_slots.val[i]! = core.option.Option.None) :
    refined_receive_slots_are_empty state slot left = ok true :=
  refined_receive_slots_are_empty_loop_true state left.val slot left rfl hcap hempty

/-- Equal bounded logical cache windows pass prefix validation. -/
theorem receive_control_prefix_matches_loop_true
    (entry committed : ratchet.control.RatchetState) (n : Nat) :
    ∀ (slot left : Std.U8), left.val = n → slot.val + left.val ≤ 50 →
      slot.val + left.val ≤ entry.receive_cache.len.val →
      slot.val + left.val ≤ committed.receive_cache.len.val →
      (∀ i, slot.val ≤ i → i < slot.val + left.val →
        entry.receive_cache.entries.val[i]! = committed.receive_cache.entries.val[i]!) →
      receive_control_prefix_matches_loop entry committed slot left = ok true := by
  induction n with
  | zero =>
    intro slot left hleft hcap hentry hcommitted hmatch
    simp only [receive_control_prefix_matches_loop, loop.eq_def,
      receive_control_prefix_matches_loop.body, if_neg (by scalar_tac : ¬left > 0#u8)]
  | succ n ih =>
    intro slot left hleft hcap hentry hcommitted hmatch
    rw [receive_control_prefix_matches_loop, loop.eq_def]
    simp only [receive_control_prefix_matches_loop.body, if_pos (by scalar_tac : left > 0#u8),
      lift, capacity_eq_ok, bind_tc_ok,
      if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
      receive_key_at_exact entry slot (by omega) (by omega),
      receive_key_at_exact committed slot (by omega) (by omega),
      hmatch slot.val (by omega) (by omega), core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64, beq_self_eq_true, if_true]
    obtain ⟨slot', hslot, hslotval⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
    obtain ⟨left', hnext, hnextval⟩ := uscalar_sub_eq_ok left 1#u8 (by scalar_tac)
    have hrun := ih slot' left' (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
      (fun i hi hj => hmatch i (by scalar_tac) (by scalar_tac))
    simp only [receive_control_prefix_matches_loop, receive_control_prefix_matches_loop.body,
      lift, capacity_eq_ok, bind_tc_ok, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64] at hrun
    simpa only [hslot, hnext, bind_tc_ok] using hrun

/-- The public prefix validator accepts equal bounded logical cache windows. -/
theorem receive_control_prefix_matches_true
    (entry committed : ratchet.control.RatchetState) (slot left : Std.U8)
    (hcap : slot.val + left.val ≤ 50)
    (hentry : slot.val + left.val ≤ entry.receive_cache.len.val)
    (hcommitted : slot.val + left.val ≤ committed.receive_cache.len.val)
    (hmatch : ∀ i, slot.val ≤ i → i < slot.val + left.val →
      entry.receive_cache.entries.val[i]! = committed.receive_cache.entries.val[i]!) :
    receive_control_prefix_matches entry committed slot left = ok true :=
  receive_control_prefix_matches_loop_true entry committed left.val slot left rfl
    hcap hentry hcommitted hmatch

/-- A future receive record satisfying the concrete control and staged-material invariants passes all publication checks. -/
theorem pending_receive_is_valid_true
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) (requested : Std.U64)
    (htarget : pending.target_sequence = requested)
    (hfuture : state.control.receive_sequence.val < requested.val)
    (hfirst : pending.first_slot = state.control.receive_cache.len)
    (hsend : pending.committed_control.send_sequence = state.control.send_sequence)
    (hreceive : pending.committed_control.receive_sequence = requested)
    (hskip : pending.skipped.val = requested.val - state.control.receive_sequence.val - 1)
    (hcap : pending.first_slot.val + pending.skipped.val ≤ 50)
    (hlen : pending.committed_control.receive_cache.len.val = pending.first_slot.val + pending.skipped.val)
    (hlookup : lookup_receive_key pending.committed_control requested = ok core.option.Option.None)
    (hprefix : ∀ i, i < pending.first_slot.val →
      pending.committed_control.receive_cache.entries.val[i]! = state.control.receive_cache.entries.val[i]!)
    (hempty : ∀ i, pending.first_slot.val ≤ i → i < 50 →
      state.receive_slots.val[i]! = core.option.Option.None)
    (hstaged_empty : ∀ i, i < 50 → pending.first_slot.val + pending.skipped.val ≤ i →
      pending.staged_slots.val[i]! = core.option.Option.None)
    (hstaged : ∀ j, j < pending.skipped.val → ∃ cached,
      pending.staged_slots.val[pending.first_slot.val + j]! = core.option.Option.Some cached ∧
      cached.sequence.val = state.control.receive_sequence.val + j + 1 ∧
      pending.committed_control.receive_cache.entries.val[pending.first_slot.val + j]! = cached.sequence) :
    pending_receive_is_valid state pending requested = ok true := by
  simp only [pending_receive_is_valid, RatchetState.impl.receive_sequence, RatchetState.impl.send_sequence,
    RatchetState.receive_cache_len, bind_tc_ok, htarget, if_true,
    if_neg (by scalar_tac : ¬requested ≤ state.control.receive_sequence), hfirst, hsend, hreceive]
  obtain ⟨gap, hgap, hgapval⟩ := uscalar_sub_eq_ok requested state.control.receive_sequence (by scalar_tac)
  obtain ⟨steps, hsteps, hstepsval⟩ := uscalar_add_eq_ok (UScalar.cast UScalarTy.U64 pending.skipped) 1#u64 (by scalar_tac)
  simp only [hgap, lift, bind_tc_ok, hsteps, if_pos (by scalar_tac : gap = steps), hlookup,
    core.option.Option.is_some, Std.core.option.Option.is_some, Option.isSome,
    core.option.Option.None, Bool.false_eq_true, if_false]
  obtain ⟨last, hlast, hlastval⟩ := uscalar_add_eq_ok (UScalar.cast UScalarTy.Usize state.control.receive_cache.len)
    (UScalar.cast UScalarTy.Usize pending.skipped) (by scalar_tac)
  have hprefix_ok := receive_control_prefix_matches_true state.control pending.committed_control
    0#u8 state.control.receive_cache.len (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (fun i hi hj => (hprefix i (by scalar_tac)).symm)
  simp only [hlast, capacity_eq_ok, bind_tc_ok,
    if_neg (by scalar_tac : ¬last > UScalar.cast UScalarTy.Usize 50#u64),
    if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize pending.committed_control.receive_cache.len = last),
    hprefix_ok, if_true]
  obtain ⟨expected, hexpected, hexpectedval⟩ := uscalar_add_eq_ok state.control.receive_sequence 1#u64 (by scalar_tac)
  have hstaged_ok := pending_receive_slots_are_valid_true state pending pending.first_slot expected pending.skipped
    hcap (by omega) (by scalar_tac)
    (fun i hi hj => hempty i hi (by omega)) (by
      intro j hj
      obtain ⟨cached, hcached, hsequence, hlogical⟩ := hstaged j hj
      exact ⟨cached, hcached, by scalar_tac, hlogical⟩)
  by_cases hlastcap : last < UScalar.cast UScalarTy.Usize 50#u64
  · simp only [if_pos hlastcap,
      array_index_bang state.receive_slots last (by scalar_tac),
      array_index_bang pending.staged_slots last (by scalar_tac),
      hempty last.val (by scalar_tac) (by scalar_tac),
      hstaged_empty last.val (by scalar_tac) (by scalar_tac),
      bind_tc_ok, core.option.Option.None, if_false, Bool.false_eq_true, hexpected, ←hfirst, hstaged_ok]
  · simp only [if_neg hlastcap, hexpected, bind_tc_ok, ←hfirst, hstaged_ok]

end beaconcrypt_core.ratchet.refined
