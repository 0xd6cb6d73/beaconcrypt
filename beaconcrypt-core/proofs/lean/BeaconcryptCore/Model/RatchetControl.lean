import BeaconcryptCore.Extraction.Funs

/-!
# Verification of the symmetric single ratchet control plane

This file proves the safety properties of the ratchet control state machine that is
extracted from `beaconcrypt-core/src/ratchet/control.rs` by Aeneas
(`BeaconcryptCore/Extraction/Funs.lean`).

The control plane tracks, for one symmetric ratchet:

* `send_sequence`   – the number of messages sent so far,
* `receive_sequence` – the highest message index whose key has been derived,
* `receive_cache`   – the store of derived-but-not-yet-consumed ("skipped") message
  keys, represented by their sequence numbers, of capacity
  `RATCHET_MAX_GAP = 50`.

The properties proved here are:

* **The bound of 50 skipped messages.**  The receive cache never holds more than 50
  entries (`SequenceCache.append_len_le`, `advance_receive_wf`), a message that would
  require more than 50 key derivations is refused by the planner
  (`plan_receive_until_reject_of_gap_gt`, `plan_receive_until_reject_51`), and so is a
  message whose derivations would push the number of outstanding skipped keys past 50
  (`plan_receive_until_reject_of_cache_full`).
* **State neutrality on authentication failure.**  `finish_receive` is the step that is
  told whether the authenticated decryption of the incoming message succeeded.  If it
  did not, the ratchet state is returned bit-for-bit unchanged and no cache entry is
  removed (`finish_receive_auth_fail_state_neutral`,
  `finish_receive_with_removal_auth_fail`).  The same holds for a message whose key is
  not (or no longer) in the cache (`finish_receive_missing_state_neutral`).
* **Every rejection is state neutral.**  Whenever the planner or the key-derivation
  step refuses a message, the state it returns is the state it was given
  (`advance_receive_reject_state_neutral`); the planner itself carries no state and
  schedules no key derivation when it refuses a message
  (`plan_receive_until_reject_of_gap_gt`, `plan_receive_until_reject_of_cache_full`).
* **Consumption.**  On successful authentication the key is removed from the cache by a
  swap-remove, decreasing the number of outstanding keys by exactly one
  (`finish_receive_consumed`), so a replayed message can no longer be delivered
  (`lookup_receive_key_consumed_absent`).
* **Totality.**  None of the control-plane functions can panic or overflow: each of
  them returns `ok` on every well-formed state (`advance_receive_ok`,
  `finish_receive_with_removal_ok`, `lookup_receive_key_ok`, ...).

The restore path and the per-peer wrappers are verified in
`BeaconcryptCore/RatchetControlRestore.lean`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result

namespace beaconcrypt_core.ratchet.control

/-! ## Basic facts about the capacity constants -/

/-- The receive-cache capacity is the maximum gap, `50`. -/
theorem capacity_eq_ok :
    RECEIVE_CACHE_CAPACITY = ok (UScalar.cast UScalarTy.Usize 50#u64) := by
  simp [RECEIVE_CACHE_CAPACITY, RATCHET_MAX_GAP]

@[simp, scalar_tac_simps]
theorem capacity_val : (UScalar.cast UScalarTy.Usize 50#u64).val = 50 := by
  simp_scalar

/-- The maximum gap tolerated on the receive path is 50 messages. -/
theorem max_gap_eq : RATCHET_MAX_GAP = 50#u64 := by
  simp [RATCHET_MAX_GAP]

@[simp, scalar_tac_simps]
theorem max_gap_val : (RATCHET_MAX_GAP).val = 50 := by
  simp [RATCHET_MAX_GAP]

/-- `50` fits in a `usize` on every supported platform. -/
@[simp, scalar_tac_simps]
theorem fifty_mod_pow_numBits : (50 : Nat) % 2 ^ System.Platform.numBits = 50 := by
  have := capacity_val
  simpa [UScalar.cast_val_eq] using this

/-- Writing into an array in bounds succeeds and performs the expected update. -/
theorem array_update_eq_ok {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (x : α) (h : i.val < v.length) : v.update i x = ok (v.set i x) := by
  unfold Std.Array.update
  rw [Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem (by simpa using h)]
  rfl

/-- An addition that does not overflow succeeds. -/
theorem uscalar_add_eq_ok {ty : UScalarTy} (x y : UScalar ty)
    (h : x.val + y.val ≤ UScalar.max ty) :
    ∃ z : UScalar ty, x + y = ok z ∧ z.val = x.val + y.val := by
  have h' := UScalar.add_equiv x y
  cases hxy : x + y with
  | ok z => rw [hxy] at h'; exact ⟨z, rfl, h'.2.1⟩
  | fail e =>
    rw [hxy] at h'
    rw [UScalar.max_def] at h
    have : 0 < 2 ^ ty.numBits := Nat.two_pow_pos _
    simp [UScalar.inBounds] at h'
    omega
  | div => rw [hxy] at h'; exact h'.elim

/-- A subtraction that does not underflow succeeds. -/
theorem uscalar_sub_eq_ok {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≤ x.val) :
    ∃ z : UScalar ty, x - y = ok z ∧ z.val = x.val - y.val := by
  have h' := UScalar.sub_equiv x y
  cases hxy : x - y with
  | ok z => rw [hxy] at h'; exact ⟨z, rfl, by omega⟩
  | fail e => rw [hxy] at h'; omega
  | div => rw [hxy] at h'; exact h'.elim

/-- Reading an array in bounds succeeds and returns the expected element. -/
theorem array_index_eq_ok {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (h : i.val < v.length) : v.index_usize i = ok v.val[i.val] := by
  unfold Std.Array.index_usize
  rw [Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem (by simpa using h)]

/-! ## Well-formedness

A ratchet state is well formed when its receive cache holds at most
`RATCHET_MAX_GAP = 50` outstanding skipped keys. -/

/-- At most 50 outstanding skipped-message keys. -/
def SequenceCache.Wf (c : SequenceCache) : Prop := c.len.val ≤ 50

/-- At most 50 outstanding skipped-message keys on the receive path. -/
def RatchetState.Wf (st : RatchetState) : Prop := st.receive_cache.Wf

theorem SequenceCache.empty_wf : ∃ c, SequenceCache.empty = ok c ∧ c.Wf ∧ c.len.val = 0 := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp [SequenceCache.Wf]

theorem RatchetState.new_wf (s : Std.U64) :
    ∃ st, RatchetState.new s = ok st ∧ st.Wf ∧ st.send_sequence = s ∧
      st.receive_sequence.val = 0 := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩ <;> simp [RatchetState.Wf, SequenceCache.Wf]

/-! ## The skipped-key cache -/

/-- Sequence number `0` is never cached (it is not a valid message index). -/
theorem SequenceCache.append_zero (c : SequenceCache) :
    SequenceCache.append c 0#u64 = ok core.option.Option.None := by
  simp [SequenceCache.append]

/-- A full cache (50 outstanding skipped keys) refuses to store another key. -/
theorem SequenceCache.append_eq_none_of_full (c : SequenceCache) (s : Std.U64)
    (h : 50 ≤ c.len.val) :
    SequenceCache.append c s = ok core.option.Option.None := by
  simp [SequenceCache.append, capacity_eq_ok, lift]
  intro _ hlt
  exfalso
  scalar_tac

/-- Below the bound of 50, a key is appended at the first free slot, and the number of
outstanding keys grows by exactly one. -/
theorem SequenceCache.append_ok (c : SequenceCache) (s : Std.U64)
    (hs : s.val ≠ 0) (hlen : c.len.val < 50) :
    ∃ c', SequenceCache.append c s = ok (core.option.Option.Some (c', c.len)) ∧
      c'.len.val = c.len.val + 1 ∧ c'.entries = c.entries.set (UScalar.cast .Usize c.len) s := by
  have hidx : (UScalar.cast UScalarTy.Usize c.len).val < c.entries.length := by
    simp_scalar
  have hupd := array_update_eq_ok c.entries (UScalar.cast UScalarTy.Usize c.len) s hidx
  obtain ⟨z, hz, hzval⟩ := uscalar_add_eq_ok c.len 1#u8 (by scalar_tac)
  refine ⟨{ entries := c.entries.set (UScalar.cast UScalarTy.Usize c.len) s, len := z },
    ?_, ?_, rfl⟩
  · simp [SequenceCache.append, capacity_eq_ok, lift, hupd, hs, hlen, hz]
  · simpa using hzval

/-- Appending never takes the cache beyond 50 entries. -/
theorem SequenceCache.append_len_le (c : SequenceCache) (s : Std.U64) (c' : SequenceCache)
    (slot : Std.U8)
    (h : SequenceCache.append c s = ok (core.option.Option.Some (c', slot))) :
    c'.Wf := by
  by_cases hfull : 50 ≤ c.len.val
  · rw [SequenceCache.append_eq_none_of_full c s hfull] at h
    simp at h
  · by_cases hs : s.val = 0
    · have hs0 : s = 0#u64 := by scalar_tac
      rw [hs0, SequenceCache.append_zero] at h
      simp at h
    · obtain ⟨c'', h'', hlen'', _⟩ := SequenceCache.append_ok c s hs (by omega)
      rw [h''] at h
      simp at h
      obtain ⟨hc, -⟩ := h
      subst hc
      simp only [SequenceCache.Wf]
      omega

/-- Appending to the cache never fails. -/
theorem SequenceCache.append_total (c : SequenceCache) (s : Std.U64) :
    ∃ o, SequenceCache.append c s = ok o := by
  by_cases hs : s.val = 0
  · have hs0 : s = 0#u64 := by scalar_tac
    exact ⟨_, by rw [hs0, SequenceCache.append_zero]⟩
  · by_cases hfull : 50 ≤ c.len.val
    · exact ⟨_, SequenceCache.append_eq_none_of_full c s hfull⟩
    · obtain ⟨c', h', -⟩ := SequenceCache.append_ok c s hs (by omega)
      exact ⟨_, h'⟩

/-! ## The send path -/

/-- At the very end of the sequence space no key is handed out and the state is
unchanged. -/
theorem advance_send_max (st : RatchetState) (h : st.send_sequence = core.num.U64.MAX) :
    advance_send st =
      ok { state := st, sequence := core.option.Option.None,
           key := { sequence := 0#u64, available := false } } := by
  simp [advance_send, SendKey.unavailable, h]

/-- Otherwise the send counter increases by exactly one and the key handed out is the
key of the new sequence number. -/
theorem advance_send_ok (st : RatchetState) (h : st.send_sequence ≠ core.num.U64.MAX) :
    ∃ adv, advance_send st = ok adv ∧
      adv.state.send_sequence.val = st.send_sequence.val + 1 ∧
      adv.state.receive_sequence = st.receive_sequence ∧
      adv.state.receive_cache = st.receive_cache ∧
      adv.sequence = core.option.Option.Some adv.state.send_sequence ∧
      adv.key = { sequence := adv.state.send_sequence, available := true } := by
  have hval : st.send_sequence.val ≠ (core.num.U64.MAX).val := fun hc =>
    h (UScalar.eq_of_val_eq hc)
  simp [core.num.U64.MAX, U64.rMax] at hval
  obtain ⟨z, hz, hzval⟩ := uscalar_add_eq_ok st.send_sequence 1#u64 (by scalar_tac)
  have heq : advance_send st =
      ok { state := { st with send_sequence := z },
           sequence := core.option.Option.Some z,
           key := { sequence := z, available := true } } := by
    simp [advance_send, h, hz]
  exact ⟨_, heq, by simpa using hzval, rfl, rfl, rfl, rfl⟩

/-- A send key can be consumed only once: consuming it marks it unavailable. -/
theorem finish_send_available (key : SendKey) (h : key.available) :
    finish_send key = ok { key := { key with available := false }, consumed := true } := by
  simp [finish_send, h]

/-- Consuming an already-used key is a no-op. -/
theorem finish_send_unavailable (key : SendKey) (h : ¬ key.available) :
    finish_send key = ok { key := key, consumed := false } := by
  simp [finish_send, h]

/-! ## Planning a receive: the bound of 50 skipped messages -/

/-- A message that is not ahead of the receive counter needs no key derivation: it is
either a replay or a message whose key is already cached. -/
theorem plan_receive_until_replay (st : RatchetState) (target : Std.U64)
    (h : target.val ≤ st.receive_sequence.val) :
    plan_receive_until st target =
      ok { sequence := core.option.Option.Some target, derivations := 0#u64 } := by
  have hle : target ≤ st.receive_sequence := by scalar_tac
  simp [plan_receive_until, hle]

/-- A message more than 50 sequence numbers ahead of the receive counter is refused. -/
theorem plan_receive_until_reject_of_gap_gt (st : RatchetState) (target : Std.U64)
    (h : st.receive_sequence.val + 50 < target.val) :
    plan_receive_until st target =
      ok { sequence := core.option.Option.None, derivations := 0#u64 } := by
  have hgt : ¬ (target ≤ st.receive_sequence) := by scalar_tac
  obtain ⟨d, hd, hdval⟩ := uscalar_sub_eq_ok target st.receive_sequence (by scalar_tac)
  simp [plan_receive_until, hgt, hd, lift]
  exact fun hcon => absurd hcon (by omega)

/-- A message whose delivery would push the number of outstanding skipped keys past 50
is refused. -/
theorem plan_receive_until_reject_of_cache_full (st : RatchetState) (target : Std.U64)
    (hgt : st.receive_sequence.val < target.val)
    (hgap : target.val ≤ st.receive_sequence.val + 50)
    (hfull : 50 < st.receive_cache.len.val + (target.val - st.receive_sequence.val)) :
    plan_receive_until st target =
      ok { sequence := core.option.Option.None, derivations := 0#u64 } := by
  have hgt : ¬ (target ≤ st.receive_sequence) := by scalar_tac
  obtain ⟨d, hd, hdval⟩ := uscalar_sub_eq_ok target st.receive_sequence (by scalar_tac)
  obtain ⟨i, hi, hival⟩ := uscalar_sub_eq_ok RATCHET_MAX_GAP d (by scalar_tac)
  simp [plan_receive_until, hgt, hd, lift, hi]
  intro _
  scalar_tac

/-- Within the bound the plan accepts the message and asks for exactly the missing
key derivations. -/
theorem plan_receive_until_accept (st : RatchetState) (target : Std.U64)
    (hgt : st.receive_sequence.val < target.val)
    (hbound : st.receive_cache.len.val + (target.val - st.receive_sequence.val) ≤ 50) :
    ∃ d : Std.U64, plan_receive_until st target =
      ok { sequence := core.option.Option.Some target, derivations := d } ∧
      d.val = target.val - st.receive_sequence.val := by
  have hgt : ¬ (target ≤ st.receive_sequence) := by scalar_tac
  obtain ⟨d, hd, hdval⟩ := uscalar_sub_eq_ok target st.receive_sequence (by scalar_tac)
  obtain ⟨i, hi, hival⟩ := uscalar_sub_eq_ok RATCHET_MAX_GAP d (by scalar_tac)
  refine ⟨d, ?_, hdval⟩
  simp [plan_receive_until, hgt, hd, lift, hi]
  rw [if_neg (by scalar_tac), if_neg (by scalar_tac)]

/-- Planning never changes the ratchet state, and an accepted plan never asks for more
derivations than the cache can hold: the outstanding skipped keys stay within 50. -/
theorem plan_receive_until_bound (st : RatchetState) (target : Std.U64) (p : ReceivePlan)
    (hst : st.Wf) (h : plan_receive_until st target = ok p)
    (hsome : p.sequence = core.option.Option.Some target) :
    p.derivations.val ≤ 50 ∧
      st.receive_cache.len.val + p.derivations.val ≤ 50 ∧
      st.receive_sequence.val + p.derivations.val = max st.receive_sequence.val target.val := by
  simp only [RatchetState.Wf, SequenceCache.Wf] at hst
  by_cases hle : target.val ≤ st.receive_sequence.val
  · rw [plan_receive_until_replay st target hle] at h
    simp at h
    subst h
    refine ⟨by simp, by simpa using hst, ?_⟩
    simp
    omega
  · by_cases hbound : st.receive_cache.len.val + (target.val - st.receive_sequence.val) ≤ 50
    · obtain ⟨d, hd, hdval⟩ := plan_receive_until_accept st target (by omega) hbound
      rw [hd] at h
      simp at h
      subst h
      refine ⟨by simpa using by omega, by simpa using by omega, ?_⟩
      simp only []
      omega
    · by_cases hgap : st.receive_sequence.val + 50 < target.val
      · rw [plan_receive_until_reject_of_gap_gt st target hgap] at h
        simp at h
        subst h
        simp at hsome
      · rw [plan_receive_until_reject_of_cache_full st target (by omega) (by omega)
          (by omega)] at h
        simp at h
        subst h
        simp at hsome

/-- The concrete bound: a message 51 ahead of the receive counter is always refused,
whatever the state of the cache. -/
theorem plan_receive_until_reject_51 (st : RatchetState) (target : Std.U64)
    (h : target.val = st.receive_sequence.val + 51) :
    plan_receive_until st target =
      ok { sequence := core.option.Option.None, derivations := 0#u64 } := by
  exact plan_receive_until_reject_of_gap_gt st target (by omega)

/-! ## Deriving the next receive key -/

/-- The receive counter can be incremented unless it has reached the end of the
sequence space. -/
theorem receive_next_ok (st : RatchetState) (hmax : st.receive_sequence ≠ core.num.U64.MAX) :
    ∃ z, st.receive_sequence + 1#u64 = ok z ∧ z.val = st.receive_sequence.val + 1 := by
  have hval : st.receive_sequence.val ≠ (core.num.U64.MAX).val := fun hc =>
    hmax (UScalar.eq_of_val_eq hc)
  simp [core.num.U64.MAX, U64.rMax] at hval
  obtain ⟨z, hz, hzval⟩ := uscalar_add_eq_ok st.receive_sequence 1#u64 (by scalar_tac)
  exact ⟨z, hz, by simpa using hzval⟩

/-- At the end of the sequence space no further key is derived. -/
theorem advance_receive_max (st : RatchetState) (hmax : st.receive_sequence = core.num.U64.MAX) :
    advance_receive st =
      ok { state := st, sequence := core.option.Option.None,
           slot := core.option.Option.None } := by
  simp [advance_receive, hmax]

/-- If the cache refuses the new key, the state is left untouched. -/
theorem advance_receive_of_append_none (st : RatchetState)
    (hmax : st.receive_sequence ≠ core.num.U64.MAX) (z : Std.U64)
    (hz : st.receive_sequence + 1#u64 = ok z)
    (ho : st.receive_cache.append z = ok core.option.Option.None) :
    advance_receive st =
      ok { state := st, sequence := core.option.Option.None,
           slot := core.option.Option.None } := by
  simp [advance_receive, hmax, hz, ho]

/-- If the cache accepts the new key, the receive counter and the cache move on. -/
theorem advance_receive_of_append_some (st : RatchetState)
    (hmax : st.receive_sequence ≠ core.num.U64.MAX) (z : Std.U64)
    (hz : st.receive_sequence + 1#u64 = ok z) (c' : SequenceCache) (slot : Std.U8)
    (ho : st.receive_cache.append z = ok (core.option.Option.Some (c', slot))) :
    advance_receive st =
      ok { state := { st with receive_sequence := z, receive_cache := c' },
           sequence := core.option.Option.Some z,
           slot := core.option.Option.Some slot } := by
  simp [advance_receive, hmax, hz, ho]

/-- Advancing the receive chain never fails. -/
theorem advance_receive_ok (st : RatchetState) :
    ∃ adv, advance_receive st = ok adv := by
  by_cases hmax : st.receive_sequence = core.num.U64.MAX
  · exact ⟨_, advance_receive_max st hmax⟩
  · obtain ⟨z, hz, -⟩ := receive_next_ok st hmax
    obtain ⟨o, ho⟩ := SequenceCache.append_total st.receive_cache z
    cases o with
    | none => exact ⟨_, advance_receive_of_append_none st hmax z hz ho⟩
    | some p => exact ⟨_, advance_receive_of_append_some st hmax z hz p.1 p.2 ho⟩

/-- If the derivation step refuses (end of the sequence space, or a full cache), the
state is returned unchanged. -/
theorem advance_receive_reject_state_neutral (st : RatchetState) (adv : ReceiveAdvance)
    (h : advance_receive st = ok adv) (hnone : adv.sequence = core.option.Option.None) :
    adv.state = st ∧ adv.slot = core.option.Option.None := by
  by_cases hmax : st.receive_sequence = core.num.U64.MAX
  · rw [advance_receive_max st hmax] at h
    simp at h
    subst h
    exact ⟨rfl, rfl⟩
  · obtain ⟨z, hz, -⟩ := receive_next_ok st hmax
    obtain ⟨o, ho⟩ := SequenceCache.append_total st.receive_cache z
    cases o with
    | none =>
      rw [advance_receive_of_append_none st hmax z hz ho] at h
      simp at h
      subst h
      exact ⟨rfl, rfl⟩
    | some p =>
      rw [advance_receive_of_append_some st hmax z hz p.1 p.2 ho] at h
      simp at h
      subst h
      simp at hnone

/-- A full cache refuses to derive a further key, leaving the state unchanged. -/
theorem advance_receive_full (st : RatchetState) (h : 50 ≤ st.receive_cache.len.val) :
    advance_receive st =
      ok { state := st, sequence := core.option.Option.None,
           slot := core.option.Option.None } := by
  by_cases hmax : st.receive_sequence = core.num.U64.MAX
  · exact advance_receive_max st hmax
  · obtain ⟨z, hz, -⟩ := receive_next_ok st hmax
    exact advance_receive_of_append_none st hmax z hz
      (SequenceCache.append_eq_none_of_full _ _ h)

/-- Below the bound, one key is derived: the receive counter moves up by one and the
key is stored in the first free cache slot. -/
theorem advance_receive_step (st : RatchetState)
    (hmax : st.receive_sequence ≠ core.num.U64.MAX)
    (hlen : st.receive_cache.len.val < 50) :
    ∃ adv, advance_receive st = ok adv ∧
      adv.state.receive_sequence.val = st.receive_sequence.val + 1 ∧
      adv.state.send_sequence = st.send_sequence ∧
      adv.state.receive_cache.len.val = st.receive_cache.len.val + 1 ∧
      adv.sequence = core.option.Option.Some adv.state.receive_sequence ∧
      adv.slot = core.option.Option.Some st.receive_cache.len := by
  obtain ⟨z, hz, hzval⟩ := receive_next_ok st hmax
  obtain ⟨c', hc', hc'len, -⟩ :=
    SequenceCache.append_ok st.receive_cache z (by scalar_tac) hlen
  exact ⟨_, advance_receive_of_append_some st hmax z hz c' st.receive_cache.len hc',
    hzval, rfl, hc'len, rfl, rfl⟩

/-- Deriving a key preserves the bound of 50 outstanding skipped keys. -/
theorem advance_receive_wf (st : RatchetState) (hst : st.Wf) (adv : ReceiveAdvance)
    (h : advance_receive st = ok adv) : adv.state.Wf := by
  by_cases hmax : st.receive_sequence = core.num.U64.MAX
  · rw [advance_receive_max st hmax] at h
    simp at h
    subst h
    exact hst
  · obtain ⟨z, hz, -⟩ := receive_next_ok st hmax
    obtain ⟨o, ho⟩ := SequenceCache.append_total st.receive_cache z
    cases o with
    | none =>
      rw [advance_receive_of_append_none st hmax z hz ho] at h
      simp at h
      subst h
      exact hst
    | some p =>
      rw [advance_receive_of_append_some st hmax z hz p.1 p.2 ho] at h
      simp at h
      subst h
      exact SequenceCache.append_len_le _ _ _ _ ho

/-- Reading a cache slot below the capacity succeeds. -/
theorem entries_index_eq_ok (c : SequenceCache) (i : Std.U8) (h : i.val < 50) :
    c.entries.index_usize (UScalar.cast UScalarTy.Usize i) = ok c.entries.val[i.val]! := by
  have hidx : (UScalar.cast UScalarTy.Usize i).val < c.entries.length := by
    simp_scalar
  rw [array_index_eq_ok _ _ hidx]
  have hcast : (UScalar.cast UScalarTy.Usize i).val = i.val := by simp_scalar
  have hlt : i.val < (c.entries.val).length := by simp; exact h
  simp [hcast, List.getElem?_eq_getElem hlt]

/-! ## Looking up a cached key -/

/-- The lookup loop, which scans the cache from `slot` upwards for at most `remaining`
steps, always terminates successfully; a hit points at a live slot holding the requested
sequence number, and a miss means no live slot in the scanned window holds it. -/
theorem lookup_receive_key_from_spec (st : RatchetState) (sequence : Std.U64) (hst : st.Wf) :
    ∀ (n : Nat) (slot remaining : Std.U8), remaining.val = n →
    ∃ r, lookup_receive_key_from st sequence slot remaining = ok r ∧
      (∀ j, r = core.option.Option.Some j →
        slot.val ≤ j.val ∧ j.val < st.receive_cache.len.val ∧
        st.receive_cache.entries.val[j.val]! = sequence) ∧
      (r = core.option.Option.None →
        ∀ i, slot.val ≤ i → i < st.receive_cache.len.val → i < slot.val + n →
          st.receive_cache.entries.val[i]! ≠ sequence) := by
  simp only [RatchetState.Wf, SequenceCache.Wf] at hst
  intro n
  induction n with
  | zero =>
    intro slot remaining hrem
    have : remaining = 0#u8 := by scalar_tac
    subst this
    refine ⟨core.option.Option.None, ?_, by simp, ?_⟩
    · rw [lookup_receive_key_from.eq_def]; simp
    · intro _ i h1 _ h3; omega
  | succ m ih =>
    intro slot remaining hrem
    have hne : remaining ≠ 0#u8 := by scalar_tac
    rw [lookup_receive_key_from.eq_def]
    simp only [hne, if_false, capacity_eq_ok, lift, bind_tc_ok]
    by_cases hcap : 50 ≤ slot.val
    · rw [if_pos (by scalar_tac)]
      exact ⟨_, rfl, by simp, by intro _ i h1 h2 h3; omega⟩
    · rw [if_neg (by scalar_tac)]
      by_cases hlen : st.receive_cache.len.val ≤ slot.val
      · rw [if_pos (by scalar_tac)]
        exact ⟨_, rfl, by simp, by intro _ i h1 h2 h3; omega⟩
      · rw [if_neg (by scalar_tac)]
        rw [entries_index_eq_ok st.receive_cache slot (by omega)]
        simp only [bind_tc_ok]
        by_cases hhit : st.receive_cache.entries.val[slot.val]! = sequence
        · rw [if_pos hhit]
          refine ⟨_, rfl, ?_, by simp⟩
          rintro j hj
          cases hj
          exact ⟨le_refl _, by omega, hhit⟩
        · rw [if_neg hhit]
          obtain ⟨slot', hslot', hslot'val⟩ := uscalar_add_eq_ok slot 1#u8 (by scalar_tac)
          obtain ⟨rem', hrem', hrem'val⟩ := uscalar_sub_eq_ok remaining 1#u8 (by scalar_tac)
          rw [hslot', hrem']
          simp only [bind_tc_ok]
          have hslot'v : slot'.val = slot.val + 1 := by simpa using hslot'val
          have hrem'v : rem'.val = m := by simp at hrem'val; omega
          obtain ⟨r, hr, hsound, hnone⟩ := ih slot' rem' hrem'v
          refine ⟨r, hr, ?_, ?_⟩
          · intro j hj
            obtain ⟨h1, h2, h3⟩ := hsound j hj
            exact ⟨by omega, h2, h3⟩
          · intro hrn i h1 h2 h3
            rcases Nat.eq_or_lt_of_le h1 with heq | hlt
            · rw [← heq]; exact hhit
            · exact hnone hrn i (by omega) h2 (by omega)

/-- A lookup scans the whole cache: 50 slots starting at slot `0`. -/
theorem lookup_receive_key_unfold (st : RatchetState) (sequence : Std.U64) :
    lookup_receive_key st sequence = lookup_receive_key_from st sequence 0#u8 50#u8 := by
  have hcast : (UScalar.cast UScalarTy.U8 (UScalar.cast UScalarTy.Usize 50#u64)) = 50#u8 := by
    apply UScalar.eq_of_val_eq; simp_scalar
  simp [lookup_receive_key, capacity_eq_ok, lift, hcast]

/-- Looking up a key never fails. -/
theorem lookup_receive_key_ok (st : RatchetState) (sequence : Std.U64) (hst : st.Wf) :
    ∃ r, lookup_receive_key st sequence = ok r := by
  obtain ⟨r, hr, -, -⟩ := lookup_receive_key_from_spec st sequence hst 50 0#u8 50#u8 (by simp)
  exact ⟨r, by rw [lookup_receive_key_unfold]; exact hr⟩

/-- A lookup that succeeds points at a live cache slot that really holds the requested
sequence number. -/
theorem lookup_receive_key_sound (st : RatchetState) (sequence : Std.U64) (slot : Std.U8)
    (hst : st.Wf)
    (h : lookup_receive_key st sequence = ok (core.option.Option.Some slot)) :
    slot.val < st.receive_cache.len.val ∧
      st.receive_cache.entries.val[slot.val]! = sequence := by
  obtain ⟨r, hr, hsound, -⟩ := lookup_receive_key_from_spec st sequence hst 50 0#u8 50#u8 (by simp)
  rw [lookup_receive_key_unfold, hr] at h
  have : r = core.option.Option.Some slot := by simpa using h
  exact ⟨(hsound slot this).2.1, (hsound slot this).2.2⟩

/-- If the key is cached, the lookup finds it. -/
theorem lookup_receive_key_complete (st : RatchetState) (sequence : Std.U64) (i : Nat)
    (hst : st.Wf) (hi : i < st.receive_cache.len.val)
    (hentry : st.receive_cache.entries.val[i]! = sequence) :
    ∃ slot, lookup_receive_key st sequence = ok (core.option.Option.Some slot) ∧
      slot.val < st.receive_cache.len.val ∧
      st.receive_cache.entries.val[slot.val]! = sequence := by
  have hst' : st.receive_cache.len.val ≤ 50 := hst
  obtain ⟨r, hr, hsound, hnone⟩ :=
    lookup_receive_key_from_spec st sequence hst 50 0#u8 50#u8 (by simp)
  cases r with
  | none => exact absurd hentry (hnone rfl i (by simp) hi (by simp; omega))
  | some j =>
    exact ⟨j, by rw [lookup_receive_key_unfold]; exact hr,
      (hsound j rfl).2.1, (hsound j rfl).2.2⟩

/-! ## Finishing a receive: authenticated encryption and state neutrality -/

/-- A cache whose length exceeds the capacity (unreachable from well-formed states)
delivers nothing and changes nothing. -/
theorem finish_receive_with_removal_over_capacity (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) (authenticated : Bool) (h : 50 < st.receive_cache.len.val) :
    finish_receive_with_removal st target slot authenticated =
      ok { state := st, disposition := ReceiveDisposition.Missing,
           removal := core.option.Option.None } := by
  simp [finish_receive_with_removal, lift, capacity_eq_ok]
  exact fun hcon => absurd hcon (by omega)

/-- A slot outside the live part of the cache delivers nothing and changes nothing. -/
theorem finish_receive_with_removal_out_of_range (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) (authenticated : Bool) (h : st.receive_cache.len.val ≤ slot.val) :
    finish_receive_with_removal st target slot authenticated =
      ok { state := st, disposition := ReceiveDisposition.Missing,
           removal := core.option.Option.None } := by
  simp [finish_receive_with_removal, lift, capacity_eq_ok]
  exact fun _ hcon => absurd hcon (by omega)

/-- A slot holding a different sequence number delivers nothing and changes nothing. -/
theorem finish_receive_with_removal_mismatch (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) (authenticated : Bool) (hst : st.Wf)
    (hslot : slot.val < st.receive_cache.len.val)
    (hne : st.receive_cache.entries.val[slot.val]! ≠ target) :
    finish_receive_with_removal st target slot authenticated =
      ok { state := st, disposition := ReceiveDisposition.Missing,
           removal := core.option.Option.None } := by
  simp only [RatchetState.Wf, SequenceCache.Wf] at hst
  simp [finish_receive_with_removal, lift, capacity_eq_ok,
    entries_index_eq_ok st.receive_cache slot (by omega)]
  intro _ _ hcon
  exact absurd hcon (by simpa using hne)

/-- **State neutrality on authentication failure** (cache-level).  When the incoming
message failed authentication, the cached key is retained and the state is unchanged. -/
theorem finish_receive_with_removal_retained (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) (hst : st.Wf) (hslot : slot.val < st.receive_cache.len.val)
    (heq : st.receive_cache.entries.val[slot.val]! = target) :
    finish_receive_with_removal st target slot false =
      ok { state := st, disposition := ReceiveDisposition.Retained,
           removal := core.option.Option.None } := by
  simp only [RatchetState.Wf, SequenceCache.Wf] at hst
  simp [finish_receive_with_removal, lift, capacity_eq_ok,
    entries_index_eq_ok st.receive_cache slot (by omega), heq]
  rw [if_neg (by omega), if_neg (by omega)]

/-- The only state change on the receive-finish step is the consumption of an
authentic message: the key is removed from the cache by a swap-remove and the number of
outstanding skipped keys drops by exactly one. -/
theorem finish_receive_consumed (st : RatchetState) (target : Std.U64) (slot : Std.U8)
    (hst : st.Wf) (hslot : slot.val < st.receive_cache.len.val)
    (hentry : st.receive_cache.entries.val[slot.val]! = target) :
    ∃ r, finish_receive_with_removal st target slot true = ok r ∧
      r.disposition = ReceiveDisposition.Consumed ∧
      r.state.receive_cache.len.val = st.receive_cache.len.val - 1 ∧
      r.state.send_sequence = st.send_sequence ∧
      r.state.receive_sequence = st.receive_sequence ∧
      r.removal = core.option.Option.Some
        { target_slot := slot, last_slot := r.state.receive_cache.len } ∧
      (∀ i, i < r.state.receive_cache.len.val →
        r.state.receive_cache.entries.val[i]! =
          if i = slot.val then
            st.receive_cache.entries.val[st.receive_cache.len.val - 1]!
          else st.receive_cache.entries.val[i]!) := by
  simp only [RatchetState.Wf, SequenceCache.Wf] at hst
  obtain ⟨last, hlast, hlastval⟩ :=
    uscalar_sub_eq_ok st.receive_cache.len 1#u8 (by scalar_tac)
  have hlastval' : last.val = st.receive_cache.len.val - 1 := by simpa using hlastval
  have hread := entries_index_eq_ok st.receive_cache slot (by omega)
  have hread2 := entries_index_eq_ok st.receive_cache last (by omega)
  have hbnd1 : (UScalar.cast UScalarTy.Usize slot).val < st.receive_cache.entries.length := by
    simp_scalar
  have hupd1 := array_update_eq_ok st.receive_cache.entries
    (UScalar.cast UScalarTy.Usize slot) st.receive_cache.entries.val[last.val]! hbnd1
  have hbnd2 : (UScalar.cast UScalarTy.Usize last).val <
      (st.receive_cache.entries.set (UScalar.cast UScalarTy.Usize slot)
        st.receive_cache.entries.val[last.val]!).length := by
    simp_scalar
  have hupd2 := array_update_eq_ok
    (st.receive_cache.entries.set (UScalar.cast UScalarTy.Usize slot)
      st.receive_cache.entries.val[last.val]!)
    (UScalar.cast UScalarTy.Usize last) 0#u64 hbnd2
  have heq : finish_receive_with_removal st target slot true =
      ok { state :=
             { send_sequence := st.send_sequence,
               receive_sequence := st.receive_sequence,
               receive_cache :=
                 { entries :=
                     (st.receive_cache.entries.set (UScalar.cast UScalarTy.Usize slot)
                       st.receive_cache.entries.val[last.val]!).set
                       (UScalar.cast UScalarTy.Usize last) 0#u64,
                   len := last } },
           disposition := ReceiveDisposition.Consumed,
           removal := core.option.Option.Some { target_slot := slot, last_slot := last } } := by
    simp [finish_receive_with_removal, lift, capacity_eq_ok, hread, hentry, hlast,
      hread2]
    rw [if_neg (by omega), if_neg (by omega),
      show ((st.receive_cache.entries.val)[last.val]?.getD default : Std.U64)
        = st.receive_cache.entries.val[last.val]! from
          (List.getElem!_eq_getElem?_getD ..).symm, hupd1]
    simp only [bind_tc_ok]
    rw [hupd2]
    simp only [bind_tc_ok]
  refine ⟨_, heq, rfl, hlastval', rfl, rfl, rfl, ?_⟩
  intro i hi
  simp only at hi
  have hcs : (UScalar.cast UScalarTy.Usize slot).val = slot.val := by simp_scalar
  have hcl : (UScalar.cast UScalarTy.Usize last).val = last.val := by simp_scalar
  simp only [Std.Array.set_val_eq, hcs, hcl, hlastval']
  by_cases hs : i = slot.val
  · subst hs
    simp_lists [hlastval']
  · simp_lists [hs]

/-- Finishing a receive never fails. -/
theorem finish_receive_with_removal_ok (st : RatchetState) (target : Std.U64) (slot : Std.U8)
    (authenticated : Bool) :
    ∃ r, finish_receive_with_removal st target slot authenticated = ok r := by
  by_cases hcap : 50 < st.receive_cache.len.val
  · exact ⟨_, finish_receive_with_removal_over_capacity st target slot authenticated hcap⟩
  · have hwf : st.Wf := by simp only [RatchetState.Wf, SequenceCache.Wf]; omega
    by_cases hslot : slot.val < st.receive_cache.len.val
    · by_cases hentry : st.receive_cache.entries.val[slot.val]! = target
      · cases authenticated with
        | false =>
          exact ⟨_, finish_receive_with_removal_retained st target slot hwf hslot hentry⟩
        | true =>
          obtain ⟨r, hr, -⟩ := finish_receive_consumed st target slot hwf hslot hentry
          exact ⟨r, hr⟩
      · exact ⟨_, finish_receive_with_removal_mismatch st target slot authenticated hwf
          hslot hentry⟩
    · exact ⟨_, finish_receive_with_removal_out_of_range st target slot authenticated
        (by omega)⟩

/-- **State neutrality on authentication failure.**  If the authenticated decryption of
the incoming message failed, the ratchet state is returned unchanged, no cache entry is
removed, and the key stays available for a later, authentic copy of the message. -/
theorem finish_receive_with_removal_auth_fail (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) :
    ∃ r, finish_receive_with_removal st target slot false = ok r ∧ r.state = st ∧
      r.removal = core.option.Option.None ∧
      (r.disposition = ReceiveDisposition.Retained ∨
        r.disposition = ReceiveDisposition.Missing) := by
  by_cases hcap : 50 < st.receive_cache.len.val
  · exact ⟨_, finish_receive_with_removal_over_capacity st target slot false hcap,
      rfl, rfl, Or.inr rfl⟩
  · have hwf : st.Wf := by simp only [RatchetState.Wf, SequenceCache.Wf]; omega
    by_cases hslot : slot.val < st.receive_cache.len.val
    · by_cases hentry : st.receive_cache.entries.val[slot.val]! = target
      · exact ⟨_, finish_receive_with_removal_retained st target slot hwf hslot hentry,
          rfl, rfl, Or.inl rfl⟩
      · exact ⟨_, finish_receive_with_removal_mismatch st target slot false hwf hslot hentry,
          rfl, rfl, Or.inr rfl⟩
    · exact ⟨_, finish_receive_with_removal_out_of_range st target slot false (by omega),
        rfl, rfl, Or.inr rfl⟩

/-- **State neutrality on authentication failure**, for the wrapper used by the
protocol layer. -/
theorem finish_receive_auth_fail_state_neutral (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) :
    ∃ r, finish_receive st target slot false = ok r ∧ r.state = st ∧
      r.disposition ≠ ReceiveDisposition.Consumed := by
  obtain ⟨r, hr, hstate, -, hdisp⟩ := finish_receive_with_removal_auth_fail st target slot
  refine ⟨{ state := r.state, disposition := r.disposition }, ?_, hstate, ?_⟩
  · simp [finish_receive, hr]
  · rcases hdisp with h | h <;> simp [h]

/-- A message whose key is not in the indicated cache slot leaves the state unchanged,
whatever the authentication result. -/
theorem finish_receive_missing_state_neutral (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) (authenticated : Bool)
    (h : slot.val ≥ st.receive_cache.len.val ∨
      st.receive_cache.entries.val[slot.val]! ≠ target) (hst : st.Wf) :
    finish_receive st target slot authenticated =
      ok { state := st, disposition := ReceiveDisposition.Missing } := by
  have hmissing : finish_receive_with_removal st target slot authenticated =
      ok { state := st, disposition := ReceiveDisposition.Missing,
           removal := core.option.Option.None } := by
    by_cases hslot : slot.val < st.receive_cache.len.val
    · have hne : st.receive_cache.entries.val[slot.val]! ≠ target := by
        rcases h with h | h
        · exact absurd hslot (by omega)
        · exact h
      exact finish_receive_with_removal_mismatch st target slot authenticated hst hslot hne
    · exact finish_receive_with_removal_out_of_range st target slot authenticated (by omega)
  simp [finish_receive, hmissing]

/-- Finishing a receive preserves the bound of 50 outstanding skipped keys. -/
theorem finish_receive_wf (st : RatchetState) (target : Std.U64) (slot : Std.U8)
    (authenticated : Bool) (hst : st.Wf) (r : ReceiveFinish)
    (h : finish_receive st target slot authenticated = ok r) : r.state.Wf := by
  by_cases hslot : slot.val < st.receive_cache.len.val
  · by_cases hentry : st.receive_cache.entries.val[slot.val]! = target
    · cases authenticated with
      | false =>
        have he : finish_receive st target slot false =
            ok { state := st, disposition := ReceiveDisposition.Retained } := by
          simp [finish_receive,
            finish_receive_with_removal_retained st target slot hst hslot hentry]
        rw [he] at h
        simp at h
        subst h
        exact hst
      | true =>
        obtain ⟨r', hr', -, hlen, -⟩ := finish_receive_consumed st target slot hst hslot hentry
        have he : finish_receive st target slot true =
            ok { state := r'.state, disposition := r'.disposition } := by
          simp [finish_receive, hr']
        rw [he] at h
        simp at h
        subst h
        simp only [RatchetState.Wf, SequenceCache.Wf] at hst ⊢
        omega
    · rw [finish_receive_missing_state_neutral st target slot authenticated (Or.inr hentry)
        hst] at h
      simp at h
      subst h
      exact hst
  · rw [finish_receive_missing_state_neutral st target slot authenticated
      (Or.inl (by omega)) hst] at h
    simp at h
    subst h
    exact hst

/-- **No replay after consumption.**  If the target sequence number occupies exactly one
live cache slot and an authentic message consumes it, a subsequent lookup of that
sequence number fails: a replayed copy of the message can no longer be delivered. -/
theorem lookup_receive_key_consumed_absent (st : RatchetState) (target : Std.U64)
    (slot : Std.U8) (hst : st.Wf) (hslot : slot.val < st.receive_cache.len.val)
    (hentry : st.receive_cache.entries.val[slot.val]! = target)
    (huniq : ∀ i, i < st.receive_cache.len.val →
      st.receive_cache.entries.val[i]! = target → i = slot.val)
    (r : ReceiveFinishWithRemoval)
    (hr : finish_receive_with_removal st target slot true = ok r) :
    lookup_receive_key r.state target = ok core.option.Option.None := by
  obtain ⟨r', hr', -, hlen, -, -, -, hpt⟩ :=
    finish_receive_consumed st target slot hst hslot hentry
  rw [hr'] at hr
  have hrr : r' = r := by simpa using hr
  subst hrr
  have hst50 : st.receive_cache.len.val ≤ 50 := hst
  have hwf' : r'.state.Wf := by
    simp only [RatchetState.Wf, SequenceCache.Wf]; omega
  obtain ⟨res, hres⟩ := lookup_receive_key_ok r'.state target hwf'
  cases hcase : res with
  | none => rw [hres, hcase]
  | some j =>
    exfalso
    rw [hcase] at hres
    obtain ⟨hj, hjval⟩ := lookup_receive_key_sound r'.state target j hwf' hres
    rw [hpt j.val hj] at hjval
    by_cases hs : j.val = slot.val
    · rw [if_pos hs] at hjval
      have hu := huniq (st.receive_cache.len.val - 1) (by omega) hjval
      omega
    · rw [if_neg hs] at hjval
      exact hs (huniq j.val (by omega) hjval)

end beaconcrypt_core.ratchet.control
