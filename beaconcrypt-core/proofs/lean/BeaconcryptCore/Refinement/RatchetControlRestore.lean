import BeaconcryptCore.Refinement.RatchetControl

/-!
# Restore and per-peer wrappers of the symmetric single ratchet control plane

This file continues the verification started in `BeaconcryptCore/Refinement/RatchetControl.lean`,
covering the two remaining parts of the extracted control plane
(`beaconcrypt-core/src/ratchet/control.rs`):

* the **restore path**, which rebuilds a ratchet state from persisted counters and a
  replay of the outstanding skipped-key sequence numbers, and
* the **per-peer wrappers**, which dispatch a request to the ratchet of one peer.

The bound of 50 outstanding skipped keys is shown to survive a restore
(`restore_receive_key_with_slot_full`, `restore_receive_key_with_slot_wf`), and the
per-peer wrappers are shown to be state neutral for any peer other than the requested
one (`replace_ratchet_for_peer_other`, `advance_send_for_peer_other`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

namespace beaconcrypt_core.ratchet.control

/-! ## Restoring a persisted ratchet -/

/-- A restore in progress is well formed when the state it is rebuilding is. -/
def RatchetRestore.Wf (r : RatchetRestore) : Prop := r.state.Wf

/-- Starting a restore rebuilds the persisted counters on top of an empty cache. -/
theorem start_restore_ok (send_sequence receive_sequence : Std.U64) :
    ∃ r, start_restore send_sequence receive_sequence = ok r ∧ r.Wf ∧
      r.state.send_sequence = send_sequence ∧
      r.state.receive_sequence = receive_sequence ∧
      r.state.receive_cache.len.val = 0 ∧ r.last_sequence = 0#u64 := by
  refine ⟨_, rfl, ?_, rfl, rfl, ?_, rfl⟩
  · simp [RatchetRestore.Wf, RatchetState.Wf, SequenceCache.Wf]
  · simp

/-- Sequence number `0` is never restored. -/
theorem restore_receive_key_with_slot_zero (r : RatchetRestore) :
    restore_receive_key_with_slot r 0#u64 = ok core.option.Option.None := by
  simp [restore_receive_key_with_slot]

/-- A key beyond the persisted receive counter is never restored. -/
theorem restore_receive_key_with_slot_ahead (r : RatchetRestore) (sequence : Std.U64)
    (h : r.state.receive_sequence.val < sequence.val) :
    restore_receive_key_with_slot r sequence = ok core.option.Option.None := by
  simp only [restore_receive_key_with_slot]
  rw [if_neg (by scalar_tac), if_pos (by scalar_tac)]

/-- The restore scan is strictly increasing: a sequence number that does not exceed the
one restored last is refused. -/
theorem restore_receive_key_with_slot_not_increasing (r : RatchetRestore) (sequence : Std.U64)
    (hzero : sequence.val ≠ 0) (hle : sequence.val ≤ r.state.receive_sequence.val)
    (h : sequence.val ≤ r.last_sequence.val) :
    restore_receive_key_with_slot r sequence = ok core.option.Option.None := by
  simp only [restore_receive_key_with_slot]
  rw [if_neg (by scalar_tac), if_neg (by scalar_tac), if_pos (by scalar_tac)]

/-- **The bound of 50 survives a restore.**  Once 50 skipped keys have been rebuilt, no
further key is accepted. -/
theorem restore_receive_key_with_slot_full (r : RatchetRestore) (sequence : Std.U64)
    (h : 50 ≤ r.state.receive_cache.len.val) :
    restore_receive_key_with_slot r sequence = ok core.option.Option.None := by
  simp only [restore_receive_key_with_slot,
    SequenceCache.append_eq_none_of_full r.state.receive_cache sequence h, bind_tc_ok]
  split_ifs <;> rfl

/-- Restoring a key never fails. -/
theorem restore_receive_key_with_slot_total (r : RatchetRestore) (sequence : Std.U64) :
    ∃ o, restore_receive_key_with_slot r sequence = ok o := by
  obtain ⟨o, ho⟩ := SequenceCache.append_total r.state.receive_cache sequence
  simp only [restore_receive_key_with_slot, ho, bind_tc_ok]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · cases o <;> exact ⟨_, rfl⟩

/-- A restore step preserves the bound of 50 outstanding skipped keys, keeps the
counters, and records the sequence number it just restored. -/
theorem restore_receive_key_with_slot_wf (r : RatchetRestore) (sequence : Std.U64)
    (step : ReceiveRestoreStep)
    (h : restore_receive_key_with_slot r sequence = ok (core.option.Option.Some step)) :
    step.restore.Wf ∧ step.restore.last_sequence = sequence ∧
      step.restore.state.send_sequence = r.state.send_sequence ∧
      step.restore.state.receive_sequence = r.state.receive_sequence := by
  obtain ⟨o, ho⟩ := SequenceCache.append_total r.state.receive_cache sequence
  simp only [restore_receive_key_with_slot, ho, bind_tc_ok] at h
  split_ifs at h
  · simp at h
  · simp at h
  · simp at h
  · cases o with
    | none => simp at h
    | some p =>
      obtain ⟨c', slot'⟩ := p
      simp at h
      subst h
      exact ⟨SequenceCache.append_len_le _ _ _ _ ho, rfl, rfl, rfl⟩

/-- Finishing a restore hands back the rebuilt state, which is well formed. -/
theorem finish_restore_wf (r : RatchetRestore) (hr : r.Wf) :
    finish_restore r = ok r.state ∧ r.state.Wf := ⟨rfl, hr⟩

/-- The restore wrapper inherits the guarantees of the slot-aware restore step. -/
theorem restore_receive_key_wf (r : RatchetRestore) (sequence : Std.U64)
    (r' : RatchetRestore)
    (h : restore_receive_key r sequence = ok (core.option.Option.Some r')) :
    r'.Wf ∧ r'.last_sequence = sequence ∧
      r'.state.send_sequence = r.state.send_sequence ∧
      r'.state.receive_sequence = r.state.receive_sequence := by
  obtain ⟨o, ho⟩ := restore_receive_key_with_slot_total r sequence
  simp only [restore_receive_key, ho, bind_tc_ok, core.option.Option.map] at h
  cases o with
  | none => simp at h
  | some step =>
    simp only
      [restore_receive_key.closure.Insts.CoreOpsFunctionFnOnceTupleReceiveRestoreStepRatchetRestore.call_once,
        bind_tc_ok] at h
    have hstep : step.restore = r' := by simpa using h
    obtain ⟨h1, h2, h3, h4⟩ := restore_receive_key_with_slot_wf r sequence step ho
    rw [hstep] at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩

/-! ## The per-peer wrappers -/

/-- Replacing the ratchet of the requested peer installs the replacement. -/
theorem replace_ratchet_for_peer_match (requested_peer : Std.U64) (peer : PeerRatchetState)
    (replacement : RatchetState) (h : requested_peer = peer.peer_id) :
    replace_ratchet_for_peer requested_peer peer replacement =
      ok { peer with ratchet := replacement } := by
  simp [replace_ratchet_for_peer, h]

/-- A request for a different peer leaves the peer state untouched. -/
theorem replace_ratchet_for_peer_other (requested_peer : Std.U64) (peer : PeerRatchetState)
    (replacement : RatchetState) (h : requested_peer ≠ peer.peer_id) :
    replace_ratchet_for_peer requested_peer peer replacement = ok peer := by
  simp [replace_ratchet_for_peer, h]

/-- A send request for a different peer is state neutral and hands out no key. -/
theorem advance_send_for_peer_other (requested_peer : Std.U64) (peer : PeerRatchetState)
    (h : requested_peer ≠ peer.peer_id) :
    advance_send_for_peer requested_peer peer =
      ok { peer := peer, sequence := core.option.Option.None,
           key := { sequence := 0#u64, available := false } } := by
  simp [advance_send_for_peer, SendKey.unavailable, h]

/-- Advancing the send path of a peer never touches its receive cache, so the bound of
50 outstanding skipped keys is preserved. -/
theorem advance_send_for_peer_wf (requested_peer : Std.U64) (peer : PeerRatchetState)
    (hpeer : peer.ratchet.Wf) :
    ∃ a, advance_send_for_peer requested_peer peer = ok a ∧
      a.peer.peer_id = peer.peer_id ∧
      a.peer.ratchet.receive_cache = peer.ratchet.receive_cache ∧
      a.peer.ratchet.receive_sequence = peer.ratchet.receive_sequence ∧
      a.peer.ratchet.Wf := by
  by_cases h : requested_peer = peer.peer_id
  · by_cases hmax : peer.ratchet.send_sequence = core.num.U64.MAX
    · have heq : advance_send_for_peer requested_peer peer =
          ok { peer := { peer with ratchet := peer.ratchet },
               sequence := core.option.Option.None,
               key := { sequence := 0#u64, available := false } } := by
        simp only [advance_send_for_peer, if_pos h, advance_send_max _ hmax, bind_tc_ok,
          replace_ratchet_for_peer_match _ _ _ h]
      exact ⟨_, heq, rfl, rfl, rfl, hpeer⟩
    · obtain ⟨adv, hadv, -, hrs, hrc, -, -⟩ := advance_send_ok peer.ratchet hmax
      have heq : advance_send_for_peer requested_peer peer =
          ok { peer := { peer with ratchet := adv.state },
               sequence := adv.sequence, key := adv.key } := by
        simp only [advance_send_for_peer, if_pos h, hadv, bind_tc_ok,
          replace_ratchet_for_peer_match _ _ _ h]
      refine ⟨_, heq, rfl, hrc, hrs, ?_⟩
      simp only [RatchetState.Wf] at hpeer ⊢
      rw [hrc]
      exact hpeer
  · exact ⟨_, advance_send_for_peer_other requested_peer peer h, rfl, rfl, rfl, hpeer⟩

end beaconcrypt_core.ratchet.control
