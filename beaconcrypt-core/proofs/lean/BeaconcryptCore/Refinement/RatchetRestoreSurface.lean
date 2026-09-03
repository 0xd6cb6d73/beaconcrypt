import BeaconcryptCore.Refinement.RatchetRestoreStructural

/-! Direct restoration contracts matching the historical structural proof surface. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core

set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.control

/-- The complete logical restoration invariant, including the imported-key frontier. -/
structure ValidRestore (restore : RatchetRestore) : Prop where
  state : ValidControl restore.state
  frontier : ∀ sequence ∈ cacheSeqs restore.state.receive_cache, sequence ≤ restore.last_sequence.val

/-- A successful restoration records the exact append slot and logical sequence. -/
structure RestoreSlotShape (before : RatchetRestore) (sequence : Std.U64)
    (step : ReceiveRestoreStep) : Prop where
  slot_value : step.slot.val = before.state.receive_cache.len.val
  slot_bound : step.slot.val < 50
  length : step.restore.state.receive_cache.len.val = before.state.receive_cache.len.val + 1
  entry : step.restore.state.receive_cache.entries.val[step.slot.val]! = sequence

/-- The returned slot is live, bounded, and contains the restored sequence. -/
theorem RestoreSlotShape.cache_slot (before : RatchetRestore) (sequence : Std.U64)
    (step : ReceiveRestoreStep) (h : RestoreSlotShape before sequence step) :
    step.slot.val < step.restore.state.receive_cache.len.val ∧ step.slot.val < 50 ∧
      step.restore.state.receive_cache.entries.val[step.slot.val]! = sequence :=
  ⟨by have := h.slot_value; have := h.length; omega, h.slot_bound, h.entry⟩

/-- Checked raw restoration preserves the full logical invariant and reports the append slot. -/
theorem ValidRestore.restore_with_slot (restore : RatchetRestore) (h : ValidRestore restore)
    (sequence : Std.U64) :
    ∃ result, restore_receive_key_with_slot restore sequence = ok result ∧
      (∀ step, result = core.option.Option.Some step →
        ValidRestore step.restore ∧ RestoreSlotShape restore sequence step) := by
  by_cases hadmit : 0 < sequence.val ∧ sequence.val ≤ restore.state.receive_sequence.val ∧
    restore.last_sequence.val < sequence.val ∧ restore.state.receive_cache.len.val < 50
  · obtain ⟨cache, happend, hlen, hentries⟩ :=
      SequenceCache.append_ok restore.state.receive_cache sequence (by omega) hadmit.2.2.2
    obtain ⟨hcontrol, hfrontier⟩ := refined.restore_control_append_valid restore.state h.state
      restore.last_sequence h.frontier sequence cache hadmit.1 hadmit.2.1 hadmit.2.2.1 hadmit.2.2.2 hlen hentries
    let step : ReceiveRestoreStep := { restore := { state := { restore.state with receive_cache := cache }, last_sequence := sequence }, slot := restore.state.receive_cache.len }
    refine ⟨core.option.Option.Some step, ?_, ?_⟩
    · simp only [restore_receive_key_with_slot, if_neg (by scalar_tac : sequence ≠ 0#u64),
        if_neg (by scalar_tac : ¬sequence > restore.state.receive_sequence),
        if_neg (by scalar_tac : ¬sequence ≤ restore.last_sequence), happend, bind_tc_ok, step]
      rfl
    · intro other heq
      obtain rfl : step = other := by simpa using heq
      refine ⟨⟨hcontrol, hfrontier⟩, ⟨rfl, hadmit.2.2.2, hlen, ?_⟩⟩
      dsimp only [step]
      simp_lists [hentries]
  · exact ⟨_, refined.restore_logical_rejects restore sequence hadmit, by simp⟩

/-- Starting logical restoration establishes every historical validity clause. -/
theorem start_restore_is_valid (send receive : Std.U64) :
    ∃ restore, start_restore send receive = ok restore ∧ ValidRestore restore := by
  refine ⟨_, rfl, ⟨?_, ?_⟩⟩
  · constructor <;> simp [RatchetState.Wf, SequenceCache.Wf, cacheSeqs]
  · simp [cacheSeqs]

/-- Finishing logical restoration publishes the complete valid control state. -/
theorem finish_restore_is_valid (restore : RatchetRestore) (h : ValidRestore restore) :
    finish_restore restore = ok restore.state ∧ ValidControl restore.state := ⟨rfl, h.state⟩

/-- The compatibility operation is exactly the projection of the detailed result. -/
theorem restore_receive_key_wrapper_matches_slot (restore : RatchetRestore) (sequence : Std.U64) :
    ∃ result, restore_receive_key_with_slot restore sequence = ok result ∧
      restore_receive_key restore sequence = ok (Option.map ReceiveRestoreStep.restore result) := by
  obtain ⟨result, hresult⟩ := restore_receive_key_with_slot_total restore sequence
  refine ⟨result, hresult, ?_⟩
  cases result <;> simp [restore_receive_key, hresult, core.option.Option.map,
    restore_receive_key.closure.Insts.CoreOpsFunctionFnOnceTupleReceiveRestoreStepRatchetRestore.call_once]

/-- The raw compatibility operation preserves the complete logical restoration invariant. -/
theorem ValidRestore.restore (restore : RatchetRestore) (h : ValidRestore restore) (sequence : Std.U64) :
    ∃ result, restore_receive_key restore sequence = ok result ∧
      (∀ next, result = core.option.Option.Some next → ValidRestore next) := by
  obtain ⟨result, hresult, hvalid⟩ := h.restore_with_slot restore sequence
  refine ⟨Option.map ReceiveRestoreStep.restore result, ?_, ?_⟩
  · cases result <;> simp [restore_receive_key, hresult, core.option.Option.map,
      restore_receive_key.closure.Insts.CoreOpsFunctionFnOnceTupleReceiveRestoreStepRatchetRestore.call_once]
  · cases result with
    | none => simp
    | some step =>
      intro next heq
      obtain rfl : step.restore = next := by simpa using heq
      exact (hvalid step rfl).1

end beaconcrypt_core.ratchet.control

namespace beaconcrypt_core.ratchet.refined

/-- Accepted restoration preserves the complete packed prefix and exposes its exact new tagged slot. -/
theorem RestoreAppendShape.exact_slots {SendChain ReceiveChain Material : Type}
    (before after : RefinedRatchetRestore SendChain ReceiveChain Material)
    (sequence : Std.U64) (material : Material)
    (h : RestoreAppendShape before after sequence material) (hvalid : ValidRestore after) :
    ∃ slot : Std.U8, slot.val = before.logical.state.receive_cache.len.val ∧
      slot.val < after.logical.state.receive_cache.len.val ∧ slot.val < 50 ∧
      after.logical.state.receive_cache.entries.val[slot.val]! = sequence ∧
      after.receive_slots.val[slot.val]! = core.option.Option.Some { sequence, material } ∧
      (∀ i, i < before.logical.state.receive_cache.len.val →
        after.logical.state.receive_cache.entries.val[i]! = before.logical.state.receive_cache.entries.val[i]! ∧
        after.receive_slots.val[i]! = before.receive_slots.val[i]!) := by
  obtain ⟨_, _, _, _, _, hlen, hentries, hslots⟩ := h
  have hcap : after.logical.state.receive_cache.len.val ≤ 50 := hvalid.control.capacity
  refine ⟨before.logical.state.receive_cache.len, rfl, by omega, by omega, ?_, ?_, ?_⟩
  · simp_lists [hentries]
  · simp_lists [hslots]
  · intro i hi
    simp_lists [hentries, hslots]

end beaconcrypt_core.ratchet.refined
