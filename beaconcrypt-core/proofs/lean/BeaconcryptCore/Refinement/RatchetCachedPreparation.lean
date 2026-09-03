import BeaconcryptCore.Refinement.RatchetAccessors
import BeaconcryptCore.PanicFreedom.Effects

/-! Structural contracts of cached receive preparation, independent of cryptographic provenance. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core
open BeaconcryptCore.Refinement.RatchetAccessors

set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.refined

/-- Every successful preparation records the checks performed by the generated code. -/
structure CachedPreparationFacts {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (sequence : Std.U64)
    (prepared : PreparedCachedReceive) : Prop where
  sequence_eq : prepared.sequence = sequence
  target_live : prepared.target_slot.val < state.control.receive_cache.len.val
  target_bound : prepared.target_slot.val < 50
  entry : state.control.receive_cache.entries.val[prepared.target_slot.val]! = sequence
  target_material : ∃ material, state.receive_slots.val[prepared.target_slot.val]! =
    core.option.Option.Some { sequence := sequence, material := material }
  last_value : prepared.last_slot.val = state.control.receive_cache.len.val - 1
  last_bound : prepared.last_slot.val < 50
  finish : control.finish_receive_with_removal state.control sequence prepared.target_slot true =
    ok { state := prepared.committed_control, disposition := control.ReceiveDisposition.Consumed, removal := core.option.Option.Some { target_slot := prepared.target_slot, last_slot := prepared.last_slot } }

theorem receive_key_at_some_inv (state : control.RatchetState) (slot : Std.U8) (sequence : Std.U64)
    (h : control.RatchetState.receive_key_at state slot = ok (core.option.Option.Some sequence)) :
    slot.val < state.receive_cache.len.val ∧ slot.val < 50 ∧
      state.receive_cache.entries.val[slot.val]! = sequence := by
  simp only [control.RatchetState.receive_key_at, control.SequenceCache.entry, lift, control.capacity_eq_ok, bind_tc_ok] at h
  (repeat' split at h) <;> simp only [RustM.ok.injEq, core.option.Option.None, core.option.Option.Some, reduceCtorEq] at h
  simp only [control.entries_index_eq_ok state.receive_cache slot (by scalar_tac), bind_tc_ok, RustM.ok.injEq, Option.some.injEq] at h
  exact ⟨by scalar_tac, by scalar_tac, h⟩

theorem prepare_cached_receive_success_inv {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (sequence : Std.U64)
    (prepared : PreparedCachedReceive)
    (h : prepare_cached_receive state sequence = ok (core.option.Option.Some prepared)) :
    CachedPreparationFacts state sequence prepared := by
  obtain ⟨lookup, hlookup⟩ := control.lookup_receive_key_total state.control sequence
  cases lookup <;> simp only [prepare_cached_receive, hlookup, bind_tc_ok, lift, control.capacity_eq_ok] at h
  all_goals first | (solve | simp at h) | skip
  rename_i targetSlot
  split at h <;> simp only [RustM.ok.injEq, core.option.Option.None, core.option.Option.Some, reduceCtorEq] at h
  rename_i htargetBound
  obtain ⟨logical, hlogical⟩ := control.RatchetState.receive_key_at_total state.control targetSlot
  cases logical <;> simp only [hlogical, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.U64.Insts.CoreCmpPartialEqU64, bind_tc_ok, Bool.false_eq_true, if_false, RustM.ok.injEq, reduceCtorEq] at h
  rename_i logicalSequence
  split at h <;> try simp only [RustM.ok.injEq, reduceCtorEq] at h
  rename_i hlogicalSequence
  have hlogicalEq : logicalSequence = sequence := by simpa using hlogicalSequence
  simp only [material_slots_index state.receive_slots targetSlot (by scalar_tac),
    bind_tc_ok, core.option.Option.as_ref, control.RatchetState.receive_cache_len] at h
  cases htarget : state.receive_slots.val[targetSlot.val]! <;>
    simp only [htarget, bind_tc_ok, RustM.ok.injEq, core.option.Option.None, reduceCtorEq] at h
  rename_i cached
  split at h <;> try simp only [RustM.ok.injEq, reduceCtorEq] at h
  rename_i hcachedSequence
  split at h <;> try simp only [RustM.ok.injEq, reduceCtorEq] at h
  obtain ⟨lastSlot, hlastSlot, hlastValue⟩ := control.uscalar_sub_eq_ok state.control.receive_cache.len 1#u8 (by scalar_tac)
  simp only [hlastSlot, bind_tc_ok] at h
  split at h <;> try simp only [RustM.ok.injEq, reduceCtorEq] at h
  rename_i hlenNe hlastBound
  obtain ⟨lastLogical, hlastLogical⟩ := control.RatchetState.receive_key_at_total state.control lastSlot
  obtain ⟨finished, hfinished⟩ := control.finish_receive_with_removal_ok state.control sequence targetSlot true
  simp only [hlastLogical, hfinished, bind_tc_ok,
    material_slots_index state.receive_slots lastSlot (by scalar_tac)] at h
  repeat'
    first
    | (solve | simp only [RustM.ok.injEq, reduceCtorEq] at h)
    | (simp only [bind_tc_ok] at h)
    | split at h
  have hprepared : (⟨sequence, targetSlot, lastSlot, finished.state⟩ : PreparedCachedReceive) = prepared := by simpa using h
  subst prepared
  have htargetLogical := receive_key_at_some_inv state.control targetSlot sequence (by simpa only [hlogicalEq] using hlogical)
  refine ⟨rfl, htargetLogical.1, htargetLogical.2.1, htargetLogical.2.2, ?_,
    by simpa using hlastValue, by scalar_tac, ?_⟩
  · exact ⟨cached.material, by simpa only [← hcachedSequence] using htarget⟩
  · cases finished
    simp_all
    cases_type control.ReceiveRemoval
    simp_all

/-- Every cached target in a structurally valid state admits successful preparation. -/
theorem ValidRefined.prepare_cached_receive {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (h : ValidRefined state)
    (sequence : Std.U64) (targetSlot : Std.U8)
    (hlookup : control.lookup_receive_key state.control sequence = ok (core.option.Option.Some targetSlot)) :
    ∃ prepared, prepare_cached_receive state sequence = ok (core.option.Option.Some prepared) ∧
      CachedPreparationFacts state sequence prepared := by
  obtain ⟨htargetLive, htargetEntry⟩ := control.lookup_receive_key_sound state.control sequence targetSlot h.control.capacity hlookup
  obtain ⟨cached, hcached, hcachedSequence⟩ := h.slots.live h.control.capacity targetSlot.val htargetLive
  have hcap : state.control.receive_cache.len.val ≤ 50 := h.control.capacity
  obtain ⟨lastSlot, hlastSub, hlastValue⟩ := control.uscalar_sub_eq_ok state.control.receive_cache.len 1#u8 (by scalar_tac)
  have hlastLive : lastSlot.val < state.control.receive_cache.len.val := by scalar_tac
  obtain ⟨lastCached, hlastCached, hlastSequence⟩ := h.slots.live h.control.capacity lastSlot.val hlastLive
  have htargetKey : control.RatchetState.receive_key_at state.control targetSlot = ok (core.option.Option.Some sequence) := by
    simpa only [htargetEntry] using receive_key_at_live state.control targetSlot htargetLive (by omega)
  have hlastKey := receive_key_at_live state.control lastSlot hlastLive (by omega)
  obtain ⟨finished, hfinish, hdisposition, hfinishedLen, _, _, hremoval, _⟩ :=
    control.finish_receive_consumed state.control sequence targetSlot h.control.capacity htargetLive htargetEntry
  have hlastControl : finished.state.receive_cache.len = lastSlot := UScalar.eq_of_val_eq (by scalar_tac)
  suffices hexact : refined.prepare_cached_receive state sequence =
      ok (core.option.Option.Some (⟨sequence, targetSlot, lastSlot, finished.state⟩ : PreparedCachedReceive)) from
    ⟨_, hexact, prepare_cached_receive_success_inv state sequence _ hexact⟩
  have hlenNe : state.control.receive_cache.len ≠ 0#u8 := by scalar_tac
  simp [refined.prepare_cached_receive, hlookup, lift, control.capacity_eq_ok,
    show ¬50 ≤ targetSlot.val by omega, show ¬50 ≤ lastSlot.val by omega,
    htargetKey, hlastKey, material_slots_index state.receive_slots targetSlot (by omega),
    material_slots_index state.receive_slots lastSlot (by omega), hcached, hlastCached,
    hcachedSequence, htargetEntry, hlastSequence, control.RatchetState.receive_cache_len,
    hlenNe, hlastSub, hfinish, hdisposition, hremoval, hlastControl,
    core.option.Option.as_ref, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.U64.Insts.CoreCmpPartialEqU64]

end beaconcrypt_core.ratchet.refined
