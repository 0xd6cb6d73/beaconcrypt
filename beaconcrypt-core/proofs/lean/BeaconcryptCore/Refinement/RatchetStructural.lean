import BeaconcryptCore.Refinement.RatchetCachedPublication
import BeaconcryptCore.Refinement.RatchetReceiveLoopExact

/-! Structural validity for arbitrary chains and materials, independently of canonical cryptographic provenance. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.control

/-- The historical structural control invariant: bounded, positive, past, distinct live sequence numbers. -/
structure ValidControl (state : RatchetState) : Prop where
  capacity : state.Wf
  positive : ∀ sequence ∈ cacheSeqs state.receive_cache, 0 < sequence
  past : ∀ sequence ∈ cacheSeqs state.receive_cache, sequence ≤ state.receive_sequence.val
  unique : (cacheSeqs state.receive_cache).Nodup

/-- Canonical control refinement entails the independent structural invariant. -/
theorem Refines.validControl {CK MK AD PT CT : Type}
    {cr : Ratchet.Crypto CK MK AD PT CT} {origin : CK}
    {receive : Ratchet.RecvState CK MK} {state : RatchetState}
    (h : Refines cr origin receive state) : ValidControl state := by
  refine ⟨h.wf, ?_, ?_, ?_⟩
  · intro sequence hmem
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp (h.cache.mem_iff.mp hmem)
    omega
  · intro sequence hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (h.cache.mem_iff.mp hmem)
    have := h.keys_lt p hp
    rw [h.seq]
    omega
  · apply h.cache.nodup_iff.mpr
    have heq : receive.skipped.map (fun p => p.1 + 1) = (receive.skipped.map Prod.fst).map (fun i => i + 1) := by simp
    rw [heq]
    exact h.nodup.map (by intro i j heq; dsimp at heq; omega)

/-- Empty caches are structurally valid at arbitrary counter values. -/
theorem from_counters_valid (send receive : Std.U64) :
    ∃ state, RatchetState.from_counters send receive = ok state ∧ ValidControl state ∧
      state.send_sequence = send ∧ state.receive_sequence = receive ∧ state.receive_cache.len = 0#u8 := by
  refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
  constructor <;> simp [RatchetState.Wf, SequenceCache.Wf, cacheSeqs]

/-- Distinct live physical slots have distinct sequence tags. -/
theorem ValidControl.slot_unique {state : RatchetState} (h : ValidControl state)
    (i j : Nat) (hi : i < state.receive_cache.len.val) (hj : j < state.receive_cache.len.val)
    (heq : state.receive_cache.entries.val[i]! = state.receive_cache.entries.val[j]!) : i = j := by
  apply (h.unique.getElem_inj_iff (hi := by simpa only [cacheSeqs_length] using hi)
    (hj := by simpa only [cacheSeqs_length] using hj)).mp
  simpa only [cacheSeqs, List.getElem_map, List.getElem_range] using congrArg UScalar.val heq

/-- Structural validity is preserved by receive advance, including exhaustion and full-cache rejection. -/
theorem ValidControl.advance_receive {state : RatchetState} (h : ValidControl state) :
    ∃ advanced, advance_receive state = ok advanced ∧ ValidControl advanced.state := by
  by_cases hmax : state.receive_sequence = core.num.U64.MAX
  · exact ⟨_, advance_receive_max state hmax, h⟩
  by_cases hfull : 50 ≤ state.receive_cache.len.val
  · exact ⟨_, advance_receive_full state hfull, h⟩
  obtain ⟨advanced, hrun, hsequence, _, hlength, _, hcache⟩ :=
    advance_receive_cacheSeqs state hmax (by omega)
  refine ⟨advanced, hrun, ⟨?_, ?_, ?_, ?_⟩⟩
  · change advanced.state.receive_cache.len.val ≤ 50
    omega
  · intro sequence hmem
    rw [hcache] at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact h.positive sequence hmem
    · simp only [List.mem_singleton] at hmem
      omega
  · intro sequence hmem
    rw [hcache] at hmem
    rw [hsequence]
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact Nat.le_trans (h.past sequence hmem) (Nat.le_succ _)
    · simp only [List.mem_singleton] at hmem
      omega
  · rw [hcache]
    refine List.Nodup.append h.unique (by simp) ?_
    intro sequence hmem hnew
    have hpast := h.past sequence hmem
    simp only [List.mem_singleton] at hnew
    omega

/-- Consuming one present sequence preserves structural validity independently of all material values. -/
theorem ValidControl.finish_consumed {state : RatchetState} (h : ValidControl state)
    (target : Std.U64) (slot : Std.U8) (hslot : slot.val < state.receive_cache.len.val)
    (hentry : state.receive_cache.entries.val[slot.val]! = target) :
    ∃ finished, finish_receive state target slot true = ok finished ∧
      finished.disposition = ReceiveDisposition.Consumed ∧ ValidControl finished.state ∧
      finished.state.receive_cache.len.val = state.receive_cache.len.val - 1 := by
  obtain ⟨finished, hrun, hdisposition, _, hreceive, hlength, hcache⟩ :=
    finish_receive_consumed_cacheSeqs state target slot h.capacity hslot hentry
  refine ⟨finished, hrun, hdisposition, ⟨?_, ?_, ?_, ?_⟩, hlength⟩
  · change finished.state.receive_cache.len.val ≤ 50
    have hcap := h.capacity
    change state.receive_cache.len.val ≤ 50 at hcap
    omega
  · intro sequence hmem
    exact h.positive sequence (List.mem_of_mem_erase (hcache.mem_iff.mp hmem))
  · intro sequence hmem
    rw [hreceive]
    exact h.past sequence (List.mem_of_mem_erase (hcache.mem_iff.mp hmem))
  · exact hcache.nodup_iff.mpr (h.unique.erase target.val)

/-- Every detailed control completion preserves the historical structural invariant. -/
theorem ValidControl.finish_receive_with_removal {state : RatchetState} (h : ValidControl state)
    (target : Std.U64) (slot : Std.U8) (authenticated : Bool) :
    ∃ result, finish_receive_with_removal state target slot authenticated = ok result ∧
      ValidControl result.state := by
  by_cases hslot : slot.val < state.receive_cache.len.val
  · by_cases hentry : state.receive_cache.entries.val[slot.val]! = target
    · cases authenticated with
      | false => exact ⟨_, finish_receive_with_removal_retained state target slot h.capacity hslot hentry, h⟩
      | true =>
          obtain ⟨result, hrun, _, _⟩ := finish_receive_consumed state target slot h.capacity hslot hentry
          obtain ⟨wrapped, hwrapped, _, hvalid, _⟩ := h.finish_consumed target slot hslot hentry
          have hwrapper : finish_receive state target slot true =
              ok { state := result.state, disposition := result.disposition } := by
            simp only [finish_receive, hrun, bind_tc_ok]
          have heq : wrapped.state = result.state :=
            congrArg (fun value => value.state) (RustM.ok.inj (hwrapped.symm.trans hwrapper))
          exact ⟨result, hrun, heq ▸ hvalid⟩
    · exact ⟨_, finish_receive_with_removal_mismatch state target slot authenticated h.capacity hslot hentry, h⟩
  · exact ⟨_, finish_receive_with_removal_out_of_range state target slot authenticated (by omega), h⟩

/-- The compatibility control wrapper preserves the same structural guarantee. -/
theorem ValidControl.finish_receive {state : RatchetState} (h : ValidControl state)
    (target : Std.U64) (slot : Std.U8) (authenticated : Bool) :
    ∃ result, finish_receive state target slot authenticated = ok result ∧ ValidControl result.state := by
  obtain ⟨result, hrun, hvalid⟩ := h.finish_receive_with_removal target slot authenticated
  exact ⟨{ state := result.state, disposition := result.disposition },
    by simp only [beaconcrypt_core.ratchet.control.finish_receive, hrun, bind_tc_ok], hvalid⟩

end beaconcrypt_core.ratchet.control

namespace beaconcrypt_core.ratchet.refined

open ratchet.control

/-- Every live slot has its exact control tag, and every inactive slot is empty. -/
def MaterialSlotsMatch {Material : Type} (cache : SequenceCache)
    (slots : Array (core.option.Option (CachedReceiveKey Material)) 50#usize) : Prop :=
  ∀ i, i < 50 → match slots.val[i]! with
    | .Some cached => i < cache.len.val ∧ cached.sequence = cache.entries.val[i]!
    | .None => cache.len.val ≤ i

/-- A matching live slot contains a tagged material record. -/
theorem MaterialSlotsMatch.live {Material : Type} {cache : SequenceCache}
    {slots : Array (core.option.Option (CachedReceiveKey Material)) 50#usize}
    (h : MaterialSlotsMatch cache slots) (hcap : cache.len.val ≤ 50)
    (i : Nat) (hi : i < cache.len.val) :
    ∃ cached, slots.val[i]! = core.option.Option.Some cached ∧ cached.sequence = cache.entries.val[i]! := by
  have hs := h i (by omega)
  cases hslot : slots.val[i]! with
  | none => simp only [hslot] at hs; omega
  | some cached =>
      simp only [hslot] at hs
      exact ⟨cached, rfl, hs.2⟩

/-- A matching inactive slot is empty. -/
theorem MaterialSlotsMatch.empty {Material : Type} {cache : SequenceCache}
    {slots : Array (core.option.Option (CachedReceiveKey Material)) 50#usize}
    (h : MaterialSlotsMatch cache slots) (i : Nat) (hlo : cache.len.val ≤ i) (hi : i < 50) :
    slots.val[i]! = core.option.Option.None := by
  have hs := h i hi
  cases hslot : slots.val[i]! with
  | none => rfl
  | some cached => simp only [hslot] at hs; omega

/-- Structural validity has no premise about chains or the provenance of material bytes. -/
structure ValidRefined {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) : Prop where
  control : ValidControl state.control
  slots : MaterialSlotsMatch state.control.receive_cache state.receive_slots

/-- The generic constructor is structurally valid for arbitrary supplied chains and counters. -/
theorem from_counters_valid {SendChain ReceiveChain Material : Type}
    (send receive : Std.U64) (sendChain : SendChain) (receiveChain : ReceiveChain) :
    ∃ state, RefinedRatchet.from_counters Material send receive sendChain receiveChain = ok state ∧
      ValidRefined state ∧ state.send_chain = sendChain ∧ state.receive_chain = receiveChain ∧
      state.control.send_sequence = send ∧ state.control.receive_sequence = receive := by
  obtain ⟨control, hcontrol, hvalid, hsend, hreceive, hlen⟩ := ratchet.control.from_counters_valid send receive
  let slots : Array (core.option.Option (CachedReceiveKey Material)) 50#usize :=
    ⟨List.replicate 50 core.option.Option.None, by simp⟩
  refine ⟨{ control, send_chain := sendChain, receive_chain := receiveChain, receive_slots := slots },
    ?_, ⟨hvalid, ?_⟩, rfl, rfl, hsend, hreceive⟩
  · simp only [RefinedRatchet.from_counters, hcontrol, bind_tc_ok, empty_material_slots]
    rfl
  · intro i hi
    change match (List.replicate 50 (core.option.Option.None : core.option.Option (CachedReceiveKey Material)))[i]! with
      | .Some cached => i < control.receive_cache.len.val ∧ cached.sequence = control.receive_cache.entries.val[i]!
      | .None => control.receive_cache.len.val ≤ i
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show i < (List.replicate 50 (core.option.Option.None : core.option.Option (CachedReceiveKey Material))).length by simpa using hi), List.getElem_replicate, Option.getD_some, hlen]
    simp

/-- The fresh generic constructor has the same structural guarantee. -/
theorem new_valid {SendChain ReceiveChain Material : Type}
    (sendChain : SendChain) (receiveChain : ReceiveChain) :
    ∃ state, RefinedRatchet.new Material sendChain receiveChain = ok state ∧ ValidRefined state := by
  obtain ⟨state, hrun, hvalid, _⟩ := from_counters_valid (Material := Material) 0#u64 0#u64 sendChain receiveChain
  exact ⟨state, hrun, hvalid⟩

/-- Cached publication preserves the weaker structural invariant for arbitrary material and chain types. -/
theorem ValidRefined.cached_publication {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (h : ValidRefined state)
    (prepared : PreparedCachedReceive)
    (htarget : prepared.target_slot.val < state.control.receive_cache.len.val)
    (hentry : state.control.receive_cache.entries.val[prepared.target_slot.val]! = prepared.sequence)
    (hlast : prepared.last_slot.val = state.control.receive_cache.len.val - 1)
    (hfinish : finish_receive_with_removal state.control prepared.sequence prepared.target_slot true =
      ok {
        state := prepared.committed_control, disposition := ReceiveDisposition.Consumed,
        removal := core.option.Option.Some { target_slot := prepared.target_slot, last_slot := prepared.last_slot } }) :
    ∃ published, publish_cached_receive state prepared = ok published ∧ ValidRefined published := by
  obtain ⟨finished, hfinished, _, hlength, hsend, hreceive, _, hentries⟩ :=
    finish_receive_consumed state.control prepared.sequence prepared.target_slot h.control.capacity htarget hentry
  have hstate : finished.state = prepared.committed_control :=
    congrArg (fun result => result.state) (RustM.ok.inj (hfinished.symm.trans hfinish))
  rw [hstate] at hlength hsend hreceive hentries
  obtain ⟨result, hresult, _, hvalid, _⟩ := h.control.finish_consumed prepared.sequence prepared.target_slot htarget hentry
  have hresultState : result.state = prepared.committed_control := by
    have hwrapper : finish_receive state.control prepared.sequence prepared.target_slot true =
        ok { state := prepared.committed_control, disposition := ReceiveDisposition.Consumed } := by
      simp only [finish_receive, hfinish, bind_tc_ok]
    exact congrArg (fun result => result.state) (RustM.ok.inj (hresult.symm.trans hwrapper))
  rw [hresultState] at hvalid
  have hcap : state.control.receive_cache.len.val ≤ 50 := h.control.capacity
  obtain ⟨published, hpublish, hcontrol, _, _, hslots⟩ := publish_cached_receive_exact state prepared (by omega) (by omega)
  refine ⟨published, hpublish, ⟨by simpa only [hcontrol] using hvalid, ?_⟩⟩
  intro i hi
  by_cases hlive : i < prepared.committed_control.receive_cache.len.val
  · let j := if i = prepared.target_slot.val then prepared.last_slot.val else i
    have hj : j < state.control.receive_cache.len.val := by dsimp only [j]; split_ifs <;> omega
    obtain ⟨cached, hcached, hsequence⟩ := h.slots.live hcap j hj
    have hentryAt : prepared.committed_control.receive_cache.entries.val[i]! = state.control.receive_cache.entries.val[j]! := by
      simpa only [j, hlast, apply_ite] using hentries i hlive
    have hslotAt : published.receive_slots.val[i]! = state.receive_slots.val[j]! := by
      simpa only [j, apply_ite, if_neg (by omega : i ≠ prepared.last_slot.val)] using hslots i hi
    simp only [hslotAt, hcached, hcontrol]
    exact ⟨hlive, hsequence.trans hentryAt.symm⟩
  · have hempty : published.receive_slots.val[i]! = core.option.Option.None := by
      by_cases hlastSlot : i = prepared.last_slot.val
      · simpa only [if_pos hlastSlot] using hslots i hi
      · simpa only [if_neg hlastSlot, if_neg (by omega : i ≠ prepared.target_slot.val),
          h.slots.empty i (by omega) hi] using hslots i hi
    simp only [hempty, hcontrol]
    omega

end beaconcrypt_core.ratchet.refined

namespace beaconcrypt_core.ratchet.concrete

/-- Full cryptographic provenance entails structural validity, but structural validity itself needs no such premise. -/
theorem KernelRefines.validRefined {AD PT CT : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {origin : ratchet.RatchetChain} {send : Ratchet.SendState ratchet.RatchetChain}
    {receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial}
    {kernel : ConcreteRatchetKernel} (h : KernelRefines cr origin send receive kernel) :
    ratchet.refined.ValidRefined kernel.refined := by
  refine ⟨h.receiveControl.validControl, ?_⟩
  intro i hi
  by_cases hlive : i < kernel.refined.control.receive_cache.len.val
  · obtain ⟨_, cached, _, hcached, hsequence, _, _⟩ := h.slotSound i hlive
    simp only [hcached]
    exact ⟨hlive, hsequence⟩
  · simp only [h.slotsAboveLenEmpty i (by omega) hi]
    omega

end beaconcrypt_core.ratchet.concrete
