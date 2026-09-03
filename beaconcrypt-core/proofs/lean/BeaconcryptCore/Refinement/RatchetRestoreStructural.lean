import BeaconcryptCore.Refinement.RatchetRestoreSlots
import BeaconcryptCore.Refinement.RatchetRestoreAtomic

/-!
# Structural validity of material restoration

Restoration preserves packed cache alignment, positive distinct sequences, the receive-counter bound, and the increasing restoration frontier for arbitrary chain and material values. Canonical cryptographic provenance is not required for these structural claims.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.refined

/-- The structural restoration invariant includes the ordering frontier of prior accepted keys. -/
structure ValidRestore {SendChain ReceiveChain Material : Type}
    (r : RefinedRatchetRestore SendChain ReceiveChain Material) : Prop where
  control : ValidControl r.logical.state
  slots : MaterialSlotsMatch r.logical.state.receive_cache r.receive_slots
  frontier : ∀ sequence ∈ cacheSeqs r.logical.state.receive_cache, sequence ≤ r.logical.last_sequence.val

private theorem array_set_bang {α : Type} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (x : α) (j : Nat) (h : j < v.length) :
    (v.set i x).val[j]! = if i.val = j then x else v.val[j]! := by
  by_cases heq : i.val = j
  · simpa only [if_pos heq, Array.getElem!_Nat_eq] using
      Array.getElem!_Nat_set_eq v i j x ⟨heq, h⟩
  · simpa only [if_neg heq, Array.getElem!_Nat_eq] using
      Array.getElem!_Nat_set_ne v i j x heq

private theorem cacheSeqs_append (cache next : SequenceCache) (sequence : Std.U64)
    (hcap : cache.len.val < 50)
    (hlen : next.len.val = cache.len.val + 1)
    (hentries : next.entries = cache.entries.set (UScalar.cast UScalarTy.Usize cache.len) sequence) :
    cacheSeqs next = cacheSeqs cache ++ [sequence.val] := by
  simp only [cacheSeqs, hlen, List.range_succ, hentries, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [array_set_bang _ _ _ _ (by scalar_tac), if_neg (by scalar_tac)]
  · rw [array_set_bang _ _ _ _ (by scalar_tac), if_pos (by simp_scalar)]

/-- Appending a positive sequence above all previously restored keys preserves structural control validity. -/
theorem restore_control_append_valid (state : RatchetState) (h : ValidControl state)
    (last : Std.U64) (hfrontier : ∀ s ∈ cacheSeqs state.receive_cache, s ≤ last.val)
    (sequence : Std.U64) (next : SequenceCache)
    (hpositive : 0 < sequence.val) (hpast : sequence.val ≤ state.receive_sequence.val)
    (hnew : last.val < sequence.val) (hcap : state.receive_cache.len.val < 50)
    (hlen : next.len.val = state.receive_cache.len.val + 1)
    (hentries : next.entries = state.receive_cache.entries.set
      (UScalar.cast UScalarTy.Usize state.receive_cache.len) sequence) :
    ValidControl { state with receive_cache := next } ∧
      (∀ s ∈ cacheSeqs next, s ≤ sequence.val) := by
  have hcache := cacheSeqs_append state.receive_cache next sequence hcap hlen hentries
  refine ⟨{
    capacity := by change next.len.val ≤ 50; omega
    positive := ?_
    past := ?_
    unique := ?_ }, ?_⟩
  · simpa only [hcache, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using
      And.intro h.positive hpositive
  · simpa only [hcache, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using
      And.intro h.past hpast
  · rw [hcache]
    refine List.Nodup.append h.unique (by simp) ?_
    intro s hs hnewmem
    have hbound := hfrontier s hs
    simp only [List.mem_singleton] at hnewmem
    omega
  · simpa only [hcache, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using
      And.intro (fun s hs => Nat.le_trans (hfrontier s hs) (Nat.le_of_lt hnew)) (Nat.le_refl sequence.val)

/-- An admitted structural restoration appends sequence and material atomically and preserves every validity clause. -/
theorem ValidRestore.append {SendChain ReceiveChain Material : Type}
    (r : RefinedRatchetRestore SendChain ReceiveChain Material) (h : ValidRestore r)
    (sequence : Std.U64) (material : Material)
    (hpositive : 0 < sequence.val) (hbelow : sequence.val ≤ r.logical.state.receive_sequence.val)
    (hfrontier : r.logical.last_sequence.val < sequence.val)
    (hcap : r.logical.state.receive_cache.len.val < 50) :
    ∃ next, refined_restore_receive_key r sequence material = ok (true, next) ∧ ValidRestore next ∧
      next.send_chain = r.send_chain ∧ next.receive_chain = r.receive_chain ∧
      next.logical.state.send_sequence = r.logical.state.send_sequence ∧
      next.logical.state.receive_sequence = r.logical.state.receive_sequence ∧
      next.logical.last_sequence = sequence ∧
      next.logical.state.receive_cache.len.val = r.logical.state.receive_cache.len.val + 1 ∧
      next.logical.state.receive_cache.entries = r.logical.state.receive_cache.entries.set
        (UScalar.cast UScalarTy.Usize r.logical.state.receive_cache.len) sequence ∧
      next.receive_slots = r.receive_slots.set (UScalar.cast UScalarTy.Usize r.logical.state.receive_cache.len)
        (core.option.Option.Some { sequence, material }) := by
  obtain ⟨cache, happend, hlen, hentries⟩ :=
    SequenceCache.append_ok r.logical.state.receive_cache sequence (by omega) hcap
  let step : ReceiveRestoreStep := {
    restore := { state := { r.logical.state with receive_cache := cache }, last_sequence := sequence }
    slot := r.logical.state.receive_cache.len }
  have hstep : restore_receive_key_with_slot r.logical sequence = ok (core.option.Option.Some step) := by
    simp only [restore_receive_key_with_slot, if_neg (by scalar_tac : sequence ≠ 0#u64),
      if_neg (by scalar_tac : ¬sequence > r.logical.state.receive_sequence),
      if_neg (by scalar_tac : ¬sequence ≤ r.logical.last_sequence), happend, bind_tc_ok, step]
    rfl
  have hrun := refined_restore_receive_key_of_append r sequence material step hstep hcap
    (h.slots.empty r.logical.state.receive_cache.len.val (by rfl) hcap)
  obtain ⟨hcontrol, hlast⟩ := restore_control_append_valid r.logical.state h.control
    r.logical.last_sequence h.frontier sequence cache hpositive hbelow hfrontier hcap hlen hentries
  exact ⟨_, hrun, ⟨hcontrol, h.slots.append r.logical.state.receive_cache cache r.receive_slots
      sequence material hcap hlen hentries, hlast⟩,
    rfl, rfl, rfl, rfl, rfl, hlen, hentries, rfl⟩

/-- Restoration begins structurally valid for arbitrary persisted counters and chains. -/
theorem start_refined_restore_valid {SendChain ReceiveChain Material : Type}
    (send receive : Std.U64) (sendChain : SendChain) (receiveChain : ReceiveChain) :
    ∃ r, start_refined_restore Material send receive sendChain receiveChain = ok r ∧ ValidRestore r := by
  refine ⟨_, rfl, ⟨?_, ?_, ?_⟩⟩
  · constructor <;> simp [RatchetState.Wf, SequenceCache.Wf, cacheSeqs]
  · intro i hi
    change match (List.replicate 50 (core.option.Option.None : core.option.Option (CachedReceiveKey Material)))[i]! with
      | .Some _ => _
      | .None => 0 ≤ i
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < (List.replicate 50 (core.option.Option.None : core.option.Option (CachedReceiveKey Material))).length by simpa using hi),
      List.getElem_replicate, Option.getD_some, Nat.zero_le]
  · simp [cacheSeqs]

/-- Finishing structural restoration publishes the exact valid control and material state. -/
theorem ValidRestore.finish {SendChain ReceiveChain Material : Type}
    (r : RefinedRatchetRestore SendChain ReceiveChain Material) (h : ValidRestore r) :
    ∃ state, finish_refined_restore r = ok state ∧ ValidRefined state ∧
      state.control = r.logical.state ∧ state.send_chain = r.send_chain ∧
      state.receive_chain = r.receive_chain ∧ state.receive_slots = r.receive_slots :=
  ⟨_, rfl, ⟨h.control, h.slots⟩, rfl, rfl, rfl, rfl⟩

/-- The exact physical and logical changes made by one accepted restoration. -/
def RestoreAppendShape {SendChain ReceiveChain Material : Type}
    (r next : RefinedRatchetRestore SendChain ReceiveChain Material) (sequence : Std.U64) (material : Material) : Prop :=
  next.send_chain = r.send_chain ∧ next.receive_chain = r.receive_chain ∧
    next.logical.state.send_sequence = r.logical.state.send_sequence ∧
    next.logical.state.receive_sequence = r.logical.state.receive_sequence ∧
    next.logical.last_sequence = sequence ∧
    next.logical.state.receive_cache.len.val = r.logical.state.receive_cache.len.val + 1 ∧
    next.logical.state.receive_cache.entries = r.logical.state.receive_cache.entries.set
      (UScalar.cast UScalarTy.Usize r.logical.state.receive_cache.len) sequence ∧
    next.receive_slots = r.receive_slots.set (UScalar.cast UScalarTy.Usize r.logical.state.receive_cache.len)
      (core.option.Option.Some { sequence, material })

/-- Every restoration attempt is structurally valid and atomic, with no material provenance premise. -/
theorem ValidRestore.restore {SendChain ReceiveChain Material : Type}
    (r : RefinedRatchetRestore SendChain ReceiveChain Material) (h : ValidRestore r)
    (sequence : Std.U64) (material : Material) :
    ∃ accepted next, refined_restore_receive_key r sequence material = ok (accepted, next) ∧
      ValidRestore next ∧ (if accepted then RestoreAppendShape r next sequence material else next = r) := by
  by_cases hadmit : 0 < sequence.val ∧ sequence.val ≤ r.logical.state.receive_sequence.val ∧
      r.logical.last_sequence.val < sequence.val ∧ r.logical.state.receive_cache.len.val < 50
  · obtain ⟨next, hrun, hnext, hshape⟩ := h.append r sequence material
      hadmit.1 hadmit.2.1 hadmit.2.2.1 hadmit.2.2.2
    exact ⟨true, next, hrun, hnext, hshape⟩
  · exact ⟨false, r, refined_restore_receive_key_logical_rejection r sequence material
      (restore_logical_rejects r.logical sequence hadmit), h, rfl⟩

end beaconcrypt_core.ratchet.refined
