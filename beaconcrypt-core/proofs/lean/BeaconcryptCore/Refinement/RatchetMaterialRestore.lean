import BeaconcryptCore.Refinement.RatchetEffectRefinement
import BeaconcryptCore.PanicFreedom.Restore

/-!
# Conditional refinement of material restoration

Restoration accepts persisted chains and material supplied by the caller. The refinement relation records their canonical ideal meanings and the increasing restoration frontier; the extracted builder preserves that relation and publishes it without changing the ideal model.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT : Type}

/-- The complete kernel represented by a restoration builder before publication. -/
def restoreKernel (r : ConcreteRatchetRestore) : ConcreteRatchetKernel :=
  { refined := {
      control := r.refined.logical.state
      send_chain := r.refined.send_chain
      receive_chain := r.refined.receive_chain
      receive_slots := r.refined.receive_slots } }

/-- Restoration additionally records the monotone frontier of accepted persisted keys. -/
structure RestoreRefines
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (restore : ConcreteRatchetRestore) : Prop where
  kernel : KernelRefines cr origin send receive (restoreKernel restore)
  frontier : ∀ p ∈ receive.skipped, p.1 + 1 ≤ restore.refined.logical.last_sequence.val

private theorem array_index_bang {α : Type} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (h : i.val < v.length) :
    v.index_usize i = ok v.val[i.val]! := by
  simpa only [getElem!_pos v.val i.val (by simpa using h)] using array_index_eq_ok v i h

/-- A successful logical append and an empty returned slot publish sequence and material together. -/
theorem concrete_restore_receive_key_of_append (r : ConcreteRatchetRestore)
    (sequence : Std.U64) (material : RatchetMaterial) (step : ReceiveRestoreStep)
    (hstep : restore_receive_key_with_slot r.refined.logical sequence = ok (core.option.Option.Some step))
    (hslot : step.slot.val < 50)
    (hempty : r.refined.receive_slots.val[step.slot.val]! = core.option.Option.None) :
    concrete_restore_receive_key r sequence material = ok (true,
      { refined := { r.refined with
          logical := step.restore
          receive_slots := r.refined.receive_slots.set (UScalar.cast UScalarTy.Usize step.slot)
            (core.option.Option.Some { sequence, material }) } }) := by
  simp only [concrete_restore_receive_key, refined.refined_restore_receive_key, hstep,
    lift, capacity_eq_ok, bind_tc_ok,
    if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize step.slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
    array_index_bang r.refined.receive_slots (UScalar.cast UScalarTy.Usize step.slot) (by scalar_tac),
    show (UScalar.cast UScalarTy.Usize step.slot).val = step.slot.val by simp_scalar,
    hempty, core.option.Option.is_some, Std.core.option.Option.is_some, Option.isSome,
    core.option.Option.None, Bool.false_eq_true, if_false, Bool.false_or,
    massert, decide_eq_true (by scalar_tac : UScalar.cast UScalarTy.Usize step.slot < 50#usize), if_true]
  simp only [Array.index_mut_usize,
    array_index_bang r.refined.receive_slots (UScalar.cast UScalarTy.Usize step.slot) (by scalar_tac),
    bind_tc_ok]
  dsimp! only
  rw [Array.set_getElem!_eq, array_update_eq_ok _ _ _ (by scalar_tac)]
  rfl

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

/-- Inserting a fresh canonical persisted key extends the represented ideal skipped store by exactly one entry. -/
theorem KernelRefines.append_restored
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (kernel : ConcreteRatchetKernel) (h : KernelRefines cr origin send receive kernel)
    (sequence : Std.U64) (material : RatchetMaterial) (next : SequenceCache)
    (hpositive : 0 < sequence.val) (hbelow : sequence.val ≤ receive.n)
    (hfresh : ∀ p ∈ receive.skipped, p.1 ≠ sequence.val - 1)
    (hmaterial : material = Ratchet.msgKeyAt cr origin (sequence.val - 1))
    (hcap : kernel.refined.control.receive_cache.len.val < 50)
    (hlen : next.len.val = kernel.refined.control.receive_cache.len.val + 1)
    (hentries : next.entries = kernel.refined.control.receive_cache.entries.set
      (UScalar.cast UScalarTy.Usize kernel.refined.control.receive_cache.len) sequence) :
    KernelRefines cr origin send
      { receive with skipped := receive.skipped ++ [(sequence.val - 1, material)] }
      { refined := { kernel.refined with
          control := { kernel.refined.control with receive_cache := next }
          receive_slots := kernel.refined.receive_slots.set
            (UScalar.cast UScalarTy.Usize kernel.refined.control.receive_cache.len)
            (core.option.Option.Some { sequence, material }) } } := by
  refine {
    receiveControl := ?_
    sendSequence := h.sendSequence
    sendLt := h.sendLt
    sendChain := h.sendChain
    receiveChain := h.receiveChain
    slotSound := ?_
    slotComplete := ?_
    slotsAboveLenEmpty := ?_ }
  · refine {
      wf := by change next.len.val ≤ 50; omega
      seq := h.receiveControl.seq
      lt := h.receiveControl.lt
      chain := h.receiveControl.chain
      keys := ?_
      keys_lt := ?_
      nodup := ?_
      cache := ?_ }
    · simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using
        And.intro h.receiveControl.keys hmaterial
    · simpa only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq] using
        And.intro h.receiveControl.keys_lt (show sequence.val - 1 < receive.n by omega)
    · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.nodup_singleton]
      refine ⟨h.receiveControl.nodup, trivial, ?_⟩
      intro a ha b hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      simpa only [List.mem_singleton.mp hb] using hfresh p hp
    · simpa only [cacheSeqs_append _ next sequence hcap hlen hentries, List.map_append,
        List.map_cons, List.map_nil, Nat.sub_add_cancel (by omega : 1 ≤ sequence.val)] using
        h.receiveControl.cache.append_right [sequence.val]
  · intro i hi
    by_cases hold : i < kernel.refined.control.receive_cache.len.val
    · obtain ⟨p, cached, hp, hcached, hlogical, hsequence, hmat⟩ := h.slotSound i hold
      refine ⟨p, cached, List.mem_append_left _ hp, ?_, ?_, hsequence, hmat⟩
      · rw [array_set_bang _ _ _ _ (by scalar_tac), if_neg (by scalar_tac)]
        exact hcached
      · change cached.sequence = next.entries.val[i]!
        rw [hentries, array_set_bang _ _ _ _ (by scalar_tac), if_neg (by scalar_tac)]
        exact hlogical
    · have hi' : i = kernel.refined.control.receive_cache.len.val := by
        change i < next.len.val at hi
        omega
      refine ⟨(sequence.val - 1, material), { sequence, material }, by simp, ?_, ?_, by simp; omega, rfl⟩
      · rw [array_set_bang _ _ _ _ (by scalar_tac), if_pos (by scalar_tac)]
      · change sequence = next.entries.val[i]!
        rw [hentries, array_set_bang _ _ _ _ (by scalar_tac), if_pos (by scalar_tac)]
  · intro p hp
    rcases List.mem_append.mp hp with hold | hnew
    · obtain ⟨i, hi, cached, hcached, hlogical, hsequence, hmat⟩ := h.slotComplete p hold
      refine ⟨i, by change i < next.len.val; omega, cached, ?_, ?_, hsequence, hmat⟩
      · rw [array_set_bang _ _ _ _ (by scalar_tac), if_neg (by scalar_tac)]
        exact hcached
      · change cached.sequence = next.entries.val[i]!
        rw [hentries, array_set_bang _ _ _ _ (by scalar_tac), if_neg (by scalar_tac)]
        exact hlogical
    · rcases List.mem_singleton.mp hnew with rfl
      refine ⟨kernel.refined.control.receive_cache.len.val, by change _ < next.len.val; omega,
        { sequence, material }, ?_, ?_, by simp; omega, rfl⟩
      · rw [array_set_bang _ _ _ _ (by scalar_tac), if_pos (by simp_scalar)]
      · change sequence = next.entries.val[kernel.refined.control.receive_cache.len.val]!
        rw [hentries, array_set_bang _ _ _ _ (by scalar_tac), if_pos (by simp_scalar)]
  · intro i hi hbound
    change next.len.val ≤ i at hi
    rw [array_set_bang _ _ _ _ (by scalar_tac), if_neg (by scalar_tac)]
    exact h.slotsAboveLenEmpty i (by omega) hbound

end beaconcrypt_core.ratchet.concrete
