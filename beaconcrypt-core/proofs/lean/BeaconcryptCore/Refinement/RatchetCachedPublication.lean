import BeaconcryptCore.Refinement.RatchetEffectRefinement
import BeaconcryptCore.PanicFreedom.Control

/-! Exact material-array publication and cached-receive refinement. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.refined

/-- Cached publication removes the target, moves the last live material into its place, and empties the old last slot. -/
theorem publish_cached_receive_exact {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (prepared : PreparedCachedReceive)
    (htarget : prepared.target_slot.val < 50) (hlast : prepared.last_slot.val < 50) :
    ∃ published, publish_cached_receive state prepared = ok published ∧
      published.control = prepared.committed_control ∧
      published.send_chain = state.send_chain ∧
      published.receive_chain = state.receive_chain ∧
      ∀ i, i < 50 → published.receive_slots.val[i]! =
        if i = prepared.last_slot.val then core.option.Option.None
        else if i = prepared.target_slot.val then state.receive_slots.val[prepared.last_slot.val]!
        else state.receive_slots.val[i]! := by
  simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok,
    if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize prepared.target_slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
    if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize prepared.last_slot ≥ UScalar.cast UScalarTy.Usize 50#u64)]
  simp! only [array_index_mut_eq_ok state.receive_slots
    (UScalar.cast UScalarTy.Usize prepared.last_slot) (by scalar_tac),
    core.option.Option.take, Std.core.option.Option.take, bind_tc_ok, massert,
    if_pos (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.target_slot < 50#usize)]
  simp! only [array_index_mut_eq_ok
    (state.receive_slots.set (UScalar.cast UScalarTy.Usize prepared.last_slot) none)
    (UScalar.cast UScalarTy.Usize prepared.target_slot) (by scalar_tac), bind_tc_ok]
  rw [array_update_eq_ok _ _ _ (by scalar_tac)]
  split_ifs with heq <;> refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
  all_goals
    intro i hi
    simp_lists [Std.Array.set_val_eq]
    split_ifs <;> simp_all

end beaconcrypt_core.ratchet.refined

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT : Type}

/-- A valid cached transaction re-establishes the full chain, counter, material, and empty-suffix relation after publication. -/
theorem KernelRefines.cached_publication
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ConcreteRatchetKernel)
    (h : KernelRefines cr origin send receive kernel)
    (prepared : ratchet.refined.PreparedCachedReceive) (index : ℕ)
    (hindex : prepared.sequence.val = index + 1)
    (htarget : prepared.target_slot.val < kernel.refined.control.receive_cache.len.val)
    (hentry : kernel.refined.control.receive_cache.entries.val[prepared.target_slot.val]! =
      prepared.sequence)
    (hlast : prepared.last_slot.val = kernel.refined.control.receive_cache.len.val - 1)
    (hfinish : ratchet.control.finish_receive_with_removal kernel.refined.control
      prepared.sequence prepared.target_slot true =
      ok {
        state := prepared.committed_control,
        disposition := ratchet.control.ReceiveDisposition.Consumed,
        removal := core.option.Option.Some {
          target_slot := prepared.target_slot, last_slot := prepared.last_slot } }) :
    ∃ published, ratchet.refined.publish_cached_receive kernel.refined prepared = ok published ∧
      KernelRefines cr origin send
        { receive with skipped := receive.skipped.filter (fun p => !(p.1 == index)) }
        { refined := published } := by
  obtain ⟨finished, hfinished, _, hlen, hsend, hreceive, _, hentries⟩ :=
    finish_receive_consumed kernel.refined.control prepared.sequence prepared.target_slot
      h.receiveControl.wf htarget hentry
  have hstate : finished.state = prepared.committed_control :=
    congrArg (fun result => result.state) (RustM.ok.inj (hfinished.symm.trans hfinish))
  rw [hstate] at hlen hsend hreceive hentries
  have hcap : kernel.refined.control.receive_cache.len.val ≤ 50 := h.receiveControl.wf
  obtain ⟨published, hpublish, hcontrol, hsendChain, hreceiveChain, hslots⟩ :=
    ratchet.refined.publish_cached_receive_exact kernel.refined prepared
      (by omega)
      (by omega)
  have hnew := ratchet.control.Refines.finish_receive_with_removal_consumed_refines cr origin receive
        kernel.refined.control h.receiveControl prepared.sequence index prepared.target_slot
        hindex htarget hentry _ hfinish
  refine ⟨published, hpublish, ?_⟩
  refine {
    receiveControl := by simpa only [hcontrol] using hnew,
    sendSequence := by simpa only [hcontrol, hsend] using h.sendSequence,
    sendLt := h.sendLt,
    sendChain := hsendChain.trans h.sendChain,
    receiveChain := hreceiveChain.trans h.receiveChain,
    slotSound := ?_,
    slotComplete := ?_,
    slotsAboveLenEmpty := ?_
  }
  · intro i hi
    have hi' : i < prepared.committed_control.receive_cache.len.val := by
      simpa only [hcontrol] using hi
    let j := if i = prepared.target_slot.val then prepared.last_slot.val else i
    have hj : j < kernel.refined.control.receive_cache.len.val := by
      dsimp only [j]
      split_ifs <;> omega
    obtain ⟨p, cached, hp, hcached, hsequence, hvalue, hmaterial⟩ := h.slotSound j hj
    have hentryAt : prepared.committed_control.receive_cache.entries.val[i]! =
        kernel.refined.control.receive_cache.entries.val[j]! := by
      simpa only [j, hlast, apply_ite] using hentries i hi'
    have hslotAt : published.receive_slots.val[i]! = kernel.refined.receive_slots.val[j]! := by
      simpa only [j, apply_ite, if_neg (by omega : i ≠ prepared.last_slot.val)] using
        hslots i (by omega)
    have hmem : p.1 + 1 ∈ cacheSeqs prepared.committed_control.receive_cache :=
      (mem_cacheSeqs_iff _ _).mpr ⟨i, hi', by rw [hentryAt, ← hsequence, hvalue]⟩
    obtain ⟨q, hq, hqvalue⟩ := List.mem_map.mp (hnew.cache.mem_iff.mp hmem)
    have hpne : p.1 ≠ index := by
      have hqne := (List.mem_filter.mp hq).2
      simp at hqne
      omega
    exact ⟨p, cached, List.mem_filter.mpr ⟨hp, by simpa using hpne⟩, hslotAt.trans hcached,
      by simpa only [hcontrol] using hsequence.trans hentryAt.symm, hvalue, hmaterial⟩
  · intro p hp
    obtain ⟨i, hi, cached, hcached, hsequence, hvalue, hmaterial⟩ :=
      h.slotComplete p (List.mem_of_mem_filter hp)
    have hpne : p.1 ≠ index := by simpa using (List.mem_filter.mp hp).2
    have hneTarget : i ≠ prepared.target_slot.val := by
      intro heq
      have hc := congrArg UScalar.val hsequence
      rw [heq, hentry] at hc
      omega
    let j := if i = prepared.last_slot.val then prepared.target_slot.val else i
    have hj : j < prepared.committed_control.receive_cache.len.val := by
      dsimp only [j]
      split_ifs <;> omega
    have hsource : (if j = prepared.target_slot.val then prepared.last_slot.val else j) = i := by
      by_cases hilast : i = prepared.last_slot.val <;> simp [j, hilast, hneTarget]
    have hentryAt : prepared.committed_control.receive_cache.entries.val[j]! =
        kernel.refined.control.receive_cache.entries.val[i]! := by
      simpa only [← hlast, ← apply_ite, hsource] using hentries j hj
    have hslotAt : published.receive_slots.val[j]! = kernel.refined.receive_slots.val[i]! := by
      simpa only [if_neg (by omega : j ≠ prepared.last_slot.val), ← apply_ite, hsource] using
        hslots j (by omega)
    exact ⟨j, by simpa only [hcontrol] using hj, cached, hslotAt.trans hcached,
      by simpa only [hcontrol] using hsequence.trans hentryAt.symm, hvalue, hmaterial⟩
  · intro i hlo hi
    have hlo' : prepared.committed_control.receive_cache.len.val ≤ i := by
      simpa only [hcontrol] using hlo
    by_cases hilast : i = prepared.last_slot.val
    · simpa only [if_pos hilast] using hslots i hi
    · simpa only [if_neg hilast, if_neg (by omega : i ≠ prepared.target_slot.val),
        h.slotsAboveLenEmpty i (by omega) hi] using hslots i hi

/-- Cached success returns the ideal plaintext and preserves the complete kernel relation, with publication derived from the extracted implementation. -/
theorem CachedOpenRefines.finish_success_refines {Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ) (material : ratchet.RatchetMaterial)
    (pending : ReceiveOpen Context)
    (h : CachedOpenRefines cr origin send receive index material pending)
    (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hdecrypt : cr.dec material ad ciphertext = some plaintext) :
    ∃ published,
      pending.finish (core.option.Option.Some plaintext) =
        ok ({ refined := published }, core.option.Option.Some plaintext) ∧
      Ratchet.recvStep cr receive ad ⟨index, ciphertext⟩ =
        (.ok plaintext, { receive with skipped := receive.skipped.filter (fun p => !(p.1 == index)) }) ∧
      KernelRefines cr origin send
        { receive with skipped := receive.skipped.filter (fun p => !(p.1 == index)) }
        { refined := published } := by
  have hdata := h
  obtain ⟨prepared, cached, hphase, _, hlast, hfinish, hkernel, _, hindex,
    hslot, _, hcontrolSequence, hsequence, _⟩ := hdata
  obtain ⟨published, hpublish, hpublication⟩ :=
    KernelRefines.cached_publication cr origin send receive pending.entry hkernel prepared index
      hindex hslot (hcontrolSequence.symm.trans hsequence) hlast hfinish
  exact ⟨published, CachedOpenRefines.finish_success_refines_of_publication cr origin send receive
    index material pending h ad ciphertext plaintext hdecrypt prepared published hphase hpublish
    hpublication⟩

end beaconcrypt_core.ratchet.concrete
