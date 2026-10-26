import BeaconcryptCore.Refinement.RatchetFutureFinalization

/-! Exact future publication preserves canonical chains, counters, and the full skipped-material correspondence. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.refined

/-- Future publication copies only the staged window and installs the validated control and chain. -/
theorem publish_future_receive_exact {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material)
    (hbound : pending.first_slot.val + pending.skipped.val ≤ 50) :
    ∃ published, publish_future_receive state pending = ok published ∧
      published.control = pending.committed_control ∧ published.send_chain = state.send_chain ∧
      published.receive_chain = pending.final_receive_chain ∧
      ∀ i, i < 50 → published.receive_slots.val[i]! =
        if pending.first_slot.val ≤ i ∧ i < pending.first_slot.val + pending.skipped.val
        then pending.staged_slots.val[i]! else state.receive_slots.val[i]! := by
  obtain ⟨out, remaining, hrun, _, hsend, _, hslots, _⟩ :=
    publish_future_receive_slots_exact state pending.staged_slots pending.first_slot pending.skipped hbound
  obtain ⟨available, havailable, havailableval⟩ := uscalar_sub_eq_ok (UScalar.cast UScalarTy.Usize 50#u64)
    (UScalar.cast UScalarTy.Usize pending.first_slot) (by scalar_tac)
  refine ⟨{ out with control := pending.committed_control, receive_chain := pending.final_receive_chain }, ?_, rfl, hsend, rfl, hslots⟩
  simp only [publish_future_receive, lift, capacity_eq_ok, bind_tc_ok,
    if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize pending.first_slot > UScalar.cast UScalarTy.Usize 50#u64),
    havailable, if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize pending.skipped > available), hrun]
  rfl

end beaconcrypt_core.ratchet.refined

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT : Type}

/-- The ideal poststate represented by a successfully authenticated future transaction. -/
def futureReceiveState
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial) (target : Std.U64) :
    Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial :=
  { ck := Ratchet.chainAt cr receive.ck (target.val - receive.n), n := target.val,
    skipped := receive.skipped ++ Ratchet.skipKeys cr receive.ck receive.n (target.val - receive.n - 1) }

/-- The completed private control cache is the old cache followed by exactly the skipped sequences. -/
theorem FuturePendingRefines.cache_sequences
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : FuturePendingRefines cr origin send receive entry target pending) :
    cacheSeqs pending.committed_control.receive_cache = cacheSeqs entry.refined.control.receive_cache ++
      (List.range (target.val - receive.n - 1)).map (fun j => receive.n + j + 1) := by
  simp only [cacheSeqs, h.committedLength, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [h.cachePrefix i (List.mem_range.mp hi)]
  · apply List.map_congr_left
    intro j hj
    exact h.cacheAppended j (List.mem_range.mp hj)

/-- Completed private control represents the ideal future poststate before any material is published. -/
theorem FuturePendingRefines.control_refines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : FuturePendingRefines cr origin send receive entry target pending) :
    Refines cr origin (futureReceiveState cr receive target) pending.committed_control := by
  have hsk : Ratchet.skipKeys cr receive.ck receive.n (target.val - receive.n - 1) =
      (List.range (target.val - receive.n - 1)).map
        (fun j => (receive.n + j, Ratchet.msgKeyAt cr origin (receive.n + j))) := by
    rw [h.entryRefines.receiveControl.chain]
    exact Ratchet.skipKeys_eq_map_range cr origin receive.n _
  refine ⟨?_, ?_, target.hmax, ?_, ?_, ?_, ?_, ?_⟩
  · change pending.committed_control.receive_cache.len.val ≤ 50
    rw [h.committedLength]
    exact h.capacity
  · exact congrArg UScalar.val h.committedReceive
  · change Ratchet.chainAt cr receive.ck (target.val - receive.n) = Ratchet.chainAt cr origin target.val
    rw [h.entryRefines.receiveControl.chain, Ratchet.chainAt_chainAt, Nat.add_sub_of_le (by have hf := h.future; omega)]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.entryRefines.receiveControl.keys p hp
    · rw [hsk] at hp
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
      rfl
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Nat.lt_trans (h.entryRefines.receiveControl.keys_lt p hp) h.future
    · have := Ratchet.mem_skipKeys_index cr receive.ck receive.n (target.val - receive.n - 1) hp
      have := h.future
      change p.1 < target.val
      omega
  · change ((receive.skipped ++ Ratchet.skipKeys cr receive.ck receive.n (target.val - receive.n - 1)).map Prod.fst).Nodup
    rw [List.map_append]
    refine List.Nodup.append h.entryRefines.receiveControl.nodup (Ratchet.nodup_skipKeys _ _ _ _) ?_
    intro i hi hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hj
    have := h.entryRefines.receiveControl.keys_lt p hp
    have := Ratchet.mem_skipKeys_index cr receive.ck receive.n (target.val - receive.n - 1) hq
    omega
  · change (cacheSeqs pending.committed_control.receive_cache).Perm
      ((receive.skipped ++ Ratchet.skipKeys cr receive.ck receive.n (target.val - receive.n - 1)).map (fun p => p.1 + 1))
    rw [h.cache_sequences cr origin send receive entry target pending, List.map_append, hsk, List.map_map]
    exact List.Perm.append h.entryRefines.receiveControl.cache (List.Perm.refl _)

/-- Publishing a canonical future transaction establishes the entire kernel relation without a poststate assumption. -/
theorem FuturePendingRefines.publication
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : FuturePendingRefines cr origin send receive entry target pending) :
    ∃ published, ratchet.refined.publish_future_receive entry.refined pending = ok published ∧
      KernelRefines cr origin send (futureReceiveState cr receive target) { refined := published } := by
  obtain ⟨published, hpublish, hcontrol, hsend, hreceive, hslots⟩ :=
    ratchet.refined.publish_future_receive_exact entry.refined pending
      (by simpa only [h.firstSlot, h.skipped] using h.capacity)
  simp only [h.firstSlot, h.skipped] at hslots
  have hsk : Ratchet.skipKeys cr receive.ck receive.n (target.val - receive.n - 1) =
      (List.range (target.val - receive.n - 1)).map
        (fun j => (receive.n + j, Ratchet.msgKeyAt cr origin (receive.n + j))) := by
    rw [h.entryRefines.receiveControl.chain]
    exact Ratchet.skipKeys_eq_map_range cr origin receive.n _
  have hmaterial : ∀ j, Ratchet.msgKeyAt cr receive.ck j = Ratchet.msgKeyAt cr origin (receive.n + j) := by
    intro j
    rw [h.entryRefines.receiveControl.chain, Ratchet.msgKeyAt_chainAt]
  refine ⟨published, hpublish, {
    receiveControl := by simpa only [hcontrol] using h.control_refines cr origin send receive entry target pending,
    sendSequence := by simpa only [hcontrol, h.committedSend] using h.entryRefines.sendSequence,
    sendLt := h.entryRefines.sendLt,
    sendChain := hsend.trans h.entryRefines.sendChain,
    receiveChain := hreceive.trans h.finalChain,
    slotSound := ?_, slotComplete := ?_, slotsAboveLenEmpty := ?_
  }⟩
  · intro i hi
    have hlen : i < entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) := by
      simpa only [hcontrol, h.committedLength] using hi
    have hib : i < 50 := by have := h.capacity; omega
    by_cases hold : i < entry.refined.control.receive_cache.len.val
    · obtain ⟨p, cached, hp, hcached, hsequence, hvalue, hmat⟩ := h.entryRefines.slotSound i hold
      refine ⟨p, cached, List.mem_append_left _ hp, ?_, ?_, hvalue, hmat⟩
      · rw [hslots i hib, if_neg (by omega)]
        exact hcached
      · simpa only [hcontrol] using hsequence.trans (h.cachePrefix i hold).symm
    · let j := i - entry.refined.control.receive_cache.len.val
      have hj : j < target.val - receive.n - 1 := by dsimp only [j]; omega
      have hij : entry.refined.control.receive_cache.len.val + j = i := by dsimp only [j]; omega
      obtain ⟨cached, hcached, hsequence, hmat⟩ := h.staging.staged j hj
      refine ⟨(receive.n + j, Ratchet.msgKeyAt cr origin (receive.n + j)), cached, ?_, ?_, ?_, hsequence, hmat.trans (hmaterial j)⟩
      · apply List.mem_append_right
        rw [hsk]
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      · rw [hslots i hib, if_pos (by omega), ← hij]
        exact hcached
      · apply UScalar.eq_of_val_eq
        simpa only [hcontrol, ← hij, hsequence] using (h.cacheAppended j hj).symm
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨i, hi, cached, hcached, hsequence, hvalue, hmat⟩ := h.entryRefines.slotComplete p hp
      refine ⟨i, ?_, cached, ?_, ?_, hvalue, hmat⟩
      · simp only [hcontrol, h.committedLength]
        omega
      · rw [hslots i (by have := h.capacity; omega), if_neg (by omega)]
        exact hcached
      · simpa only [hcontrol] using hsequence.trans (h.cachePrefix i hi).symm
    · rw [hsk] at hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      have hj' := List.mem_range.mp hj
      obtain ⟨cached, hcached, hsequence, hmat⟩ := h.staging.staged j hj'
      refine ⟨entry.refined.control.receive_cache.len.val + j, ?_, cached, ?_, ?_, hsequence, hmat.trans (hmaterial j)⟩
      · simp only [hcontrol, h.committedLength]
        omega
      · rw [hslots _ (by have := h.capacity; omega), if_pos (by omega)]
        exact hcached
      · apply UScalar.eq_of_val_eq
        simpa only [hcontrol, hsequence] using (h.cacheAppended j hj').symm
  · intro i hlo hi
    have hlen : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ i := by
      simpa only [hcontrol, h.committedLength] using hlo
    rw [hslots i hi, if_neg (by omega)]
    exact h.entryRefines.slotsAboveLenEmpty i (by omega) hi

/-- Any accepted callback result publishes the canonical future poststate. -/
theorem FutureOpenRefines.finish_some {Context Plaintext : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (opened : ReceiveOpen Context)
    (h : FutureOpenRefines cr origin send receive entry context target opened)
    (plaintext : Plaintext) :
    ∃ published, opened.finish (core.option.Option.Some plaintext) =
        ok ({ refined := published }, core.option.Option.Some plaintext) ∧
      KernelRefines cr origin send (futureReceiveState cr receive target) { refined := published } := by
  obtain ⟨pending, hentry, _, hphase, hpending⟩ := h
  obtain ⟨published, hpublish, hkernel⟩ := hpending.publication cr origin send receive entry target pending
  refine ⟨published, ?_, hkernel⟩
  simp only [ReceiveOpen.finish, hphase, hentry, hpublish, bind_tc_ok]

/-- Authentication receives exactly the ideal target material. -/
theorem FutureOpenRefines.material_exact {Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (opened : ReceiveOpen Context)
    (h : FutureOpenRefines cr origin send receive entry context target opened) :
    opened.material = ok (core.option.Option.Some (Ratchet.msgKeyAt cr receive.ck (target.val - receive.n - 1))) := by
  obtain ⟨pending, _, _, hphase, hpending⟩ := h
  simp only [ReceiveOpen.material, hphase, hpending.targetMaterial]

/-- Successful ideal authentication agrees with the actual future publication and preserves every kernel invariant. -/
theorem FutureOpenRefines.finish_success_refines {Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (opened : ReceiveOpen Context)
    (h : FutureOpenRefines cr origin send receive entry context target opened)
    (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hdecrypt : cr.dec (Ratchet.msgKeyAt cr receive.ck (target.val - receive.n - 1)) ad ciphertext = some plaintext) :
    ∃ published, opened.finish (core.option.Option.Some plaintext) =
        ok ({ refined := published }, core.option.Option.Some plaintext) ∧
      Ratchet.recvStep cr receive ad ⟨target.val - 1, ciphertext⟩ =
        (.ok plaintext, futureReceiveState cr receive target) ∧
      KernelRefines cr origin send (futureReceiveState cr receive target) { refined := published } := by
  obtain ⟨published, hfinish, hkernel⟩ := h.finish_some cr origin send receive entry context target opened plaintext
  obtain ⟨pending, _, _, _, hpending⟩ := h
  have hf := hpending.future
  have hge : receive.n ≤ target.val - 1 := by omega
  have hgap : target.val - 1 - receive.n = target.val - receive.n - 1 := by omega
  have hlen := hpending.entryRefines.receiveControl.cache.length_eq
  simp only [cacheSeqs_length, List.length_map] at hlen
  have hideal := Ratchet.recvStep_chain_ok cr receive ad ⟨target.val - 1, ciphertext⟩ plaintext
    (Ratchet.lookup_eq_none_of_keys_lt hpending.entryRefines.receiveControl.keys_lt hge) hge
    (by have hc := hpending.capacity; simp only [Ratchet.maxSkip]; omega)
    (by simpa only [hgap] using hdecrypt)
  refine ⟨published, hfinish, ?_, hkernel⟩
  simpa only [hgap, show target.val - receive.n - 1 + 1 = target.val - receive.n by omega,
    show target.val - 1 + 1 = target.val by omega, futureReceiveState] using hideal

end beaconcrypt_core.ratchet.concrete
