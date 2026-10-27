import BeaconcryptCore.Refinement.RatchetFutureAdmission

/-! The last future-receive KDF response validates the completed private transaction and requests authentication using the exact ideal target material. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- A completed future transaction retains exactly the old cache and the newly derived skipped keys. -/
structure FuturePendingRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial) : Prop where
  entryRefines : KernelRefines cr origin send receive entry
  future : receive.n < target.val
  capacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50
  firstSlot : pending.first_slot = entry.refined.control.receive_cache.len
  skipped : pending.skipped.val = target.val - receive.n - 1
  committedSend : pending.committed_control.send_sequence = entry.refined.control.send_sequence
  committedReceive : pending.committed_control.receive_sequence = target
  committedLength : pending.committed_control.receive_cache.len.val =
    entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1)
  cachePrefix : ∀ i, i < entry.refined.control.receive_cache.len.val →
    pending.committed_control.receive_cache.entries.val[i]! = entry.refined.control.receive_cache.entries.val[i]!
  cacheAppended : ∀ j, j < target.val - receive.n - 1 →
    (pending.committed_control.receive_cache.entries.val[entry.refined.control.receive_cache.len.val + j]!).val =
      receive.n + j + 1
  staging : FutureStagedRefines cr receive.ck receive.n entry.refined.control.receive_cache.len.val
    (target.val - receive.n - 1) pending.staged_slots
  finalChain : pending.final_receive_chain = Ratchet.chainAt cr receive.ck (target.val - receive.n)
  targetSequence : pending.target_sequence = target
  targetMaterial : pending.target_material = Ratchet.msgKeyAt cr receive.ck (target.val - receive.n - 1)

/-- The open request carries the original entry/context and a fully refined future transaction. -/
def FutureOpenRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (opened : ReceiveOpen Context) : Prop :=
  ∃ pending, opened.entry = entry ∧ opened.context = context ∧
    opened.prepared = ratchet.refined.PreparedReceive.PreparedReceiveFutureCase pending ∧
    FuturePendingRefines cr origin send receive entry target pending

/-- The authentication target is absent from the private skipped-key cache. -/
theorem FuturePendingRefines.target_absent
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : FuturePendingRefines cr origin send receive entry target pending) :
    lookup_receive_key pending.committed_control target = ok core.option.Option.None := by
  apply lookup_receive_key_of_not_mem _ _ (show pending.committed_control.Wf from by
    change pending.committed_control.receive_cache.len.val ≤ 50
    rw [h.committedLength]
    exact h.capacity)
  intro hmem
  obtain ⟨i, hi, heq⟩ := (mem_cacheSeqs_iff _ _).1 hmem
  by_cases hold : i < entry.refined.control.receive_cache.len.val
  · obtain ⟨p, cached, hp, _, hkey, hsequence, _⟩ := h.entryRefines.slotSound i hold
    have hpast := h.entryRefines.receiveControl.keys_lt p hp
    rw [h.cachePrefix i hold, ← hkey, hsequence] at heq
    have hfuture := h.future
    omega
  · have happended := h.cacheAppended (i - entry.refined.control.receive_cache.len.val) (by have hlen := h.committedLength; omega)
    rw [Nat.add_sub_of_le (by omega), heq] at happended
    have hlen := h.committedLength
    have hfuture := h.future
    omega

/-- Every transaction satisfying the semantic staging invariant passes production validation. -/
theorem FuturePendingRefines.valid
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : FuturePendingRefines cr origin send receive entry target pending) :
    ratchet.refined.pending_receive_is_valid entry.refined pending target = ok true := by
  refine ratchet.refined.pending_receive_is_valid_true entry.refined pending target
    h.targetSequence (by simpa only [h.entryRefines.receiveControl.seq] using h.future)
    h.firstSlot h.committedSend h.committedReceive
    (by simpa only [h.entryRefines.receiveControl.seq] using h.skipped)
    (by simpa only [h.firstSlot, h.skipped] using h.capacity)
    (by simpa only [h.firstSlot, h.skipped] using h.committedLength)
    (h.target_absent cr origin send receive entry target pending)
    (by simpa only [h.firstSlot] using h.cachePrefix)
    (by simpa only [h.firstSlot] using h.entryRefines.slotsAboveLenEmpty)
    (fun i hi hj => h.staging.empty i hi (Or.inr (by simpa only [h.firstSlot, h.skipped] using hj))) ?_
  intro j hj
  obtain ⟨cached, hcached, hsequence, _⟩ := h.staging.staged j (by simpa only [h.skipped] using hj)
  refine ⟨cached, by simpa only [h.firstSlot] using hcached,
    by simpa only [h.entryRefines.receiveControl.seq] using hsequence,
    UScalar.eq_of_val_eq ?_⟩
  simpa only [h.firstSlot, hsequence] using h.cacheAppended j (by simpa only [h.skipped] using hj)

end beaconcrypt_core.ratchet.concrete
