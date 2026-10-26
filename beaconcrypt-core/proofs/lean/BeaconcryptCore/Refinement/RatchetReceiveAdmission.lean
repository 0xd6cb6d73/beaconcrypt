import BeaconcryptCore.Refinement.RatchetFuturePublication

/-! Exact rejection classification for canonical extracted receive admission. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- A missing old sequence is rejected at admission and returns the exact entry kernel. -/
theorem KernelRefines.begin_receive_missing
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (h : KernelRefines cr origin send receive entry)
    (hpast : target.val ≤ receive.n)
    (hmissing : ∀ p ∈ receive.skipped, p.1 + 1 ≠ target.val) :
    begin_receive entry target context = ok (ReceiveEffect.ReceiveRejected entry context) := by
  have hlookup := lookup_receive_key_of_not_mem entry.refined.control target h.receiveControl.wf (by
    intro hmem
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp (h.receiveControl.cache.mem_iff.mp hmem)
    exact hmissing p hp heq)
  simp only [begin_receive, plan_receive_until_replay entry.refined.control target
    (by simpa only [h.receiveControl.seq] using hpast), bind_tc_ok, if_true,
    ratchet.refined.prepare_cached_receive, hlookup, receive_rejected]

/-- Sequence zero has no ideal message predecessor and is always rejected by a canonical kernel. -/
theorem KernelRefines.begin_receive_zero
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context)
    (h : KernelRefines cr origin send receive entry) :
    begin_receive entry 0#u64 context = ok (ReceiveEffect.ReceiveRejected entry context) := by
  exact h.begin_receive_missing cr origin send receive entry 0#u64 context (by simp) (by intro p _; simp)

/-- An old sequence absent from the ideal store is rejected before any external request. -/
theorem KernelRefines.begin_receive_replay
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (h : KernelRefines cr origin send receive entry)
    (hpast : target.val ≤ receive.n) (hpositive : 0 < target.val)
    (hmissing : List.lookup (target.val - 1) receive.skipped = none) :
    begin_receive entry target context = ok (ReceiveEffect.ReceiveRejected entry context) := by
  apply h.begin_receive_missing cr origin send receive entry target context hpast
  intro p hp heq
  have hne := List.lookup_eq_none_iff.mp hmissing p hp
  simp only [bne_iff_ne] at hne
  exact hne (by omega)

/-- Exceeding the retained-key budget rejects admission without changing the entry kernel. -/
theorem KernelRefines.begin_receive_capacity_rejected
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (h : KernelRefines cr origin send receive entry)
    (hfuture : receive.n < target.val)
    (hcapacity : 50 < entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1)) :
    begin_receive entry target context = ok (ReceiveEffect.ReceiveRejected entry context) := by
  have hplan : plan_receive_until entry.refined.control target =
      ok { sequence := core.option.Option.None, derivations := 0#u64 } := by
    by_cases hgap : receive.n + 51 < target.val
    · exact plan_receive_until_reject_of_gap_gt _ _ (by simpa only [h.receiveControl.seq] using hgap)
    · exact plan_receive_until_reject_of_cache_full _ _
        (by simpa only [h.receiveControl.seq] using hfuture)
        (by simpa only [h.receiveControl.seq] using Nat.le_of_not_gt hgap)
        (by simpa only [h.receiveControl.seq] using hcapacity)
  simp only [begin_receive, hplan, bind_tc_ok, receive_rejected]

end beaconcrypt_core.ratchet.concrete
