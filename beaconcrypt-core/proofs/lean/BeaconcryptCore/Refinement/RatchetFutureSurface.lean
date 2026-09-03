import BeaconcryptCore.Refinement.RatchetRelativeFuture

/-! Explicit future-target exclusion and inactive-slot consequences of the structural relative proof. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- A future target is absent from every structurally valid entry cache. -/
theorem future_target_is_absent_from_entry {SendChain ReceiveChain Material : Type}
    (entry : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (h : ratchet.refined.ValidRefined entry) (target : Std.U64)
    (hfuture : entry.control.receive_sequence.val < target.val) :
    target.val ∉ cacheSeqs entry.control.receive_cache := by
  exact fun hmem => (Nat.not_le.mpr hfuture) (h.control.past _ hmem)

/-- Every staged key precedes the uncached target sequence. -/
theorem FutureStagedRefines.excludes_target {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (chain : ratchet.RatchetChain) (base first count : Nat)
    (slots : Array (core.option.Option (ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial)) 50#usize)
    (h : FutureStagedRefines cr chain base first count slots)
    (target : Std.U64) (htarget : target.val = base + count + 1) :
    ∀ i, i < 50 → ∀ cached, slots.val[i]! = core.option.Option.Some cached → cached.sequence ≠ target := by
  intro i hi cached hslot heq
  by_cases hout : i < first ∨ first + count ≤ i
  · simp only [h.empty i hi hout, core.option.Option.Some, core.option.Option.None, reduceCtorEq] at hslot
  · obtain ⟨record, hrecord, hsequence, _⟩ := h.staged (i - first) (by omega)
    have hrecord_eq : record = cached := by simpa only [Nat.add_sub_of_le (by omega : first ≤ i), hslot, core.option.Option.Some, Option.some.injEq] using hrecord.symm
    rw [hrecord_eq, heq, htarget] at hsequence
    omega

/-- A validated relative future transaction never stages its authentication target. -/
theorem RelativeFuturePending.staged_excludes_target {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : RelativeFuturePending cr entry target pending) :
    ∀ i, i < 50 → ∀ cached, pending.staged_slots.val[i]! = core.option.Option.Some cached → cached.sequence ≠ target := by
  exact h.staging.excludes_target cr entry.refined.receive_chain entry.refined.control.receive_sequence.val
    entry.refined.control.receive_cache.len.val _ pending.staged_slots target (by have hf := h.future; omega)

/-- The final structural cache relation clears every inactive material slot. -/
theorem RelativeFutureResult.empty_suffix {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : RelativeFutureResult cr entry target published)
    (i : Nat) (hi : i < 50)
    (hout : entry.refined.control.receive_cache.len.val +
      (target.val - entry.refined.control.receive_sequence.val - 1) ≤ i) :
    published.receive_slots.val[i]! = core.option.Option.None := by
  exact h.valid.slots.empty i (by simpa only [h.length] using hout) hi

end beaconcrypt_core.ratchet.concrete
