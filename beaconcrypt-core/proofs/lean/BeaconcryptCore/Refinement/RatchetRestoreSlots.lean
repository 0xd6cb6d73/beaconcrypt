import BeaconcryptCore.Refinement.RatchetStructural

/-! Pointwise material-slot preservation when restoring one cached key. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core

namespace beaconcrypt_core.ratchet.refined

/-- Appending a tagged material and its logical entry preserves structural alignment. -/
theorem MaterialSlotsMatch.append {Material : Type}
    (cache next : control.SequenceCache)
    (slots : Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
    (sequence : Std.U64) (material : Material)
    (h : MaterialSlotsMatch cache slots) (hcap : cache.len.val < 50)
    (hlen : next.len.val = cache.len.val + 1)
    (hentries : next.entries = cache.entries.set (UScalar.cast .Usize cache.len) sequence) :
    MaterialSlotsMatch next (slots.set (UScalar.cast .Usize cache.len)
      (core.option.Option.Some { sequence := sequence, material := material })) := by
  intro i hi
  have hcast : (UScalar.cast UScalarTy.Usize cache.len).val = cache.len.val := by simp_scalar
  by_cases heq : i = cache.len.val
  · subst i
    simp_lists [hentries, hcast, hlen]
    omega
  · have hold := h i hi
    simp_lists [hentries, hcast, hlen, heq]
    simp only [getElem!_pos slots.val i (by simpa using hi),
      getElem!_pos cache.entries.val i (by simpa using hi)] at hold
    cases hs : slots.val[i]'(by simpa using hi) <;> simp only [hs] at hold ⊢ <;> try omega
    exact ⟨by omega, hold.2⟩

end beaconcrypt_core.ratchet.refined
