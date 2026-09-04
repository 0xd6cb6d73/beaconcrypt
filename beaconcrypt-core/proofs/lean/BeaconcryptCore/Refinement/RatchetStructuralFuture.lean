import BeaconcryptCore.Refinement.RatchetStructural
import BeaconcryptCore.Refinement.RatchetFuturePublication

/-! Future publication preserves structural validity for arbitrary chains and materials. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.control

/-- Appending an exact interval of fresh sequence numbers preserves structural control validity. -/
theorem ValidControl.extend {entry committed : RatchetState} (h : ValidControl entry)
    (count : Nat) (hcapacity : committed.Wf)
    (hreceive : entry.receive_sequence.val + count ≤ committed.receive_sequence.val)
    (hcache : cacheSeqs committed.receive_cache = cacheSeqs entry.receive_cache ++
      (List.range count).map (fun j => entry.receive_sequence.val + j + 1)) :
    ValidControl committed := by
  refine ⟨hcapacity, ?_, ?_, ?_⟩
  · intro sequence hmem
    rw [hcache] at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact h.positive sequence hmem
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hmem
      omega
  · intro sequence hmem
    rw [hcache] at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · have := h.past sequence hmem
      omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
      have := List.mem_range.mp hj
      omega
  · rw [hcache]
    refine List.Nodup.append h.unique (List.nodup_range.map (by intro i j heq; dsimp at heq; omega)) ?_
    intro sequence hmem hnew
    obtain ⟨j, _, heq⟩ := List.mem_map.mp hnew
    have := h.past sequence hmem
    omega

end beaconcrypt_core.ratchet.control

namespace beaconcrypt_core.ratchet.refined

open ratchet.control

/-- Exact validated transaction shape suffices for structural publication; no material derivation premise is needed. -/
theorem ValidRefined.future_publication {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (h : ValidRefined state)
    (pending : PendingReceive ReceiveChain Material)
    (hcontrol : ValidControl pending.committed_control)
    (hfirst : pending.first_slot = state.control.receive_cache.len)
    (hlength : pending.committed_control.receive_cache.len.val = pending.first_slot.val + pending.skipped.val)
    (hprefix : ∀ i, i < state.control.receive_cache.len.val →
      pending.committed_control.receive_cache.entries.val[i]! = state.control.receive_cache.entries.val[i]!)
    (hstaged : ∀ j, j < pending.skipped.val → ∃ cached,
      pending.staged_slots.val[pending.first_slot.val + j]! = core.option.Option.Some cached ∧
      cached.sequence = pending.committed_control.receive_cache.entries.val[pending.first_slot.val + j]!) :
    ∃ published, publish_future_receive state pending = ok published ∧ ValidRefined published := by
  have hcapacity : pending.first_slot.val + pending.skipped.val ≤ 50 := by
    have hc := hcontrol.capacity
    change pending.committed_control.receive_cache.len.val ≤ 50 at hc
    omega
  obtain ⟨published, hpublish, hpublishedControl, _, _, hslots⟩ := publish_future_receive_exact state pending hcapacity
  refine ⟨published, hpublish, ⟨by simpa only [hpublishedControl] using hcontrol, ?_⟩⟩
  intro i hi
  by_cases hold : i < state.control.receive_cache.len.val
  · obtain ⟨cached, hcached, hsequence⟩ := h.slots.live h.control.capacity i hold
    have hout : published.receive_slots.val[i]! = core.option.Option.Some cached := by
      rw [hslots i hi, if_neg (by simp only [hfirst]; omega)]
      exact hcached
    simp only [hout, hpublishedControl]
    exact ⟨by rw [hlength, hfirst]; omega, hsequence.trans (hprefix i hold).symm⟩
  · by_cases hlive : i < pending.committed_control.receive_cache.len.val
    · let j := i - pending.first_slot.val
      have hj : j < pending.skipped.val := by dsimp only [j]; rw [hfirst] at *; omega
      have hij : pending.first_slot.val + j = i := by dsimp only [j]; rw [hfirst]; omega
      obtain ⟨cached, hcached, hsequence⟩ := hstaged j hj
      have hout : published.receive_slots.val[i]! = core.option.Option.Some cached := by
        rw [hslots i hi, if_pos (by rw [hfirst] at *; omega), ← hij]
        exact hcached
      simp only [hout, hpublishedControl]
      exact ⟨hlive, by simpa only [hij] using hsequence⟩
    · have hout : published.receive_slots.val[i]! = core.option.Option.None := by
        rw [hslots i hi, if_neg (by omega)]
        exact h.slots.empty i (by omega) hi
      simp only [hout, hpublishedControl]
      omega

end beaconcrypt_core.ratchet.refined
