import BeaconcryptCore.Refinement.RatchetCachedPreparation
import BeaconcryptCore.Refinement.RatchetStructural
import BeaconcryptCore.Refinement.RatchetReceiveRollback

/-! Successful cached publication preserves structural validity and consumes the target independently of material provenance. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.refined

/-- Every successfully prepared cached transaction publishes a valid state, consumes its target, and frees exactly one slot. -/
theorem CachedPreparationFacts.publication {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (hvalid : ValidRefined state)
    (sequence : Std.U64) (prepared : PreparedCachedReceive)
    (h : CachedPreparationFacts state sequence prepared) :
    ∃ published, publish_cached_receive state prepared = ok published ∧ ValidRefined published ∧
      published.control = prepared.committed_control ∧
      published.control.receive_sequence = state.control.receive_sequence ∧
      published.control.receive_cache.len.val = state.control.receive_cache.len.val - 1 ∧
      0 < sequence.val ∧ sequence.val ≤ published.control.receive_sequence.val ∧
      lookup_receive_key published.control sequence = ok core.option.Option.None := by
  obtain ⟨published, hpublish, hpublishedValid⟩ := hvalid.cached_publication state prepared h.target_live
    (h.entry.trans h.sequence_eq.symm) h.last_value (by simpa only [h.sequence_eq] using h.finish)
  obtain ⟨other, hother, hcontrol, _, _, _⟩ := publish_cached_receive_exact state prepared h.target_bound h.last_bound
  have heq : other = published := RustM.ok.inj (hother.symm.trans hpublish)
  rw [heq] at hcontrol
  obtain ⟨finished, hfinished, _, hlength, _, hreceive, _, _⟩ :=
    finish_receive_consumed state.control sequence prepared.target_slot hvalid.control.capacity h.target_live h.entry
  have hfinishedState : finished.state = prepared.committed_control :=
    congrArg (fun result => result.state) (RustM.ok.inj (hfinished.symm.trans h.finish))
  rw [hfinishedState] at hlength hreceive
  have hmem : sequence.val ∈ cacheSeqs state.control.receive_cache :=
    (mem_cacheSeqs_iff _ _).mpr ⟨prepared.target_slot.val, h.target_live, congrArg UScalar.val h.entry⟩
  have hlookup := lookup_receive_key_consumed_absent state.control sequence prepared.target_slot
    hvalid.control.capacity h.target_live h.entry
    (fun i hi hentry => hvalid.control.slot_unique i prepared.target_slot.val hi h.target_live (hentry.trans h.entry.symm))
    _ h.finish
  exact ⟨published, hpublish, hpublishedValid, hcontrol, hcontrol ▸ hreceive,
    by simpa only [hcontrol] using hlength, hvalid.control.positive sequence.val hmem,
    by simpa only [hcontrol, hreceive] using hvalid.control.past sequence.val hmem,
    by simpa only [hcontrol] using hlookup⟩

end beaconcrypt_core.ratchet.refined

namespace beaconcrypt_core.ratchet.concrete

/-- A completed receive has consumed its positive target and retains a structurally valid kernel. -/
structure ReceiveSuccess (target : Std.U64) (result : ConcreteRatchetKernel) : Prop where
  valid : ratchet.refined.ValidRefined result.refined
  positive : 0 < target.val
  received : target.val ≤ result.refined.control.receive_sequence.val
  consumed : lookup_receive_key result.refined.control target = ok core.option.Option.None

/-- Any cached successful callback publishes the checked structural success condition. -/
theorem finish_cached_success {Context Output : Type}
    (opened : ReceiveOpen Context) (sequence : Std.U64) (prepared : ratchet.refined.PreparedCachedReceive)
    (hvalid : ratchet.refined.ValidRefined opened.entry.refined)
    (hphase : opened.prepared = ratchet.refined.PreparedReceive.PreparedReceiveCachedCase prepared)
    (h : ratchet.refined.CachedPreparationFacts opened.entry.refined sequence prepared)
    (plaintext : Output) :
    ∃ result, opened.finish (core.option.Option.Some plaintext) = ok (result, core.option.Option.Some plaintext) ∧
      ReceiveSuccess sequence result := by
  obtain ⟨published, hpublish, hpublished, _, _, _, hpositive, hreceived, hconsumed⟩ :=
    h.publication opened.entry.refined hvalid sequence prepared
  exact ⟨{ refined := published }, by simp only [ReceiveOpen.finish, hphase, hpublish, bind_tc_ok],
    hpublished, hpositive, hreceived, hconsumed⟩

/-- Replaying a consumed target is neutral for any later interpreter, context, or callback. -/
theorem ReceiveSuccess.replay {Context Output : Type} {target : Std.U64} {result : ConcreteRatchetKernel}
    (h : ReceiveSuccess target result) (execute : KdfInterpreter) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output) :
    receiveNext execute result target context openReply = ok (result, core.option.Option.None) := by
  have hbegin : begin_receive result target context = ok (ReceiveEffect.ReceiveRejected result context) := by
    simp only [begin_receive, plan_receive_until_replay result.refined.control target h.received,
      bind_tc_ok, if_true, ratchet.refined.prepare_cached_receive, h.consumed, receive_rejected]
  exact (show ReceiveRun execute openReply result target context result core.option.Option.None from
    ⟨_, hbegin, .rejected result context⟩).driver_eq

end beaconcrypt_core.ratchet.concrete
