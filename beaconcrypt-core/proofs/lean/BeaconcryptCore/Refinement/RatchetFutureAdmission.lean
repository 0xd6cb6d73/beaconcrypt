import BeaconcryptCore.Refinement.RatchetFutureRefinement
import BeaconcryptCore.Refinement.RatchetReceiveLoopExact

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- The production empty-slot constructor creates fifty empty material cells. -/
theorem empty_material_slots_exact :
    ∃ slots, ratchet.refined.empty_material_slots ratchet.RatchetMaterial = ok slots ∧
      ∀ i, i < 50 → slots.val[i]! = core.option.Option.None := by
  refine ⟨_, rfl, ?_⟩
  change ∀ i, i < 50 → (List.replicate 50 (core.option.Option.None : core.option.Option (ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial)))[i]! = core.option.Option.None
  intro i hi
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show i < (List.replicate 50 (core.option.Option.None : core.option.Option (ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial))).length by simpa using hi), List.getElem_replicate, Option.getD_some]

/-- Every admitted future request starts the exact private derivation invariant. -/
theorem KernelRefines.begin_receive_future
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines cr origin send receive entry)
    (hfuture : receive.n < target.val)
    (hcapacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50) :
    ∃ pending, begin_receive entry target context = ok (ReceiveEffect.ReceiveKdfRequested pending) ∧
      FutureKdfRefines cr origin send receive entry context target 0 pending := by
  obtain ⟨derivations, hplan, hderivations⟩ := plan_receive_until_accept entry.refined.control target
    (by simpa only [h.receiveControl.seq] using hfuture)
    (by simpa only [h.receiveControl.seq] using hcapacity)
  obtain ⟨skipped, hskipped, hskippedval⟩ := uscalar_sub_eq_ok derivations 1#u64 (by have hseq := h.receiveControl.seq; scalar_tac)
  have hempty := ratchet.refined.refined_receive_slots_are_empty_true entry.refined entry.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped) (by have hseq := h.receiveControl.seq; scalar_tac) (fun i hi hj => h.slotsAboveLenEmpty i hi (by have hseq := h.receiveControl.seq; scalar_tac))
  obtain ⟨slots, hslots, hslotsempty⟩ := empty_material_slots_exact
  let pending : ReceiveKdf Context := {
    entry, context, target, working_control := entry.refined.control, staged_slots := slots,
    first_slot := entry.refined.control.receive_cache.len, skipped := 0#u8,
    remaining := UScalar.cast UScalarTy.U8 derivations,
    request := { input := entry.refined.receive_chain.bytes, info := ratchet.SYM_RATCHET_INFO }
  }
  refine ⟨pending, ?_, ?_⟩
  · simp only [begin_receive, hplan, bind_tc_ok,
      if_neg (show derivations ≠ 0#u64 by have hseq := h.receiveControl.seq; scalar_tac),
      hskipped, if_neg (show ¬skipped > RATCHET_MAX_GAP by have hseq := h.receiveControl.seq; scalar_tac),
      lift, RatchetState.receive_cache_len, hempty, if_true, RatchetChain.as_bytes,
      SymmetricRatchetKdfRequest.new, hslots]
    rfl
  · refine ⟨h, rfl, rfl, rfl, hfuture, hcapacity, by omega, rfl, rfl,
      by have hseq := h.receiveControl.seq; dsimp [pending]; scalar_tac,
      ⟨rfl, by simp [pending], by simp [pending], fun _ _ => rfl, by simp⟩,
      ⟨by simp, fun i hi _ => hslotsempty i hi⟩, ?_, rfl⟩
    simpa [pending, Ratchet.chainAt] using congrArg RatchetChain.bytes h.receiveChain

end beaconcrypt_core.ratchet.concrete
