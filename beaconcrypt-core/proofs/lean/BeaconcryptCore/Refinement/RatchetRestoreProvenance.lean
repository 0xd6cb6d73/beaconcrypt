import BeaconcryptCore.Refinement.RatchetRestoreStructural

/-! Generic restoration preserves trusted persistence provenance for arbitrary chain and material types. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core

set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.refined

/-- A physically present tagged key agrees with its trusted canonical material interpretation. -/
def DerivedMaterials {Material : Type} (materialAt : Nat → Material)
    (slots : Array (core.option.Option (CachedReceiveKey Material)) 50#usize) : Prop :=
  ∀ i, i < 50 → ∀ cached, slots.val[i]! = core.option.Option.Some cached →
    0 < cached.sequence.val ∧ cached.material = materialAt cached.sequence.val

/-- This is the historical generic restoration provenance premise, parameterized by its canonical interpretations. -/
structure RestoreProvenance {SendChain ReceiveChain Material : Type}
    (sendAt : Nat → SendChain) (receiveAt : Nat → ReceiveChain) (materialAt : Nat → Material)
    (restore : RefinedRatchetRestore SendChain ReceiveChain Material) : Prop where
  valid : ValidRestore restore
  send : restore.send_chain = sendAt restore.logical.state.send_sequence.val
  receive : restore.receive_chain = receiveAt restore.logical.state.receive_sequence.val
  materials : DerivedMaterials materialAt restore.receive_slots

/-- The published generic state carries exactly the same provenance clauses. -/
structure RefinedProvenance {SendChain ReceiveChain Material : Type}
    (sendAt : Nat → SendChain) (receiveAt : Nat → ReceiveChain) (materialAt : Nat → Material)
    (state : RefinedRatchet SendChain ReceiveChain Material) : Prop where
  valid : ValidRefined state
  send : state.send_chain = sendAt state.control.send_sequence.val
  receive : state.receive_chain = receiveAt state.control.receive_sequence.val
  materials : DerivedMaterials materialAt state.receive_slots

theorem DerivedMaterials.append {Material : Type} (materialAt : Nat → Material)
    (slots : Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
    (h : DerivedMaterials materialAt slots) (slot : Std.U8)
    (sequence : Std.U64) (material : Material)
    (hpositive : 0 < sequence.val) (hmaterial : material = materialAt sequence.val) :
    DerivedMaterials materialAt (slots.set (UScalar.cast .Usize slot)
      (core.option.Option.Some { sequence, material })) := by
  intro i hi cached hcached
  have hcast : (UScalar.cast UScalarTy.Usize slot).val = slot.val := by simp_scalar
  by_cases heq : slot.val = i
  · have hset := Array.getElem!_Nat_set_eq slots (UScalar.cast UScalarTy.Usize slot) i
      (core.option.Option.Some { sequence, material }) ⟨hcast.trans heq, by simpa using hi⟩
    simp only [Array.getElem!_Nat_eq] at hset
    have hrecord : (⟨sequence, material⟩ : CachedReceiveKey Material) = cached := by
      simpa only [Array.getElem!_Nat_eq, core.option.Option.Some, Option.some.injEq] using hset.symm.trans hcached
    simpa only [← hrecord] using And.intro hpositive hmaterial
  · have hset := Array.getElem!_Nat_set_ne slots (UScalar.cast UScalarTy.Usize slot) i
      (core.option.Option.Some { sequence, material }) (by simpa only [hcast] using heq)
    simp only [Array.getElem!_Nat_eq] at hset
    exact h i hi cached (hset.symm.trans hcached)

/-- Every attempt preserves generic provenance under precisely the trusted material premise. -/
theorem RestoreProvenance.restore {SendChain ReceiveChain Material : Type}
    (sendAt : Nat → SendChain) (receiveAt : Nat → ReceiveChain) (materialAt : Nat → Material)
    (restore : RefinedRatchetRestore SendChain ReceiveChain Material)
    (h : RestoreProvenance sendAt receiveAt materialAt restore)
    (sequence : Std.U64) (material : Material)
    (hpositive : 0 < sequence.val) (hmaterial : material = materialAt sequence.val) :
    ∃ accepted next, refined_restore_receive_key restore sequence material = ok (accepted, next) ∧
      RestoreProvenance sendAt receiveAt materialAt next := by
  obtain ⟨accepted, next, hrun, hvalid, hshape⟩ := h.valid.restore restore sequence material
  refine ⟨accepted, next, hrun, ?_⟩
  cases accepted
  · simpa only [Bool.false_eq_true, if_false] using hshape ▸ h
  · obtain ⟨hsend, hreceive, hsendCounter, hreceiveCounter, _, _, _, hslots⟩ := hshape
    refine ⟨hvalid, by simpa only [hsend, hsendCounter] using h.send,
      by simpa only [hreceive, hreceiveCounter] using h.receive, ?_⟩
    simpa only [hslots] using h.materials.append materialAt restore.receive_slots
      restore.logical.state.receive_cache.len sequence material hpositive hmaterial

/-- Trusted persisted chains establish empty restoration provenance for arbitrary types and interpretations. -/
theorem start_refined_restore_provenance {SendChain ReceiveChain Material : Type}
    (sendAt : Nat → SendChain) (receiveAt : Nat → ReceiveChain) (materialAt : Nat → Material)
    (send receive : Std.U64) (sendChain : SendChain) (receiveChain : ReceiveChain)
    (hsend : sendChain = sendAt send.val) (hreceive : receiveChain = receiveAt receive.val) :
    ∃ restore, start_refined_restore Material send receive sendChain receiveChain = ok restore ∧
      RestoreProvenance sendAt receiveAt materialAt restore := by
  obtain ⟨restore, hrun, hvalid⟩ := start_refined_restore_valid (Material := Material) send receive sendChain receiveChain
  refine ⟨restore, hrun, ?_⟩
  simp only [start_refined_restore, control.start_restore, control.RatchetState.from_counters,
    control.SequenceCache.empty, empty_material_slots, bind_tc_ok, RustM.ok.injEq] at hrun
  subst restore
  refine ⟨hvalid, hsend, hreceive, ?_⟩
  intro i hi cached hcached
  have hempty := hvalid.slots.empty i (by simp) hi
  simp only [hempty, core.option.Option.None, core.option.Option.Some, reduceCtorEq] at hcached

/-- Finishing restoration publishes exactly the generic chain and material provenance it carries. -/
theorem RestoreProvenance.finish {SendChain ReceiveChain Material : Type}
    (sendAt : Nat → SendChain) (receiveAt : Nat → ReceiveChain) (materialAt : Nat → Material)
    (restore : RefinedRatchetRestore SendChain ReceiveChain Material)
    (h : RestoreProvenance sendAt receiveAt materialAt restore) :
    ∃ state, finish_refined_restore restore = ok state ∧
      RefinedProvenance sendAt receiveAt materialAt state := by
  exact ⟨_, rfl, ⟨⟨h.valid.control, h.valid.slots⟩, h.send, h.receive, h.materials⟩⟩

end beaconcrypt_core.ratchet.refined
