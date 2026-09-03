import BeaconcryptCore.PanicFreedom.Control
import BeaconcryptCore.Refinement.RatchetRoleReachability
import BeaconcryptCore.Refinement.RatchetStructural

/-! Exact tagged-material accessors and selected-peer behavior for the raw extraction. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open ratchet.control

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.RatchetAccessors

theorem material_slots_index {Material : Type}
    (slots : Std.Array (core.option.Option (ratchet.refined.CachedReceiveKey Material)) 50#usize)
    (slot : Std.U8) (hslot : slot.val < 50) :
    slots.index_usize (Std.UScalar.cast .Usize slot) = ok slots.val[slot.val]! := by
  have hcast : (Std.UScalar.cast .Usize slot).val = slot.val := by simp_scalar
  simpa [hcast, List.getElem?_eq_getElem (show slot.val < slots.val.length from by simpa using hslot)]
    using array_index_eq_ok slots (Std.UScalar.cast .Usize slot) (by simp [hcast]; exact hslot)

theorem receive_entry_at_value {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (slot : Std.U8) (sequence : Std.U64) (cached : ratchet.refined.CachedReceiveKey Material)
    (hslot : slot.val < 50)
    (hlogical : state.control.receive_key_at slot = ok (.Some sequence))
    (hcached : state.receive_slots.val[slot.val]! = .Some cached) :
    state.receive_entry_at slot = ok (if cached.sequence = sequence then .Some (cached.sequence, cached.material) else .None) := by
  simp [ratchet.refined.RefinedRatchet.receive_entry_at, hlogical, lift, capacity_eq_ok,
    Nat.not_le.mpr hslot, apply_ite,
    material_slots_index _ _ hslot, hcached, core.option.Option.as_ref]
  split_ifs <;> scalar_tac

theorem refined_receive_key_value {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (slot : Std.U8) (sequence : Std.U64) (cached : ratchet.refined.CachedReceiveKey Material)
    (hslot : slot.val < 50)
    (hlogical : lookup_receive_key state.control sequence = ok (.Some slot))
    (hcached : state.receive_slots.val[slot.val]! = .Some cached) :
    ratchet.refined.refined_receive_key state sequence = ok (if cached.sequence = sequence then .Some cached.material else .None) := by
  simp [ratchet.refined.refined_receive_key, hlogical, lift, capacity_eq_ok,
    Nat.not_le.mpr hslot, apply_ite,
    material_slots_index _ _ hslot, hcached, core.option.Option.as_ref]
  split_ifs <;> scalar_tac

theorem refined_receive_entry_mismatched_tag_is_rejected {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (slot : Std.U8) (sequence : Std.U64) (cached : ratchet.refined.CachedReceiveKey Material)
    (hslot : slot.val < 50)
    (hlogical : state.control.receive_key_at slot = ok (.Some sequence))
    (hcached : state.receive_slots.val[slot.val]! = .Some cached) (hne : cached.sequence ≠ sequence) :
    state.receive_entry_at slot = ok .None := by
  simp [receive_entry_at_value state slot sequence cached hslot hlogical hcached, hne]

theorem refined_receive_key_mismatched_tag_is_rejected {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (slot : Std.U8) (sequence : Std.U64) (cached : ratchet.refined.CachedReceiveKey Material)
    (hslot : slot.val < 50)
    (hlogical : lookup_receive_key state.control sequence = ok (.Some slot))
    (hcached : state.receive_slots.val[slot.val]! = .Some cached) (hne : cached.sequence ≠ sequence) :
    ratchet.refined.refined_receive_key state sequence = ok .None := by
  simp [refined_receive_key_value state slot sequence cached hslot hlogical hcached, hne]

theorem advance_send_for_selected_peer_matches (peer : PeerRatchetState) :
    ∃ advanced, advance_send peer.ratchet = ok advanced ∧
      advance_send_for_peer peer.peer_id peer = ok {
        peer := { peer_id := peer.peer_id, ratchet := advanced.state }, sequence := advanced.sequence, key := advanced.key } :=
  (advance_send_total peer.ratchet).elim fun advanced hadv =>
    ⟨advanced, hadv, by simp [advance_send_for_peer, hadv, replace_ratchet_for_peer]⟩

/-- The active material prefix is populated and agrees with its control tags; no chain-derivation premise is needed by raw accessors. -/
def SlotsAligned {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material) : Prop :=
  ∀ i : Nat, i < state.control.receive_cache.len.val →
    ∃ cached : ratchet.refined.CachedReceiveKey Material,
      state.receive_slots.val[i]! = .Some cached ∧ cached.sequence = state.control.receive_cache.entries.val[i]!

def RefinedSlot {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (sequence : Std.U64) (material : Material) (slot : Std.U8) : Prop :=
  slot.val < state.control.receive_cache.len.val ∧ slot.val < 50 ∧
    state.control.receive_cache.entries.val[slot.val]! = sequence ∧
    state.receive_slots.val[slot.val]! = .Some { sequence, material }

theorem receive_key_at_live (state : RatchetState) (slot : Std.U8)
    (hlive : slot.val < state.receive_cache.len.val) (hcap : slot.val < 50) :
    state.receive_key_at slot = ok (.Some state.receive_cache.entries.val[slot.val]!) := by
  simp [RatchetState.receive_key_at, SequenceCache.entry, lift, capacity_eq_ok, hlive, hcap,
    entries_index_eq_ok _ _ hcap]

theorem refined_receive_entry_is_associated {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (hwf : state.control.Wf) (haligned : SlotsAligned state) (slot : Std.U8)
    (hlive : slot.val < state.control.receive_cache.len.val) :
    ∃ sequence material, state.receive_entry_at slot = ok (.Some (sequence, material)) ∧
      RefinedSlot state sequence material slot :=
  (haligned slot.val hlive).elim fun cached hc =>
    let hcap : slot.val < 50 := Nat.lt_of_lt_of_le hlive hwf
    ⟨cached.sequence, cached.material,
      by
        simpa [hc.2] using receive_entry_at_value state slot _ cached hcap
          (receive_key_at_live state.control slot hlive hcap) hc.1,
      hlive, hcap, hc.2.symm, hc.1⟩

theorem refined_receive_key_is_associated {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (hwf : state.control.Wf) (haligned : SlotsAligned state) (sequence : Std.U64) :
    ∃ result, ratchet.refined.refined_receive_key state sequence = ok result ∧
      (match result with
      | .Some material => ∃ slot, RefinedSlot state sequence material slot
      | .None => ¬ ∃ material slot, RefinedSlot state sequence material slot) := by
  obtain ⟨logical, hlogical⟩ := lookup_receive_key_ok state.control sequence hwf
  cases logical with
  | none =>
    refine ⟨.None, by simp [ratchet.refined.refined_receive_key, hlogical], ?_⟩
    rintro ⟨material, slot, hlive, _, hentry, _⟩
    obtain ⟨found, hfound, _⟩ := lookup_receive_key_complete state.control sequence slot.val hwf hlive hentry
    simp [hlogical] at hfound
  | some slot =>
    have hs := lookup_receive_key_sound state.control sequence slot hwf hlogical
    obtain ⟨cached, hcached, htag⟩ := haligned slot.val hs.1
    exact ⟨.Some cached.material,
      by simp [refined_receive_key_value state slot sequence cached (Nat.lt_of_lt_of_le hs.1 hwf)
          hlogical hcached, htag.trans hs.2],
      slot, hs.1, Nat.lt_of_lt_of_le hs.1 hwf, hs.2, by simpa [← htag.trans hs.2] using hcached⟩

theorem kernel_slots_aligned {AD PT CT : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {origin : ratchet.RatchetChain} {send : Ratchet.SendState ratchet.RatchetChain}
    {receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial}
    {kernel : ratchet.concrete.ConcreteRatchetKernel}
    (h : ratchet.concrete.KernelRefines cr origin send receive kernel) : SlotsAligned kernel.refined :=
  fun i hi => (h.slotSound i hi).elim fun _ hp => hp.elim fun cached hc => ⟨cached, hc.2.1, hc.2.2.1⟩

/-- Every material returned by a reachable kernel is the canonical message material for its positive wire sequence. -/
theorem refined_receive_key_is_derived {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain) (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (h : ratchet.concrete.KernelRefines cr origin send receive kernel)
    (sequence : Std.U64) (material : ratchet.RatchetMaterial)
    (hresult : ratchet.refined.refined_receive_key kernel.refined sequence = ok (.Some material)) :
    0 < sequence.val ∧ material = Ratchet.msgKeyAt cr origin (sequence.val - 1) := by
  obtain ⟨result, hlookup, hassociated⟩ := refined_receive_key_is_associated kernel.refined h.receiveControl.wf
    (kernel_slots_aligned h) sequence
  have hr : result = .Some material := RustM.ok.inj (hlookup.symm.trans hresult)
  obtain ⟨slot, hlive, _, _, hslot⟩ : ∃ slot, RefinedSlot kernel.refined sequence material slot := by
    simpa only [hr] using hassociated
  obtain ⟨p, cached, hp, hcached, _, hsequence, hmaterial⟩ := h.slotSound slot.val hlive
  have hc : cached = { sequence, material } := by simpa using hcached.symm.trans hslot
  have hseq : sequence.val = p.1 + 1 := by simpa only [hc] using hsequence
  exact ⟨by omega, by simpa [hc, hseq] using hmaterial.trans (h.receiveControl.keys p hp)⟩

/-- The exact historical structural validity premise entails the weaker active-slot premise used above. -/
theorem slotsAligned_of_valid {SendChain ReceiveChain Material : Type}
    {state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material}
    (h : ratchet.refined.ValidRefined state) : SlotsAligned state := by
  intro i hi
  have hm := h.slots i (Nat.lt_of_lt_of_le hi h.control.capacity)
  cases hs : state.receive_slots.val[i]! with
  | none => simp [hs, Nat.not_le.mpr hi] at hm
  | some cached => exact ⟨cached, rfl,
      (show i < state.control.receive_cache.len.val ∧ cached.sequence = state.control.receive_cache.entries.val[i]!
        from by simpa [hs] using hm).2⟩

theorem refined_receive_entry_is_associated_valid {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (h : ratchet.refined.ValidRefined state) (slot : Std.U8)
    (hlive : slot.val < state.control.receive_cache.len.val) :
    ∃ sequence material, state.receive_entry_at slot = ok (.Some (sequence, material)) ∧
      RefinedSlot state sequence material slot :=
  refined_receive_entry_is_associated state h.control.capacity (slotsAligned_of_valid h) slot hlive

theorem refined_receive_key_is_associated_valid {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (h : ratchet.refined.ValidRefined state) (sequence : Std.U64) :
    ∃ result, ratchet.refined.refined_receive_key state sequence = ok result ∧
      (match result with
      | .Some material => ∃ slot, RefinedSlot state sequence material slot
      | .None => ¬ ∃ material slot, RefinedSlot state sequence material slot) :=
  refined_receive_key_is_associated state h.control.capacity (slotsAligned_of_valid h) sequence

end BeaconcryptCore.Refinement.RatchetAccessors
