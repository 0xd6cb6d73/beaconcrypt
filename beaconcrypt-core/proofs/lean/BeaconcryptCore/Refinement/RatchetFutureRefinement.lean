import BeaconcryptCore.Refinement.RatchetEffectRefinement
import BeaconcryptCore.PanicFreedom.RatchetReceive

/-!
# Future receive refinement

A future receive derives skipped materials privately before requesting authentication of the target. The staging invariant records the exact old control prefix, each appended logical sequence, each corresponding derived material, and the chain requested at the next KDF phase. The ideal PQXDH and ratchet models are unchanged.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- Private control derivations preserve the entry prefix and append exactly the next sequence numbers. -/
structure FutureControlRefines (entry : ratchet.control.RatchetState) (count : Nat)
    (working : ratchet.control.RatchetState) : Prop where
  sendSequence : working.send_sequence = entry.send_sequence
  receiveSequence : working.receive_sequence.val = entry.receive_sequence.val + count
  cacheLength : working.receive_cache.len.val = entry.receive_cache.len.val + count
  cachePrefix : ∀ i, i < entry.receive_cache.len.val →
    working.receive_cache.entries.val[i]! = entry.receive_cache.entries.val[i]!
  cacheAppended : ∀ j, j < count →
    (working.receive_cache.entries.val[entry.receive_cache.len.val + j]!).val =
      entry.receive_sequence.val + j + 1

/-- Staged slots contain exactly the derived skipped materials, and every other slot is empty. -/
structure FutureStagedRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (chain : ratchet.RatchetChain) (base first count : Nat)
    (slots : Array (core.option.Option (ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial)) 50#usize) : Prop where
  staged : ∀ j, j < count →
    ∃ cached : ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial,
      slots.val[first + j]! = core.option.Option.Some cached ∧
      cached.sequence.val = base + j + 1 ∧
      cached.material = Ratchet.msgKeyAt cr chain j
  empty : ∀ i, i < 50 → (i < first ∨ first + count ≤ i) →
    slots.val[i]! = core.option.Option.None

/-- A live KDF continuation owns a private prefix of the admitted future derivations. -/
structure FutureKdfRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context) : Prop where
  entryRefines : KernelRefines cr origin send receive entry
  entryEq : pending.entry = entry
  contextEq : pending.context = context
  targetEq : pending.target = target
  future : receive.n < target.val
  capacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50
  position : count < target.val - receive.n
  firstSlot : pending.first_slot = entry.refined.control.receive_cache.len
  skipped : pending.skipped.val = count
  remaining : pending.remaining.val = target.val - receive.n - count
  control : FutureControlRefines entry.refined.control count pending.working_control
  staging : FutureStagedRefines cr receive.ck receive.n
    entry.refined.control.receive_cache.len.val count pending.staged_slots
  requestInput : pending.request.input = (Ratchet.chainAt cr receive.ck count).bytes
  requestInfo : pending.request.info = ratchet.SYM_RATCHET_INFO

/-- An array update changes exactly its selected in-bounds cell. -/
theorem array_set_get! {α : Type} [Inhabited α] {n : Std.Usize}
    (a : Array α n) (slot : Std.Usize) (value : α) (i : Nat) (hi : i < a.length) :
    (a.set slot value).val[i]! = if slot.val = i then value else a.val[i]! := by
  by_cases heq : slot.val = i <;>
    simp [Array.set_val_eq, heq, show i < n.val by simpa using hi]

/-- Appending a skipped derivation preserves the exact control-prefix relation. -/
theorem FutureControlRefines.advance
    (entry working : ratchet.control.RatchetState) (count : Nat)
    (h : FutureControlRefines entry count working)
    (hsequence : working.receive_sequence.val + 1 < 2 ^ 64)
    (hcapacity : working.receive_cache.len.val < 50) :
    ∃ advanced,
      advance_receive working = ok advanced ∧
      advanced.sequence = core.option.Option.Some advanced.state.receive_sequence ∧
      advanced.slot = core.option.Option.Some working.receive_cache.len ∧
      FutureControlRefines entry (count + 1) advanced.state := by
  have hmax : working.receive_sequence ≠ core.num.U64.MAX := fun hmax => by
    simp [hmax, core.num.U64.MAX, U64.rMax] at hsequence
  obtain ⟨sequence, hnext, hnextval⟩ := receive_next_ok working hmax
  obtain ⟨cache, hcache, hcachelen, hcacheentries⟩ := SequenceCache.append_ok working.receive_cache sequence (by omega) hcapacity
  refine ⟨_, advance_receive_of_append_some working hmax sequence hnext cache working.receive_cache.len hcache, rfl, rfl, ?_⟩
  rcases h with ⟨hsend, hseq, hlen, hprefix, happended⟩
  refine ⟨hsend, by simp only [hnextval, hseq, Nat.add_assoc], by simp only [hcachelen, hlen, Nat.add_assoc], ?_, ?_⟩
  · intro i hi
    rw [hcacheentries, array_set_get! _ _ _ _ (by scalar_tac), if_neg (by scalar_tac)]
    exact hprefix i hi
  · intro j hj
    rw [hcacheentries, array_set_get! _ _ _ _ (by scalar_tac)]
    split_ifs with heq
    · scalar_tac
    · exact happended j (by scalar_tac)

/-- Installing the next canonical skipped material preserves the exact staging relation. -/
theorem FutureStagedRefines.append
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (chain : ratchet.RatchetChain) (base first count : Nat)
    (slots : Array (core.option.Option (ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial)) 50#usize)
    (h : FutureStagedRefines cr chain base first count slots)
    (slot : Std.Usize) (sequence : Std.U64)
    (hslot : slot.val = first + count) (hsequence : sequence.val = base + count + 1)
    (hcapacity : first + count < 50) :
    FutureStagedRefines cr chain base first (count + 1)
      (slots.set slot (core.option.Option.Some { sequence, material := Ratchet.msgKeyAt cr chain count })) := by
  constructor
  · intro j hj
    by_cases heq : j = count
    · subst j
      exact ⟨{ sequence, material := Ratchet.msgKeyAt cr chain count }, by rw [array_set_get! _ _ _ _ (by scalar_tac), if_pos hslot], hsequence, rfl⟩
    · rw [array_set_get! _ _ _ _ (by scalar_tac), if_neg (by omega)]
      exact h.staged j (by omega)
  · intro i hi hout
    rw [array_set_get! _ _ _ _ (by simpa using hi), if_neg (by omega)]
    exact h.empty i hi (by omega)

/-- A live bounded logical slot exposes its exact cached sequence. -/
theorem receive_key_at_some (state : ratchet.control.RatchetState)
    (slot : Std.U8) (sequence : Std.U64)
    (hlen : slot.val < state.receive_cache.len.val) (hcap : slot.val < 50)
    (hentry : state.receive_cache.entries.val[slot.val]! = sequence) :
    RatchetState.receive_key_at state slot = ok (core.option.Option.Some sequence) := by
  simp only [RatchetState.receive_key_at, SequenceCache.entry, lift, capacity_eq_ok, bind_tc_ok,
    if_pos (show slot < state.receive_cache.len by scalar_tac),
    if_pos (show UScalar.cast UScalarTy.Usize slot < UScalar.cast UScalarTy.Usize 50#u64 by scalar_tac),
    entries_index_eq_ok state.receive_cache slot hcap, hentry]

/-- Bounded array reads agree with the total list-index notation used by the invariants. -/
theorem array_index_get! {α : Type} [Inhabited α] {n : Std.Usize}
    (a : Array α n) (i : Std.Usize) (h : i.val < a.length) :
    a.index_usize i = ok a.val[i.val]! := by
  simpa only [List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i.val < a.val.length by simpa using h), Option.getD_some]
    using array_index_eq_ok a i h

/-- A non-final KDF response advances the private staging transaction by exactly one derivation. -/
theorem FutureKdfRefines.resume_more
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context)
    (h : FutureKdfRefines cr origin send receive entry context target count pending)
    (hmore : 1 < pending.remaining.val) (response : ratchet.RatchetKdfResponse)
    (hresponse : ResponseRefines cr (Ratchet.chainAt cr receive.ck count) response) :
    ∃ next,
      pending.resume response = ok (ReceiveEffect.ReceiveKdfRequested next) ∧
      FutureKdfRefines cr origin send receive entry context target (count + 1) next := by
  have hreceive := h.entryRefines.receiveControl.seq
  rcases h with ⟨hentry, hentryEq, hcontext, htarget, hfuture, hcap, hpos, hfirst, hskipped, hremaining, hcontrol, hstaging, hinput, hinfo⟩
  obtain ⟨hsend, hsequence, hlen, hprefix, happended⟩ := hcontrol
  obtain ⟨advanced, hadvanced, hadvancedSequence, hadvancedSlot, hadvancedControl⟩ :=
    FutureControlRefines.advance entry.refined.control pending.working_control count
      ⟨hsend, hsequence, hlen, hprefix, happended⟩ (by scalar_tac) (by omega)
  obtain ⟨hadvsend, hadvsequence, hadvlen, hadvprefix, hadvappended⟩ := hadvancedControl
  have hlast := hadvappended count (by omega)
  have hkey : advanced.state.receive_cache.entries.val[pending.working_control.receive_cache.len.val]! = advanced.state.receive_sequence :=
    UScalar.eq_of_val_eq (by simpa only [hlen, hadvsequence, Nat.add_assoc] using hlast)
  have hget := receive_key_at_some advanced.state pending.working_control.receive_cache.len advanced.state.receive_sequence (by omega) (by omega) hkey
  have hempty : pending.staged_slots.val[(UScalar.cast UScalarTy.Usize pending.working_control.receive_cache.len).val]! = core.option.Option.None :=
    hstaging.empty _ (by scalar_tac) (Or.inr (by scalar_tac))
  have hindex : pending.staged_slots.index_usize (UScalar.cast UScalarTy.Usize pending.working_control.receive_cache.len) = ok core.option.Option.None := by
    simpa only [hempty] using array_index_get! pending.staged_slots (UScalar.cast UScalarTy.Usize pending.working_control.receive_cache.len) (by scalar_tac)
  obtain ⟨nextSlot, hsum, hsumval⟩ := uscalar_add_eq_ok (UScalar.cast UScalarTy.Usize pending.first_slot) (UScalar.cast UScalarTy.Usize pending.skipped) (by scalar_tac)
  have hnextSlot : nextSlot = UScalar.cast UScalarTy.Usize pending.working_control.receive_cache.len := by scalar_tac
  obtain ⟨skipped, hskippedNext, hskippedVal⟩ := uscalar_add_eq_ok pending.skipped 1#u8 (by scalar_tac)
  obtain ⟨remaining, hremainingNext, hremainingVal⟩ := uscalar_sub_eq_ok pending.remaining 1#u8 (by scalar_tac)
  let next : ReceiveKdf Context := {
    pending with
    working_control := advanced.state
    staged_slots := pending.staged_slots.set (UScalar.cast UScalarTy.Usize pending.working_control.receive_cache.len)
      (core.option.Option.Some { sequence := advanced.state.receive_sequence, material := Ratchet.msgKeyAt cr receive.ck count })
    skipped := skipped
    remaining := remaining
    request := { input := (cr.kdfChain (Ratchet.chainAt cr receive.ck count)).bytes, info := ratchet.SYM_RATCHET_INFO }
  }
  refine ⟨next, ?_, ?_⟩
  · simp only [ReceiveKdf.resume,
      if_neg (show pending.remaining ≠ 0#u8 by scalar_tac),
      if_neg (show pending.remaining ≠ 1#u8 by scalar_tac),
      hadvanced, hadvancedSequence, hadvancedSlot, lift, hget,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
      bind_tc_ok, capacity_eq_ok]
    simp only [beq_self_eq_true, if_true,
      if_neg (show ¬UScalar.cast UScalarTy.Usize pending.working_control.receive_cache.len ≥ UScalar.cast UScalarTy.Usize 50#u64 by scalar_tac),
      hsum, hnextSlot, hindex, core.option.Option.is_some, Std.core.option.Option.is_some,
      bind_tc_ok, if_neg (show ¬advanced.state.receive_sequence ≥ pending.target by scalar_tac)]
    simp only [core.option.Option.None, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [hresponse]
    simp only [bind_tc_ok, hskippedNext, hremainingNext, RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new]
    rw [array_update_eq_ok _ _ _ (by scalar_tac)]
    rfl
  · refine ⟨hentry, hentryEq, hcontext, htarget, hfuture, hcap, ?_, hfirst, ?_, ?_,
      ⟨hadvsend, hadvsequence, hadvlen, hadvprefix, hadvappended⟩, ?_, ?_, rfl⟩
    · omega
    · simpa [next, hskipped] using hskippedVal
    · simpa [next, hremaining, Nat.sub_sub, Nat.add_assoc] using hremainingVal
    · exact FutureStagedRefines.append cr receive.ck receive.n _ count pending.staged_slots hstaging
        _ _ (by scalar_tac) (by omega) (by omega)
    · simp only [next, Ratchet.chainAt, Function.iterate_succ_apply']

end beaconcrypt_core.ratchet.concrete
