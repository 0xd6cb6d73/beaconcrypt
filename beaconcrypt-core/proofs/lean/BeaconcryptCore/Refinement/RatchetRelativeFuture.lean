import BeaconcryptCore.Refinement.RatchetStructuralFuture
import BeaconcryptCore.Refinement.RatchetExecution

/-!
# Relative future derivation from structurally valid entries

Future receive preparation needs structural cache validity, but does not require old cached material or the entry chain to have canonical provenance from a session origin. This invariant retains the exact new chain and message-material derivation relative to the supplied entry receive chain.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- A live KDF continuation owns a private prefix of the admitted future derivations. -/
structure RelativeFutureKdf
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context) : Prop where
  entryValid : ratchet.refined.ValidRefined entry.refined
  entryEq : pending.entry = entry
  contextEq : pending.context = context
  targetEq : pending.target = target
  future : entry.refined.control.receive_sequence.val < target.val
  capacity : entry.refined.control.receive_cache.len.val + (target.val - entry.refined.control.receive_sequence.val - 1) ≤ 50
  position : count < target.val - entry.refined.control.receive_sequence.val
  firstSlot : pending.first_slot = entry.refined.control.receive_cache.len
  skipped : pending.skipped.val = count
  remaining : pending.remaining.val = target.val - entry.refined.control.receive_sequence.val - count
  control : FutureControlRefines entry.refined.control count pending.working_control
  staging : FutureStagedRefines cr entry.refined.receive_chain entry.refined.control.receive_sequence.val
    entry.refined.control.receive_cache.len.val count pending.staged_slots
  requestInput : pending.request.input = (Ratchet.chainAt cr entry.refined.receive_chain count).bytes
  requestInfo : pending.request.info = ratchet.SYM_RATCHET_INFO

/-- A non-final KDF response advances the private staging transaction by exactly one derivation. -/
theorem RelativeFutureKdf.resume_more
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context)
    (h : RelativeFutureKdf cr entry context target count pending)
    (hmore : 1 < pending.remaining.val) (response : ratchet.RatchetKdfResponse)
    (hresponse : ResponseRefines cr (Ratchet.chainAt cr entry.refined.receive_chain count) response) :
    ∃ next,
      pending.resume response = ok (ReceiveEffect.ReceiveKdfRequested next) ∧
      RelativeFutureKdf cr entry context target (count + 1) next := by
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
      (core.option.Option.Some { sequence := advanced.state.receive_sequence, material := Ratchet.msgKeyAt cr entry.refined.receive_chain count })
    skipped := skipped
    remaining := remaining
    request := { input := (cr.kdfChain (Ratchet.chainAt cr entry.refined.receive_chain count)).bytes, info := ratchet.SYM_RATCHET_INFO }
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
    · exact FutureStagedRefines.append cr entry.refined.receive_chain entry.refined.control.receive_sequence.val _ count pending.staged_slots hstaging
        _ _ (by scalar_tac) (by omega) (by omega)
    · simp only [next, Ratchet.chainAt, Function.iterate_succ_apply']

/-- Every admitted future request starts the exact private derivation invariant. -/
theorem relative_begin_receive_future
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : ratchet.refined.ValidRefined entry.refined)
    (hfuture : entry.refined.control.receive_sequence.val < target.val)
    (hcapacity : entry.refined.control.receive_cache.len.val + (target.val - entry.refined.control.receive_sequence.val - 1) ≤ 50) :
    ∃ pending, begin_receive entry target context = ok (ReceiveEffect.ReceiveKdfRequested pending) ∧
      RelativeFutureKdf cr entry context target 0 pending := by
  obtain ⟨derivations, hplan, hderivations⟩ := plan_receive_until_accept entry.refined.control target
    hfuture
    hcapacity
  obtain ⟨skipped, hskipped, hskippedval⟩ := uscalar_sub_eq_ok derivations 1#u64 (by scalar_tac)
  have hempty := ratchet.refined.refined_receive_slots_are_empty_true entry.refined entry.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped) (by scalar_tac) (fun i hi hj => h.slots.empty i hi (by scalar_tac))
  obtain ⟨slots, hslots, hslotsempty⟩ := empty_material_slots_exact
  let pending : ReceiveKdf Context := {
    entry, context, target, working_control := entry.refined.control, staged_slots := slots,
    first_slot := entry.refined.control.receive_cache.len, skipped := 0#u8,
    remaining := UScalar.cast UScalarTy.U8 derivations,
    request := { input := entry.refined.receive_chain.bytes, info := ratchet.SYM_RATCHET_INFO }
  }
  refine ⟨pending, ?_, ?_⟩
  · simp only [begin_receive, hplan, bind_tc_ok,
      if_neg (show derivations ≠ 0#u64 by scalar_tac),
      hskipped, if_neg (show ¬skipped > RATCHET_MAX_GAP by scalar_tac),
      lift, RatchetState.receive_cache_len, hempty, if_true, RatchetChain.as_bytes,
      SymmetricRatchetKdfRequest.new, hslots]
    rfl
  · refine ⟨h, rfl, rfl, rfl, hfuture, hcapacity, by omega, rfl, rfl,
      by dsimp [pending]; scalar_tac,
      ⟨rfl, by simp [pending], by simp [pending], fun _ _ => rfl, by simp⟩,
      ⟨by simp, fun i hi _ => hslotsempty i hi⟩, ?_, rfl⟩
    simp [pending, Ratchet.chainAt]

/-- A completed future transaction retains exactly the old cache and the newly derived skipped keys. -/
structure RelativeFuturePending
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial) : Prop where
  entryValid : ratchet.refined.ValidRefined entry.refined
  future : entry.refined.control.receive_sequence.val < target.val
  capacity : entry.refined.control.receive_cache.len.val + (target.val - entry.refined.control.receive_sequence.val - 1) ≤ 50
  firstSlot : pending.first_slot = entry.refined.control.receive_cache.len
  skipped : pending.skipped.val = target.val - entry.refined.control.receive_sequence.val - 1
  committedSend : pending.committed_control.send_sequence = entry.refined.control.send_sequence
  committedReceive : pending.committed_control.receive_sequence = target
  committedLength : pending.committed_control.receive_cache.len.val =
    entry.refined.control.receive_cache.len.val + (target.val - entry.refined.control.receive_sequence.val - 1)
  cachePrefix : ∀ i, i < entry.refined.control.receive_cache.len.val →
    pending.committed_control.receive_cache.entries.val[i]! = entry.refined.control.receive_cache.entries.val[i]!
  cacheAppended : ∀ j, j < target.val - entry.refined.control.receive_sequence.val - 1 →
    (pending.committed_control.receive_cache.entries.val[entry.refined.control.receive_cache.len.val + j]!).val =
      entry.refined.control.receive_sequence.val + j + 1
  staging : FutureStagedRefines cr entry.refined.receive_chain entry.refined.control.receive_sequence.val entry.refined.control.receive_cache.len.val
    (target.val - entry.refined.control.receive_sequence.val - 1) pending.staged_slots
  finalChain : pending.final_receive_chain = Ratchet.chainAt cr entry.refined.receive_chain (target.val - entry.refined.control.receive_sequence.val)
  targetSequence : pending.target_sequence = target
  targetMaterial : pending.target_material = Ratchet.msgKeyAt cr entry.refined.receive_chain (target.val - entry.refined.control.receive_sequence.val - 1)

/-- The open request carries the original entry/context and a fully refined future transaction. -/
def RelativeFutureOpen
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (opened : ReceiveOpen Context) : Prop :=
  ∃ pending, opened.entry = entry ∧ opened.context = context ∧
    opened.prepared = ratchet.refined.PreparedReceive.PreparedReceiveFutureCase pending ∧
    RelativeFuturePending cr entry target pending

/-- The authentication target is absent from the private skipped-key cache. -/
theorem RelativeFuturePending.target_absent
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : RelativeFuturePending cr entry target pending) :
    lookup_receive_key pending.committed_control target = ok core.option.Option.None := by
  apply lookup_receive_key_of_not_mem _ _ (show pending.committed_control.Wf from by
    change pending.committed_control.receive_cache.len.val ≤ 50
    rw [h.committedLength]
    exact h.capacity)
  intro hmem
  obtain ⟨i, hi, heq⟩ := (mem_cacheSeqs_iff _ _).1 hmem
  by_cases hold : i < entry.refined.control.receive_cache.len.val
  · have hpast := h.entryValid.control.past (entry.refined.control.receive_cache.entries.val[i]!).val
      ((mem_cacheSeqs_iff _ _).2 ⟨i, hold, rfl⟩)
    rw [h.cachePrefix i hold] at heq
    have hfuture := h.future
    omega
  · have happended := h.cacheAppended (i - entry.refined.control.receive_cache.len.val) (by have hlen := h.committedLength; omega)
    rw [Nat.add_sub_of_le (by omega), heq] at happended
    have hlen := h.committedLength
    have hfuture := h.future
    omega


/-- Every transaction satisfying the semantic staging invariant passes production validation. -/
theorem RelativeFuturePending.valid
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (pending : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : RelativeFuturePending cr entry target pending) :
    ratchet.refined.pending_receive_is_valid entry.refined pending target = ok true := by
  refine ratchet.refined.pending_receive_is_valid_true entry.refined pending target
    h.targetSequence h.future
    h.firstSlot h.committedSend h.committedReceive
    h.skipped
    (by simpa only [h.firstSlot, h.skipped] using h.capacity)
    (by simpa only [h.firstSlot, h.skipped] using h.committedLength)
    (h.target_absent cr entry target pending)
    (by simpa only [h.firstSlot] using h.cachePrefix)
    (by simpa only [h.firstSlot] using h.entryValid.slots.empty)
    (fun i hi hj => h.staging.empty i hi (Or.inr (by simpa only [h.firstSlot, h.skipped] using hj))) ?_
  intro j hj
  obtain ⟨cached, hcached, hsequence, _⟩ := h.staging.staged j (by simpa only [h.skipped] using hj)
  refine ⟨cached, by simpa only [h.firstSlot] using hcached,
    hsequence,
    UScalar.eq_of_val_eq ?_⟩
  simpa only [h.firstSlot, hsequence] using h.cacheAppended j (by simpa only [h.skipped] using hj)

/-- The last canonical KDF response produces the exact validated future open phase. -/
theorem RelativeFutureKdf.resume_last
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context)
    (h : RelativeFutureKdf cr entry context target count pending)
    (hlast : pending.remaining.val = 1) (response : ratchet.RatchetKdfResponse)
    (hresponse : ResponseRefines cr (Ratchet.chainAt cr entry.refined.receive_chain count) response) :
    ∃ opened, pending.resume response = ok (ReceiveEffect.ReceiveOpenRequested opened) ∧
      RelativeFutureOpen cr entry context target opened := by
  have hcount : count = target.val - entry.refined.control.receive_sequence.val - 1 := by
    have hremaining := h.remaining
    have hposition := h.position
    omega
  have hmax : pending.working_control.receive_sequence ≠ core.num.U64.MAX := by
    have hsequence := h.control.receiveSequence
    have hfuture := h.future
    simp only [core.num.U64.MAX, U64.rMax]
    scalar_tac
  obtain ⟨advanced, hadvanced, hadvsequence, hadvsend, hadvcache, hadvresult⟩ :=
    advance_receive_target_ok pending.working_control hmax
  have hadvtarget : advanced.state.receive_sequence = target := by
    have hsequence := h.control.receiveSequence
    have hfuture := h.future
    scalar_tac
  let transaction : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial := {
    committed_control := advanced.state,
    final_receive_chain := cr.kdfChain (Ratchet.chainAt cr entry.refined.receive_chain count),
    staged_slots := pending.staged_slots,
    target_sequence := target,
    target_material := cr.kdfMsg (Ratchet.chainAt cr entry.refined.receive_chain count),
    first_slot := pending.first_slot, skipped := pending.skipped
  }
  have htransaction : RelativeFuturePending cr entry target transaction := by
    refine ⟨h.entryValid, h.future, h.capacity, h.firstSlot,
      h.skipped.trans hcount, hadvsend.trans h.control.sendSequence, hadvtarget,
      by simpa only [transaction, hadvcache, hcount] using h.control.cacheLength,
      by simpa only [transaction, hadvcache] using h.control.cachePrefix,
      by simpa only [transaction, hadvcache, hcount] using h.control.cacheAppended,
      by simpa only [transaction, hcount] using h.staging,
      ?_, rfl, by simp only [transaction, Ratchet.msgKeyAt, hcount]⟩
    have hsteps : target.val - entry.refined.control.receive_sequence.val = count + 1 := by have hfuture := h.future; omega
    simp only [transaction, hsteps, Ratchet.chainAt, Function.iterate_succ_apply']
  refine ⟨{ entry, context, prepared := ratchet.refined.PreparedReceive.PreparedReceiveFutureCase transaction },
    ?_, ⟨transaction, rfl, rfl, rfl, htransaction⟩⟩
  simp only [ReceiveKdf.resume, if_neg (show pending.remaining ≠ 0#u8 by scalar_tac),
    if_pos (show pending.remaining = 1#u8 by scalar_tac), hadvanced, hadvresult,
    hadvtarget, h.targetEq, if_true, bind_tc_ok]
  rw [hresponse]
  simp only [bind_tc_ok, h.entryEq, h.contextEq]
  have hvalid := htransaction.valid cr entry target transaction
  dsimp only [transaction] at hvalid
  simp only [hvalid, bind_tc_ok, if_true, transaction]


/-- The remaining counter is a constructive bound for the exact extracted KDF execution. -/
theorem relative_future_kdf_trace_count
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (n : Nat) :
    ∀ (count : Nat) (pending : ReceiveKdf Context), pending.remaining.val = n →
      RelativeFutureKdf (withInterpreter cr execute) entry context target count pending →
      ∃ opened, ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending)
          (ReceiveEffect.ReceiveOpenRequested opened) n ∧
        RelativeFutureOpen (withInterpreter cr execute) entry context target opened := by
  induction n with
  | zero =>
    intro count pending hremaining h
    have hpositive := h.position
    have hcounter := h.remaining
    omega
  | succ n ih =>
    intro count pending hremaining h
    have hresponse := interpreter_request_refines cr execute
      (Ratchet.chainAt (withInterpreter cr execute) entry.refined.receive_chain count) pending.request h.requestInput h.requestInfo
    by_cases hn : n = 0
    · obtain ⟨opened, hresume, hopen⟩ := h.resume_last (withInterpreter cr execute)
        entry context target count pending (by omega) (execute pending.request) hresponse
      exact ⟨opened, by simpa only [hn] using (ReceiveKdfTrace.step pending _ _ 0 hresume
          (ReceiveKdfTrace.refl (ReceiveEffect.ReceiveOpenRequested opened))), hopen⟩
    · obtain ⟨next, hresume, hnext⟩ := h.resume_more (withInterpreter cr execute)
        entry context target count pending (by omega) (execute pending.request) hresponse
      obtain ⟨opened, htrace, hopen⟩ := ih (count + 1) next
        (by have hleft := h.remaining; have hright := hnext.remaining; omega) hnext
      exact ⟨opened, ReceiveKdfTrace.step pending _ _ n hresume htrace, hopen⟩

/-- Any live semantic continuation reaches authentication in exactly its remaining KDF steps. -/
theorem RelativeFutureKdf.trace
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context)
    (h : RelativeFutureKdf (withInterpreter cr execute) entry context target count pending) :
    ∃ opened, ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending)
        (ReceiveEffect.ReceiveOpenRequested opened) pending.remaining.val ∧
      RelativeFutureOpen (withInterpreter cr execute) entry context target opened :=
  relative_future_kdf_trace_count cr execute entry context target pending.remaining.val count pending rfl h


/-- An admitted future receive constructively reaches the ideal target's authentication phase. -/
theorem relative_begin_receive_future_trace
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : ratchet.refined.ValidRefined entry.refined)
    (hfuture : entry.refined.control.receive_sequence.val < target.val)
    (hcapacity : entry.refined.control.receive_cache.len.val + (target.val - entry.refined.control.receive_sequence.val - 1) ≤ 50) :
    ∃ pending opened,
      begin_receive entry target context = ok (ReceiveEffect.ReceiveKdfRequested pending) ∧
      ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending)
        (ReceiveEffect.ReceiveOpenRequested opened) (target.val - entry.refined.control.receive_sequence.val) ∧
      RelativeFutureOpen (withInterpreter cr execute) entry context target opened := by
  obtain ⟨pending, hbegin, hpending⟩ := relative_begin_receive_future (withInterpreter cr execute) entry context target h hfuture hcapacity
  obtain ⟨opened, htrace, hopen⟩ := hpending.trace cr execute entry context target 0 pending
  exact ⟨pending, opened, hbegin, by simpa only [hpending.remaining, Nat.sub_zero] using htrace, hopen⟩

end beaconcrypt_core.ratchet.concrete
