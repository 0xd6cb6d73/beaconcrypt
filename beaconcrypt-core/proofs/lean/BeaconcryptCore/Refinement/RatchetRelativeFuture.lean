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

end beaconcrypt_core.ratchet.concrete
