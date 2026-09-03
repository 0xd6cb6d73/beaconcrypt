import BeaconcryptCore.Refinement.RatchetFutureFinalization
import BeaconcryptCore.Refinement.RatchetExecution

/-! Constructive execution of every admitted future receive through its exact finite KDF trace. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- The last canonical KDF response produces the exact validated future open phase. -/
theorem FutureKdfRefines.resume_last
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context)
    (h : FutureKdfRefines cr origin send receive entry context target count pending)
    (hlast : pending.remaining.val = 1) (response : ratchet.RatchetKdfResponse)
    (hresponse : ResponseRefines cr (Ratchet.chainAt cr receive.ck count) response) :
    ∃ opened, pending.resume response = ok (ReceiveEffect.ReceiveOpenRequested opened) ∧
      FutureOpenRefines cr origin send receive entry context target opened := by
  have hcount : count = target.val - receive.n - 1 := by
    have hremaining := h.remaining
    have hposition := h.position
    omega
  have hmax : pending.working_control.receive_sequence ≠ core.num.U64.MAX := by
    have hsequence := h.control.receiveSequence
    have hreceive := h.entryRefines.receiveControl.seq
    have hfuture := h.future
    simp only [core.num.U64.MAX, U64.rMax]
    scalar_tac
  obtain ⟨advanced, hadvanced, hadvsequence, hadvsend, hadvcache, hadvresult⟩ :=
    advance_receive_target_ok pending.working_control hmax
  have hadvtarget : advanced.state.receive_sequence = target := by
    have hsequence := h.control.receiveSequence
    have hreceive := h.entryRefines.receiveControl.seq
    have hfuture := h.future
    scalar_tac
  let transaction : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial := {
    committed_control := advanced.state,
    final_receive_chain := cr.kdfChain (Ratchet.chainAt cr receive.ck count),
    staged_slots := pending.staged_slots,
    target_sequence := target,
    target_material := cr.kdfMsg (Ratchet.chainAt cr receive.ck count),
    first_slot := pending.first_slot, skipped := pending.skipped
  }
  have htransaction : FuturePendingRefines cr origin send receive entry target transaction := by
    refine ⟨h.entryRefines, h.future, h.capacity, h.firstSlot,
      h.skipped.trans hcount, hadvsend.trans h.control.sendSequence, hadvtarget,
      by simpa only [transaction, hadvcache, hcount] using h.control.cacheLength,
      by simpa only [transaction, hadvcache] using h.control.cachePrefix,
      by simpa only [transaction, hadvcache, hcount, h.entryRefines.receiveControl.seq] using h.control.cacheAppended,
      by simpa only [transaction, hcount] using h.staging,
      ?_, rfl, by simp only [transaction, Ratchet.msgKeyAt, hcount]⟩
    have hsteps : target.val - receive.n = count + 1 := by have hfuture := h.future; omega
    simp only [transaction, hsteps, Ratchet.chainAt, Function.iterate_succ_apply']
  refine ⟨{ entry, context, prepared := ratchet.refined.PreparedReceive.PreparedReceiveFutureCase transaction },
    ?_, ⟨transaction, rfl, rfl, rfl, htransaction⟩⟩
  simp only [ReceiveKdf.resume, if_neg (show pending.remaining ≠ 0#u8 by scalar_tac),
    if_pos (show pending.remaining = 1#u8 by scalar_tac), hadvanced, hadvresult,
    hadvtarget, h.targetEq, if_true, bind_tc_ok]
  rw [hresponse]
  simp only [bind_tc_ok, h.entryEq, h.contextEq]
  have hvalid := htransaction.valid cr origin send receive entry target transaction
  dsimp only [transaction] at hvalid
  simp only [hvalid, bind_tc_ok, if_true, transaction]

/-- The remaining counter is a constructive bound for the exact extracted KDF execution. -/
theorem future_kdf_trace_count
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (n : Nat) :
    ∀ (count : Nat) (pending : ReceiveKdf Context), pending.remaining.val = n →
      FutureKdfRefines (withInterpreter cr execute) origin send receive entry context target count pending →
      ∃ opened, ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending)
          (ReceiveEffect.ReceiveOpenRequested opened) n ∧
        FutureOpenRefines (withInterpreter cr execute) origin send receive entry context target opened := by
  induction n with
  | zero =>
    intro count pending hremaining h
    have hpositive := h.position
    have hcounter := h.remaining
    omega
  | succ n ih =>
    intro count pending hremaining h
    have hresponse := interpreter_request_refines cr execute
      (Ratchet.chainAt (withInterpreter cr execute) receive.ck count) pending.request h.requestInput h.requestInfo
    by_cases hn : n = 0
    · obtain ⟨opened, hresume, hopen⟩ := h.resume_last (withInterpreter cr execute) origin send receive
        entry context target count pending (by omega) (execute pending.request) hresponse
      exact ⟨opened, by simpa only [hn] using (ReceiveKdfTrace.step pending _ _ 0 hresume
          (ReceiveKdfTrace.refl (ReceiveEffect.ReceiveOpenRequested opened))), hopen⟩
    · obtain ⟨next, hresume, hnext⟩ := h.resume_more (withInterpreter cr execute) origin send receive
        entry context target count pending (by omega) (execute pending.request) hresponse
      obtain ⟨opened, htrace, hopen⟩ := ih (count + 1) next
        (by have hleft := h.remaining; have hright := hnext.remaining; omega) hnext
      exact ⟨opened, ReceiveKdfTrace.step pending _ _ n hresume htrace, hopen⟩

/-- Any live semantic continuation reaches authentication in exactly its remaining KDF steps. -/
theorem FutureKdfRefines.trace
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (count : Nat)
    (pending : ReceiveKdf Context)
    (h : FutureKdfRefines (withInterpreter cr execute) origin send receive entry context target count pending) :
    ∃ opened, ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending)
        (ReceiveEffect.ReceiveOpenRequested opened) pending.remaining.val ∧
      FutureOpenRefines (withInterpreter cr execute) origin send receive entry context target opened :=
  future_kdf_trace_count cr execute origin send receive entry context target pending.remaining.val count pending rfl h

/-- An admitted future receive constructively reaches the ideal target's authentication phase. -/
theorem KernelRefines.begin_receive_future_trace
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hfuture : receive.n < target.val)
    (hcapacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50) :
    ∃ pending opened,
      begin_receive entry target context = ok (ReceiveEffect.ReceiveKdfRequested pending) ∧
      ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending)
        (ReceiveEffect.ReceiveOpenRequested opened) (target.val - receive.n) ∧
      FutureOpenRefines (withInterpreter cr execute) origin send receive entry context target opened := by
  obtain ⟨pending, hbegin, hpending⟩ := h.begin_receive_future (withInterpreter cr execute) origin send receive
    entry context target hfuture hcapacity
  obtain ⟨opened, htrace, hopen⟩ := hpending.trace cr execute origin send receive entry context target 0 pending
  exact ⟨pending, opened, hbegin, by simpa only [hpending.remaining, Nat.sub_zero] using htrace, hopen⟩

end beaconcrypt_core.ratchet.concrete
