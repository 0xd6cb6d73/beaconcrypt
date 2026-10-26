import BeaconcryptCore.Refinement.RatchetInterpreter

/-! Lifetime reachability of one extracted role under one fixed pure KDF interpreter. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

/-- Exact represented receive reachability and material provenance, plus derivational reachability of the sending chain from its fixed origin. -/
def RoleReachable {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (kernel : ConcreteRatchetKernel) : Prop :=
  ∃ send receive, KernelRefines cr receiveOrigin send receive kernel ∧
    send.ck = Ratchet.chainAt cr sendOrigin send.n

theorem send_successor_reachable {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (h : send.ck = Ratchet.chainAt cr origin send.n) :
    cr.kdfChain send.ck = Ratchet.chainAt cr origin (send.n + 1) := by
  simp [h, Ratchet.chainAt, Function.iterate_succ_apply']

/-- Execute the extracted send phases with a fixed request interpreter and arbitrary seal result. -/
def sealNext {Context Output : Type} (execute : KdfInterpreter)
    (kernel : ConcreteRatchetKernel) (context : Context)
    (sealCallback : RatchetMaterial → Std.U64 → Context → core.option.Option Output) :
    RustM (ConcreteRatchetKernel × core.option.Option Output) := do
  let started ← begin_send kernel context
  match started with
  | .SendExhausted entry _ => ok (entry, .None)
  | .SendKdfRequested pending =>
    let ready ← pending.resume (execute pending.request)
    ready.finish (sealCallback ready.material ready.sequence ready.context)

/-- Every send attempt terminates and preserves the lifetime relation for every seal callback result, including exhaustion and failure. -/
theorem sealNext_preserves_reachability {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (sendOrigin receiveOrigin : RatchetChain) (kernel : ConcreteRatchetKernel)
    (h : RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin kernel)
    (context : Context) (sealCallback : RatchetMaterial → Std.U64 → Context → core.option.Option Output) :
    ∃ next output, sealNext execute kernel context sealCallback = ok (next, output) ∧
      RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin next := by
  by_cases hmax : kernel.refined.control.send_sequence = core.num.U64.MAX
  · exact ⟨kernel, .None, by simp [sealNext, begin_send_exhausted_restores_entry kernel context hmax], h⟩
  · obtain ⟨send, receive, hkernel, horigin⟩ := h
    obtain ⟨pending, hbegin, hpending⟩ :=
      begin_send_refines (withInterpreter cr execute) receiveOrigin send receive kernel context hkernel hmax
    obtain ⟨ready, hresume, hready⟩ :=
      SendKdf.resume_refines (withInterpreter cr execute) receiveOrigin send receive kernel context pending hpending
        (execute pending.request) (interpreter_request_refines cr execute send.ck pending.request
          hpending.requestInput hpending.requestInfo)
    exact ⟨ready.advanced, sealCallback ready.material ready.sequence ready.context,
      by simp [sealNext, hbegin, hresume, SendSeal.finish_returns_interpreter_result],
      ⟨_, receive, hready.advanced, send_successor_reachable (withInterpreter cr execute) sendOrigin send horigin⟩⟩

end beaconcrypt_core.ratchet.concrete
