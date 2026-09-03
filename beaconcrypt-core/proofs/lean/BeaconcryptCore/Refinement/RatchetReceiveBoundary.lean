import BeaconcryptCore.Refinement.RatchetReceiveCompatibility

/-! The historical fifty-derivation F* boundary publishes forty-nine skipped records and keeps the authentication target out of the cache. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context Plaintext : Type}

/-- Adapt a material/sequence/context callback to the actual extracted open-request getters. -/
def receiveMaterialOpenReply
    (callback : ratchet.RatchetMaterial → Std.U64 → Context → core.option.Option Plaintext)
    (opened : ReceiveOpen Context) : core.option.Option Plaintext :=
  match opened.material, opened.sequence with
  | ok (core.option.Option.Some material), ok sequence => callback material sequence opened.context
  | _, _ => core.option.Option.None

/-- With an empty entry cache, exactly fifty admitted derivations publish forty-nine skipped records and never publish the target. -/
theorem KernelRefines.fresh_maximum_gap_success_publishes_exactly_49
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hempty : entry.refined.control.receive_cache.len.val = 0)
    (hplan : plan_receive_until entry.refined.control target =
      ok { sequence := core.option.Option.Some target, derivations := 50#u64 })
    (callback : ratchet.RatchetMaterial → Std.U64 → Context → core.option.Option Plaintext)
    (plaintext : Plaintext)
    (hcallback : callback (Ratchet.msgKeyAt (withInterpreter cr execute) receive.ck 49) target context =
      core.option.Option.Some plaintext) :
    ∃ result,
      receiveNext execute entry target context (receiveMaterialOpenReply callback) = ok (result, core.option.Option.Some plaintext) ∧
      KernelRefines (withInterpreter cr execute) origin send (futureReceiveState (withInterpreter cr execute) receive target) result ∧
      result.refined.control.receive_sequence = target ∧ result.refined.control.receive_cache.len.val = 49 ∧
      lookup_receive_key result.refined.control target = ok core.option.Option.None := by
  obtain ⟨_, _, hmax⟩ := plan_receive_until_bound entry.refined.control target
    { sequence := core.option.Option.Some target, derivations := 50#u64 } h.receiveControl.wf hplan rfl
  have hsteps : target.val = receive.n + 50 := by have hsequence := h.receiveControl.seq; scalar_tac
  obtain ⟨pending, opened, hbegin, htrace, hopen⟩ := h.begin_receive_future_trace cr execute origin send receive
    entry context target (by omega) (by omega)
  have hmaterial := hopen.material_exact (withInterpreter cr execute) origin send receive entry context target opened
  obtain ⟨transaction, hentry, hcontext, hphase, htransaction⟩ := hopen
  obtain ⟨published, hpublish, hkernel⟩ := htransaction.publication (withInterpreter cr execute) origin send receive
    entry target transaction
  obtain ⟨out, hout, hcontrol, _, _, _⟩ := ratchet.refined.publish_future_receive_exact entry.refined transaction
    (by simpa only [htransaction.firstSlot, htransaction.skipped] using htransaction.capacity)
  have heq : out = published := RustM.ok.inj (hout.symm.trans hpublish)
  subst out
  have hreply : receiveMaterialOpenReply callback opened = core.option.Option.Some plaintext := by
    simp only [receiveMaterialOpenReply, hmaterial, ReceiveOpen.sequence, hphase,
      htransaction.targetSequence, hcontext, show target.val - receive.n - 1 = 49 by omega, hcallback]
  have hfinish : opened.finish (receiveMaterialOpenReply callback opened) =
      ok ({ refined := published }, core.option.Option.Some plaintext) := by
    simp only [hreply, ReceiveOpen.finish, hphase, hentry, hpublish, bind_tc_ok]
  exact ⟨{ refined := published },
    (show ReceiveRun execute (receiveMaterialOpenReply callback) entry target context
      { refined := published } (core.option.Option.Some plaintext) from
      ⟨_, hbegin, htrace.complete (ReceiveExecution.opened opened _ _ hfinish)⟩).driver_eq,
    hkernel, by simpa only [hcontrol] using htransaction.committedReceive,
    by simp [hcontrol, htransaction.committedLength, hempty, hsteps],
    by simpa only [hcontrol] using htransaction.target_absent (withInterpreter cr execute) origin send receive entry target transaction⟩

end beaconcrypt_core.ratchet.concrete
