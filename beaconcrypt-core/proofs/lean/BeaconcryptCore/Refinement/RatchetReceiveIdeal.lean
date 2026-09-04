import BeaconcryptCore.Refinement.RatchetReceiveAdmission
import BeaconcryptCore.Refinement.RatchetCachedPublication
import BeaconcryptCore.Refinement.RatchetFutureTrace
import BeaconcryptCore.Refinement.RatchetReceiveDriver
import BeaconcryptCore.PanicFreedom.Effects

/-! Complete correspondence between extracted receive execution and the unchanged ideal ratchet model. The authentication callback decrypts using the material returned by the actual extracted open request. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- The callback obtains the actual extracted request material before running ideal decryption. -/
def receiveIdealOpenReply
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (ad : AD) (ciphertext : CT) (opened : ReceiveOpen Context) : core.option.Option PT :=
  match opened.material with
  | ok (core.option.Option.Some material) => idealOpenReply cr material ad ciphertext
  | _ => core.option.Option.None

/-- The effect API represents every ideal rejection by an absent plaintext. -/
def receiveIdealPlaintext : Except Ratchet.RecvError PT → core.option.Option PT
  | .ok plaintext => core.option.Option.Some plaintext
  | .error _ => core.option.Option.None

private theorem begin_receive_cached_entry (entry : ConcreteRatchetKernel) (target : Std.U64)
    (context : Context) (opened : ReceiveOpen Context)
    (hpast : target.val ≤ entry.refined.control.receive_sequence.val)
    (hbegin : begin_receive entry target context = ok (ReceiveEffect.ReceiveOpenRequested opened)) :
    opened.entry = entry := by
  obtain ⟨prepared, hprepared⟩ := ratchet.refined.prepare_cached_receive_total entry.refined target
  cases prepared with
  | none =>
    simp only [begin_receive, plan_receive_until_replay entry.refined.control target hpast,
      bind_tc_ok, if_true, hprepared, receive_rejected, RustM.ok.injEq, reduceCtorEq] at hbegin
  | some prepared =>
    simp only [begin_receive, plan_receive_until_replay entry.refined.control target hpast,
      bind_tc_ok, if_true, hprepared, RustM.ok.injEq, ReceiveEffect.ReceiveOpenRequested.injEq] at hbegin
    exact (congrArg ReceiveOpen.entry hbegin).symm

/-- Complete extracted execution returns exactly the ideal plaintext outcome and refines the ideal poststate; every ideal rejection returns the exact entry kernel. -/
theorem KernelRefines.receive_ideal_run
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hpositive : 0 < target.val) (ad : AD) (ciphertext : CT) :
    ∃ result,
      ReceiveRun execute (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext)
        entry target context result
        (receiveIdealPlaintext (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).1) ∧
      KernelRefines (withInterpreter cr execute) origin send
        (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).2 result ∧
      (∀ error, (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).1 = .error error → result = entry) := by
  have hlength : entry.refined.control.receive_cache.len.val = receive.skipped.length := by
    simpa only [cacheSeqs_length, List.length_map] using h.receiveControl.cache.length_eq
  cases hlookup : List.lookup (target.val - 1) receive.skipped with
  | some material =>
    obtain ⟨opened, hbegin, hopen⟩ := begin_receive_cached_refines (withInterpreter cr execute) origin send receive
      entry context target (target.val - 1) material h (by omega) hlookup
    have hmaterial := hopen.material_exact (withInterpreter cr execute) origin send receive (target.val - 1) material opened
    have hentry : opened.entry = entry := begin_receive_cached_entry entry target context opened
      (by have hlt := h.receiveControl.keys_lt _ (mem_of_lookup_eq_some hlookup); rw [h.receiveControl.seq]; omega) hbegin
    cases hdecrypt : (withInterpreter cr execute).dec material ad ciphertext with
    | none =>
      rw [Ratchet.recvStep_stored_authFail (withInterpreter cr execute) receive ad
        ⟨target.val - 1, ciphertext⟩ material hlookup hdecrypt]
      exact ⟨entry, ⟨_, hbegin, ReceiveExecution.opened opened _ _
        (by simpa only [receiveIdealOpenReply, hmaterial, idealOpenReply, hdecrypt, receiveIdealPlaintext, hentry]
          using (ReceiveOpen.finish_failure_restores_entry (Plaintext := PT) opened))⟩, h, fun _ _ => rfl⟩
    | some plaintext =>
      obtain ⟨published, hfinish, hideal, hkernel⟩ := hopen.finish_success_refines
        (withInterpreter cr execute) origin send receive (target.val - 1) material opened ad ciphertext plaintext hdecrypt
      rw [hideal]
      exact ⟨{ refined := published }, ⟨_, hbegin, ReceiveExecution.opened opened _ _
        (by simpa only [receiveIdealOpenReply, hmaterial, idealOpenReply, hdecrypt, receiveIdealPlaintext] using hfinish)⟩,
        hkernel, by simp⟩
  | none =>
    by_cases hpast : target.val ≤ receive.n
    · have hideal := Ratchet.recvStep_replay_rejected (withInterpreter cr execute) receive ad
        ⟨target.val - 1, ciphertext⟩ (by change target.val - 1 < receive.n; omega) hlookup
      rw [hideal]
      exact ⟨entry, ⟨_, h.begin_receive_replay (withInterpreter cr execute) origin send receive entry target context
        hpast hpositive hlookup, ReceiveExecution.rejected entry context⟩, h, fun _ _ => rfl⟩
    · by_cases hcapacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50
      · obtain ⟨pending, opened, hbegin, htrace, hopen⟩ := h.begin_receive_future_trace cr execute origin send receive
          entry context target (by omega) hcapacity
        have hmaterial := hopen.material_exact (withInterpreter cr execute) origin send receive entry context target opened
        cases hdecrypt : (withInterpreter cr execute).dec
            (Ratchet.msgKeyAt (withInterpreter cr execute) receive.ck (target.val - receive.n - 1)) ad ciphertext with
        | none =>
          have hideal := Ratchet.recvStep_chain_authFail (withInterpreter cr execute) receive ad
            ⟨target.val - 1, ciphertext⟩ hlookup (by change receive.n ≤ target.val - 1; omega)
            (by simp only [Ratchet.maxSkip]; omega) (by simpa only [Nat.sub_sub, Nat.add_comm] using hdecrypt)
          obtain ⟨transaction, hentry, _, _, _⟩ := hopen
          rw [hideal]
          refine ⟨entry, ⟨_, hbegin, htrace.complete (ReceiveExecution.opened opened entry _ ?_)⟩,
            h, fun _ _ => rfl⟩
          simpa only [receiveIdealOpenReply, hmaterial, idealOpenReply, hdecrypt, receiveIdealPlaintext, hentry]
            using (ReceiveOpen.finish_failure_restores_entry (Plaintext := PT) opened)
        | some plaintext =>
          obtain ⟨published, hfinish, hideal, hkernel⟩ := hopen.finish_success_refines
            (withInterpreter cr execute) origin send receive entry context target opened ad ciphertext plaintext hdecrypt
          rw [hideal]
          refine ⟨{ refined := published }, ⟨_, hbegin, ?_⟩, hkernel, by simp⟩
          apply htrace.complete
          exact ReceiveExecution.opened opened _ _ (by simpa only [receiveIdealOpenReply, hmaterial, idealOpenReply, hdecrypt, receiveIdealPlaintext] using hfinish)
      · have hideal := Ratchet.recvStep_reject_tooManySkipped (withInterpreter cr execute) receive ad
          ⟨target.val - 1, ciphertext⟩ hlookup (by change receive.n ≤ target.val - 1; omega)
          (by simp only [Ratchet.maxSkip]; omega)
        rw [hideal]
        exact ⟨entry, ⟨_, h.begin_receive_capacity_rejected (withInterpreter cr execute) origin send receive
          entry target context (by omega) (by omega), ReceiveExecution.rejected entry context⟩, h, fun _ _ => rfl⟩

/-- The complete synchronous composition terminates and matches the ideal receive outcome and poststate. -/
theorem KernelRefines.receive_ideal
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hpositive : 0 < target.val) (ad : AD) (ciphertext : CT) :
    ∃ result,
      receiveNext execute entry target context (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext) =
        ok (result, receiveIdealPlaintext (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).1) ∧
      KernelRefines (withInterpreter cr execute) origin send
        (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).2 result ∧
      (∀ error, (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).1 = .error error → result = entry) := by
  obtain ⟨result, hrun, hkernel, herror⟩ := h.receive_ideal_run cr execute origin send receive entry context target hpositive ad ciphertext
  exact ⟨result, hrun.driver_eq, hkernel, herror⟩

end beaconcrypt_core.ratchet.concrete
