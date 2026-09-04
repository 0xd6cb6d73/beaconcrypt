import BeaconcryptCore.Refinement.RatchetReceiveIdeal

/-! Consumption, replay protection, and retry laws for the actual receive composition. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core.ratchet.control

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- Every successful ideal receive consumes its target and advances beyond that target's index. -/
private theorem ideal_receive_success_consumes
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (hwf : Ratchet.RecvWf receive) (ad : AD) (message : Ratchet.Msg CT) (plaintext : PT)
    (hsuccess : (Ratchet.recvStep cr receive ad message).1 = .ok plaintext) :
    message.idx < (Ratchet.recvStep cr receive ad message).2.n ∧
      List.lookup message.idx (Ratchet.recvStep cr receive ad message).2.skipped = none := by
  rcases Ratchet.recvStep_cases cr receive ad message with
    ⟨pt, material, hlookup, hdecrypt, hstep⟩ | ⟨pt, hlookup, hfuture, hstep⟩ | ⟨error, hstep⟩
  · rw [hstep]
    refine ⟨hwf.keys_lt _ (mem_of_lookup_eq_some hlookup), ?_⟩
    simp [List.lookup_eq_none_iff, List.mem_filter, ne_comm]
  · rw [hstep]
    refine ⟨by simp, Ratchet.lookup_eq_none_of_keys_lt (base := message.idx) ?_ (Nat.le_refl _)⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Nat.lt_of_lt_of_le (hwf.keys_lt p hp) hfuture
    · simpa only [Nat.add_sub_of_le hfuture] using (Ratchet.mem_skipKeys_index cr receive.ck receive.n (message.idx - receive.n) hp).2
  · simp only [hstep, reduceCtorEq] at hsuccess

/-- A successful observed extracted execution determines the ideal plaintext and preserves the full poststate relation. -/
theorem KernelRefines.receive_success_refines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry result : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hpositive : 0 < target.val) (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hactual : receiveNext execute entry target context
      (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext) = ok (result, core.option.Option.Some plaintext)) :
    (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).1 = .ok plaintext ∧
      KernelRefines (withInterpreter cr execute) origin send
        (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).2 result := by
  obtain ⟨canonical, hcanonical, hkernel, _⟩ := h.receive_ideal cr execute origin send receive entry context target hpositive ad ciphertext
  have heq := RustM.ok.inj (hcanonical.symm.trans hactual)
  cases houtcome : (Ratchet.recvStep (withInterpreter cr execute) receive ad ⟨target.val - 1, ciphertext⟩).1 with
  | error error =>
    simp only [houtcome, receiveIdealPlaintext, Prod.mk.injEq, core.option.Option.None, core.option.Option.Some, reduceCtorEq, and_false] at heq
  | ok pt =>
    simp only [houtcome, receiveIdealPlaintext, Prod.mk.injEq, core.option.Option.Some, Option.some.injEq] at heq
    exact ⟨congrArg Except.ok heq.2, heq.1 ▸ hkernel⟩

/-- After a successful receive, replaying the target is rejected before any authentication callback and preserves the exact resulting kernel. -/
theorem KernelRefines.receive_success_replay {RetryContext RetryPlaintext : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry result : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hpositive : 0 < target.val) (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hactual : receiveNext execute entry target context
      (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext) = ok (result, core.option.Option.Some plaintext))
    (retryContext : RetryContext) (reply : ReceiveOpen RetryContext → core.option.Option RetryPlaintext) :
    receiveNext execute result target retryContext reply = ok (result, core.option.Option.None) := by
  obtain ⟨hsuccess, hpost⟩ := h.receive_success_refines cr execute origin send receive entry result context target
    hpositive ad ciphertext plaintext hactual
  obtain ⟨hindex, hlookup⟩ := ideal_receive_success_consumes (withInterpreter cr execute) receive
    h.receiveControl.recvWf ad ⟨target.val - 1, ciphertext⟩ plaintext hsuccess
  have hbegin := hpost.begin_receive_replay (withInterpreter cr execute) origin send _ result target retryContext
    (by dsimp only at hindex; omega) hpositive hlookup
  exact (show ReceiveRun execute reply result target retryContext result core.option.Option.None from
    ⟨_, hbegin, ReceiveExecution.rejected result retryContext⟩).driver_eq

end beaconcrypt_core.ratchet.concrete
