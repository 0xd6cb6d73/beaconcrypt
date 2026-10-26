import BeaconcryptCore.Refinement.RatchetReceiveIdeal

/-! Concrete delivery and rejection properties obtained from the unchanged ideal ratchet. These statements execute extracted receive phases and retain exact plaintext and poststate observations. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- A valid next record delivers its original plaintext, advances once, and retains the skipped store. -/
theorem KernelRefines.receive_in_order
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (htarget : target.val = receive.n + 1) (ad : AD) (plaintext : PT) :
    ∃ result,
      receiveNext execute entry target context
        (receiveIdealOpenReply (withInterpreter cr execute) ad
          ((withInterpreter cr execute).enc ((withInterpreter cr execute).kdfMsg receive.ck) ad plaintext)) =
        ok (result, core.option.Option.Some plaintext) ∧
      KernelRefines (withInterpreter cr execute) origin send
        ⟨(withInterpreter cr execute).kdfChain receive.ck, receive.n + 1, receive.skipped⟩ result := by
  have hideal := Ratchet.recvStep_inOrder (withInterpreter cr execute)
    receive.ck receive.n receive.skipped h.receiveControl.recvWf ad plaintext
  obtain ⟨result, hrun, hresult, _⟩ := h.receive_ideal cr execute origin send receive
    entry context target (by omega) ad
    ((withInterpreter cr execute).enc ((withInterpreter cr execute).kdfMsg receive.ck) ad plaintext)
  exact ⟨result, by simpa only [htarget, Nat.add_sub_cancel, hideal, receiveIdealPlaintext] using hrun,
    by simpa only [htarget, Nat.add_sub_cancel, hideal] using hresult⟩

/-- A replay with no retained key returns no plaintext and restores the exact entry kernel, for every ciphertext. -/
theorem KernelRefines.receive_replay
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hpositive : 0 < target.val) (hpast : target.val ≤ receive.n)
    (hmissing : List.lookup (target.val - 1) receive.skipped = none)
    (ad : AD) (ciphertext : CT) :
    receiveNext execute entry target context
      (receiveIdealOpenReply (withInterpreter cr execute) ad ciphertext) =
      ok (entry, core.option.Option.None) := by
  have hideal := Ratchet.recvStep_replay_rejected (withInterpreter cr execute)
    receive ad ⟨target.val - 1, ciphertext⟩ (by simp only; omega) hmissing
  obtain ⟨result, hrun, _, herror⟩ := h.receive_ideal cr execute origin send receive
    entry context target hpositive ad ciphertext
  simpa only [hideal, receiveIdealPlaintext,
    herror .replay (congrArg Prod.fst hideal)] using hrun

/-- A retained out-of-order key delivers the sender's original plaintext and removes precisely that key. -/
theorem KernelRefines.receive_retained
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (origin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (h : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (hpositive : 0 < target.val) (material : ratchet.RatchetMaterial)
    (hretained : List.lookup (target.val - 1) receive.skipped = some material)
    (ad : AD) (plaintext : PT) :
    ∃ result,
      receiveNext execute entry target context
        (receiveIdealOpenReply (withInterpreter cr execute) ad
          ((withInterpreter cr execute).enc material ad plaintext)) =
        ok (result, core.option.Option.Some plaintext) ∧
      KernelRefines (withInterpreter cr execute) origin send
        { receive with skipped := receive.skipped.filter (fun p => !(p.1 == target.val - 1)) } result := by
  have hideal := Ratchet.recvStep_stored_ok (withInterpreter cr execute) receive ad
    ⟨target.val - 1, (withInterpreter cr execute).enc material ad plaintext⟩ material plaintext
    hretained ((withInterpreter cr execute).dec_enc material ad plaintext)
  obtain ⟨result, hrun, hresult, _⟩ := h.receive_ideal cr execute origin send receive
    entry context target hpositive ad ((withInterpreter cr execute).enc material ad plaintext)
  exact ⟨result, by simpa only [hideal, receiveIdealPlaintext] using hrun,
    by simpa only [hideal] using hresult⟩

end beaconcrypt_core.ratchet.concrete
