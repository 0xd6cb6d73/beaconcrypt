import BeaconcryptCore.Refinement.RatchetRoleReachability
import BeaconcryptCore.Refinement.RatchetCachedPublication

/-! Cached receive publication preserves lifetime reachability for every optional callback result. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

/-- Cached opening preserves the role invariant for any returned plaintext or failure, without a decryption premise. -/
theorem CachedOpenRefines.finish_preserves_reachability {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain)
    (send : Ratchet.SendState RatchetChain) (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (index : Nat) (material : RatchetMaterial) (pending : ReceiveOpen Context)
    (h : CachedOpenRefines cr receiveOrigin send receive index material pending)
    (hsend : send.ck = Ratchet.chainAt cr sendOrigin send.n)
    (opened : core.option.Option Output) :
    ∃ next, pending.finish opened = ok (next, opened) ∧
      RoleReachable cr sendOrigin receiveOrigin next := by
  obtain ⟨prepared, cached, hphase, _, hlast, hfinish, hkernel, _, hindex,
    hslot, _, hcontrolSequence, hsequence, _⟩ := h
  cases opened with
  | none => exact ⟨pending.entry, rfl, send, receive, hkernel, hsend⟩
  | some plaintext =>
    obtain ⟨published, hpublish, hpublication⟩ :=
      KernelRefines.cached_publication cr receiveOrigin send receive pending.entry hkernel prepared index
        hindex hslot (hcontrolSequence.symm.trans hsequence) hlast hfinish
    exact ⟨{ refined := published }, by simp [ReceiveOpen.finish, hphase, hpublish],
      send, _, hpublication, hsend⟩

end beaconcrypt_core.ratchet.concrete
