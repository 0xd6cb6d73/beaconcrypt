import BeaconcryptCore.Refinement.RatchetMaterialRestore
import BeaconcryptCore.Refinement.RatchetRoleReachability

/-! Canonical initialization of the actual production kernel at fresh and persisted counters. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- The direct constructor and finishing an empty restoration construct the same production kernel. -/
theorem from_counters_eq_empty_restore
    (sendSequence receiveSequence : Std.U64) (sendChain receiveChain : ratchet.RatchetChain) :
    ConcreteRatchetKernel.from_counters sendSequence receiveSequence sendChain receiveChain =
      (do let restore ← start_concrete_restore sendSequence receiveSequence sendChain receiveChain
          finish_concrete_restore restore) := by rfl

/-- The arbitrary-counter production constructor establishes reachability under exactly the canonical persisted-chain premises. -/
theorem from_counters_reachable {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : ratchet.RatchetChain) (sendSequence receiveSequence : Std.U64)
    (sendChain receiveChain : ratchet.RatchetChain)
    (hsend : sendChain = Ratchet.chainAt cr sendOrigin sendSequence.val)
    (hreceive : receiveChain = Ratchet.chainAt cr receiveOrigin receiveSequence.val) :
    ∃ kernel, ConcreteRatchetKernel.from_counters sendSequence receiveSequence sendChain receiveChain = ok kernel ∧
      KernelRefines cr receiveOrigin
        { ck := sendChain, n := sendSequence.val }
        { ck := receiveChain, n := receiveSequence.val, skipped := [] } kernel ∧
      RoleReachable cr sendOrigin receiveOrigin kernel := by
  obtain ⟨restore, hrestore, hrefines⟩ := start_concrete_restore_refines cr sendOrigin receiveOrigin
    sendSequence receiveSequence sendChain receiveChain hsend hreceive
  have hkernel : KernelRefines cr receiveOrigin
      { ck := sendChain, n := sendSequence.val }
      { ck := receiveChain, n := receiveSequence.val, skipped := [] } (restoreKernel restore) := by
    simpa only [hsend, hreceive] using hrefines.kernel
  refine ⟨restoreKernel restore, ?_, hkernel, _, _, hkernel, hsend⟩
  rw [from_counters_eq_empty_restore, hrestore, bind_tc_ok]
  rfl

/-- Fresh initialization is reachable under any fixed crypto model from its exact supplied directional chains. -/
theorem new_reachable {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (sendChain receiveChain : ratchet.RatchetChain) :
    ∃ kernel, ConcreteRatchetKernel.new sendChain receiveChain = ok kernel ∧
      KernelRefines cr receiveChain { ck := sendChain, n := 0 }
        { ck := receiveChain, n := 0, skipped := [] } kernel ∧
      RoleReachable cr sendChain receiveChain kernel := by
  exact from_counters_reachable cr sendChain receiveChain 0#u64 0#u64 sendChain receiveChain
    (by simp [Ratchet.chainAt]) (by simp [Ratchet.chainAt])

end beaconcrypt_core.ratchet.concrete
