import BeaconcryptCore.Computational.PqxdhLaterChallengeInsideRetained

/-! A missing source cursor bounds the counter of every owner on the same already-executed directional path, with no chain-input injectivity premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache
open PqxdhSecretInputKdf RawCtxCursorLineage RawCtxSelectiveChainGame
variable {M P I D K A N : Type} {S B : Nat}

/-- A kernel on the actual cached path cannot have advanced beyond a still-missing cursor input in that same table. -/
theorem counter_le (root : RootOutput) (store : Store) (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain)
    (lineage : Lineage root store) (path : RawCtxSourceSendPath.Path root ⟨kernel⟩ store.1)
    (missing : store.1 (cursorAddress store.2) = none) : kernel.control.send_sequence.val ≤ store.2.depth := by
  by_contra later
  exact PqxdhLaterCommonRisk.cached_beyond_cursor root kernel.control.send_sequence store lineage
    (let ⟨earlier, walked⟩ := path; ⟨earlier, _, walked⟩) (Nat.lt_of_not_ge later) missing

/-- A currently marked owner in the actual source invariant has not passed a missing cursor in that same complete native state. -/
theorem marked_counter (root : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (front : PqxdhInitialPostContext.NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Bool S B)
    (state : PqxdhInitialOriginPostPath.State A N)
    (active : PqxdhInitialOriginPostPath.Active root owner (front, trace) state)
    (lineage : Lineage root state.1.1.2) (missing : state.1.1.2.1 (cursorAddress state.1.1.2.2) = none)
    (installed : trace.installed owner = some true)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain)
    (present : RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 = some kernel) :
    kernel.control.send_sequence.val ≤ state.1.1.2.2.depth :=
  counter_le root state.1.1.2 kernel lineage (active installed kernel present) missing

end BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache.counter_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache.counter_le

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache.marked_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache.marked_counter
