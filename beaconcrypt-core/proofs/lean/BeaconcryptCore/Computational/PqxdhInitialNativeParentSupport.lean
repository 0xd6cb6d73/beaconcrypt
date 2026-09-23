import BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom
import BeaconcryptCore.Computational.PqxdhInitialSourceExperiment

/-!
Actual supported cut continuations retain membership in the original complete source execution. Both adjacent stages use their proved common prefix. Consequently the source publication theorem supplies each endpoint's cached-lineage witness; no final-state path hypothesis is introduced by the local cryptographic comparison.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialNativeLog PqxdhInitialNativeCarried
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)
  (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))

/-- Every actual supported cut, original query reply and complete continuation outcome occurs in the full original source execution. -/
theorem continuation_supported (depth stage : Nat) (initial state : State A N C)
    (context : Context extra M P I D K Result Origin S B)
    (cut : RawCtxForwardScan.Cut.pending context state ∈ support
      (carried source writer mark sender route decode execution depth stage external initial))
    (reply : (Spec extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialOriginContext.frame mark sender route decode context).1 × State A N C)
    (queried : reply ∈ support ((handler source writer stage external
      (PqxdhInitialOriginContext.frame mark sender route decode context).1).run state))
    (result : Final M P I D K Result Origin S B × State A N C)
    (continued : result ∈ support ((simulateQ (handler source writer stage external)
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2 reply.1)).run reply.2)) :
    result ∈ support (PqxdhInitialNativeAdjacent.run source writer mark sender route decode execution external stage initial) := by
  rw [PqxdhInitialNativeAdjacent.run, ← carried_finish source writer mark sender route decode execution depth stage external initial,
    mem_support_bind_iff]
  refine ⟨.pending context state, cut, ?_⟩
  change result ∈ support ((handler source writer stage external
    (PqxdhInitialOriginContext.frame mark sender route decode context).1).run state >>= fun reply =>
      (simulateQ (handler source writer stage external)
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2 reply.1)).run reply.2)
  rw [mem_support_bind_iff]
  exact ⟨reply, queried, continued⟩

/-- Every full76 parent response remains an actual possible original query outcome at a supported missing cut. -/
theorem parent_supported (depth stage : Nat) (before : depth < stage) (initial state : State A N C)
    (covered : Covered initial) (context : Context extra M P I D K Result Origin S B)
    (cut : RawCtxForwardScan.Cut.pending context state ∈ support
      (carried source writer mark sender route decode execution depth stage external initial))
    (missing : state.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) = none)
    (parent : FullOutput)
    (result : Final M P I D K Result Origin S B × State A N C)
    (continued : result ∈ support ((simulateQ (handler source writer stage external)
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run
          (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) parent state))) :
    result ∈ support (PqxdhInitialNativeAdjacent.run source writer mark sender route decode execution external stage initial) := by
  apply continuation_supported source writer mark sender route decode execution external depth stage initial state context cut
    (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent,
      PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) parent state) _ result continued
  rw [carried_miss source writer mark sender route decode execution depth stage stage before external initial state covered context cut missing,
    support_map]
  exact ⟨parent, by simp, rfl⟩

/-- The actual common prefix also supplies every later-stage continuation outcome, using its proved complete-state equality before the selected parent. -/
theorem parent_later_supported (depth : Nat) (initial state : State A N C)
    (valid : PqxdhInitialNativePrefix.Depth depth initial) (covered : Covered initial)
    (context : Context extra M P I D K Result Origin S B)
    (cut : RawCtxForwardScan.Cut.pending context state ∈ support
      (carried source writer mark sender route decode execution depth (depth + 1) external initial))
    (missing : state.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) = none)
    (parent : FullOutput)
    (result : Final M P I D K Result Origin S B × State A N C)
    (continued : result ∈ support ((simulateQ (handler source writer (depth + 2) external)
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run
          (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) parent state))) :
    result ∈ support (PqxdhInitialNativeAdjacent.run source writer mark sender route decode execution external (depth + 2) initial) := by
  apply parent_supported source writer mark sender route decode execution external depth (depth + 2) (by omega)
    initial state covered context _ missing parent result continued
  rw [← carried_same source writer mark sender route decode execution depth external initial valid]
  exact cut

end BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport.continuation_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport.continuation_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport.parent_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport.parent_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport.parent_later_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport.parent_later_supported
