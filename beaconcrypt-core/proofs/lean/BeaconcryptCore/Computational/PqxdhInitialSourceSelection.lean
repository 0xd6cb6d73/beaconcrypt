import BeaconcryptCore.Computational.PqxdhInitialSourceExperiment

/-!
Adaptive record-position selection is bounded in the actual complete source execution. The finite allowance is derived from the original first builder and post program, including failed and repeated operations. This module supplies probability accounting only; the per-position cryptographic reductions must use these same source events.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceSelection
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialBeaconAmbient PqxdhInitialSourceExperiment
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
  (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (selected : RawCtxProtocolReveals.Owner S B)
  (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)

/-- Selecting an actually published fresh record costs a finite sum over the source-derived position allowance, retaining the same original decision and byte-level freshness. -/
theorem positions (stage qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (ancestors disclosed : List RatchetChain) :
    Pr[fun result => ∃ number : Std.U64,
      PqxdhInitialPublishedEvent.sourceEvent source (root source previousRoot response64 selected)
        selected number ancestors disclosed result |
      run source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
        selected shared privateState cache stage] ≤
      ∑ position ∈ Finset.range (7 + qPost * 67 + 1),
        Pr[fun result => ∃ number : Std.U64, number.val = position ∧
          PqxdhInitialPublishedEvent.sourceEvent source (root source previousRoot response64 selected)
            selected number ancestors disclosed result |
          run source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
            selected shared privateState cache stage] := by
  refine le_trans ?_ (probEvent_exists_finset_le_sum _ _ _)
  apply probEvent_mono
  exact fun result supported ⟨number, event⟩ =>
    ⟨number.val, Finset.mem_range.mpr (Nat.lt_succ_of_le
      (published_bound source writer selectedMessage previousRoot response64 other sender route decode index metadata ready
        post before selected number shared privateState cache stage qPost bounded result supported event.1.2)), number, rfl, event⟩

end BeaconcryptCore.Computational.PqxdhInitialSourceSelection

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSelection.positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSelection.positions
