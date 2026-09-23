import BeaconcryptCore.Computational.PqxdhInitialSourceExperiment
import BeaconcryptCore.Computational.PqxdhInitialNativeRetained

/-!
The first evolving-chain experiment uses the actual fixed ratchet function. Its empty private table is analysis instrumentation: every supported final lookup is the same fixed function, and the complete original result and ambient state are retained when that instrumentation is removed. In particular the actual published-record freshness event is observed before this removal and agrees with the fixed-function event.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceReal
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

/-- The entire actual stage-zero cache, including entries reached by failed or repeated requests, has exactly the real fixed-HKDF lookup. -/
theorem final_lookup
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × PqxdhInitialOriginPostPath.State A N)
    (supported : result ∈ support (run source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected shared privateState cache 0)) :
    RawCtxSelectedParentTable.view (productionStream source.crypto) result.2.1.1.2.1 = productionStream source.crypto := by
  exact (PqxdhInitialNativeRetained.final_view source writer 0
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other)
    (PqxdhInitialNativeCarried.original source (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode (execution response64 index metadata ready post before))
    (initialState (root source previousRoot response64 selected) shared privateState cache) (Nat.zero_le _)
    result supported).trans rfl

noncomputable def decision (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) ×
      PqxdhInitialNativeRetained.RetainedState A N RootOracle.QueryCache) : Bool :=
  @decide (PqxdhInitialPublishedEvent.Gate selected number result.1 ∧ RawCtxLiveLineage.Fresh
    (RawCtxPublishedLineage.lineage (productionStream source.crypto)
      (RawCtxFreshChainCut.concreteChain (root source previousRoot response64 selected)) (number.val - 1) ++ ancestors)
    disclosed result.1.2.1.roles.2) (Classical.propDecidable _)

/-- Observing the actual stage-zero publication and freshness before removing private instrumentation equals observing the fixed source lineage afterward. -/
theorem decision_source (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × PqxdhInitialOriginPostPath.State A N)
    (supported : result ∈ support (run source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected shared privateState cache 0)) :
    PqxdhInitialPublishedEvent.sourceDecision source (root source previousRoot response64 selected)
      selected number ancestors disclosed result =
      decision source previousRoot response64 selected number ancestors disclosed
        (result.1, PqxdhInitialNativeRetained.project result.2) := by
  unfold PqxdhInitialPublishedEvent.sourceDecision PqxdhInitialPublishedEvent.sourceEvent decision
  rw [final_lookup source writer selectedMessage previousRoot response64 other sender route decode index metadata ready
      post before selected shared privateState cache result supported]

noncomputable def realRun :=
  (simulateQ (PqxdhInitialNativeRetained.retained source writer (productionStream source.crypto)
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other))
    (PqxdhInitialNativeCarried.original source (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode (execution response64 index metadata ready post before))).run
      (shared, (privateState, cache))

/-- The same complete source observation is executable against the fixed function without any private analysis cache. -/
theorem game_source (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    game source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected number ancestors disclosed shared privateState cache 0 =
    decision source previousRoot response64 selected number ancestors disclosed <$>
      realRun source writer selectedMessage previousRoot response64 other sender route decode index metadata ready
        post before shared privateState cache := by
  have erased := PqxdhInitialNativeRetained.retained_run source writer 0
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other)
    (PqxdhInitialNativeCarried.original source (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode (execution response64 index metadata ready post before))
    (initialState (root source previousRoot response64 selected) shared privateState cache) (Nat.zero_le _)
  change (fun result => (result.1, PqxdhInitialNativeRetained.project result.2)) <$>
    run source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected shared privateState cache 0 =
    realRun source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      shared privateState cache at erased
  rw [← erased, game, Functor.map_map, ← bind_pure_comp, ← bind_pure_comp]
  exact bind_congr_of_forall_mem_support _ (fun result supported =>
    congrArg pure (decision_source source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected shared privateState cache number ancestors disclosed result supported))

end BeaconcryptCore.Computational.PqxdhInitialSourceReal

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceReal.final_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceReal.final_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceReal.decision_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceReal.decision_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceReal.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceReal.game_source
