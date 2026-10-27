import BeaconcryptCore.Computational.PqxdhInitialPublishedEvent
import BeaconcryptCore.Computational.PqxdhInitialCounterPublication
import BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent

/-!
Every chain stage runs the same original supplied-initializer builder and full adaptive post schedule. The selected directional root comes from the actual initialized kernels. The selective cache, chronological log and origin trace start empty; the complete primitive, identity and initializer-cache states are retained. The final bit tests one fixed publication and its actual original-lineage freshness.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceExperiment
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialBeaconAmbient PqxdhInitialSourcePublication
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem server_exists (source : FixedHkdfSha512NoSaltSource)
    (response : PqxdhInitialRootLabelService.Response) :
    ∃ server, PqxdhInitialReplyErasure.kernelOf false response = ok server := by
  obtain ⟨_, server, _, created, _⟩ := PqxdhInitialSuppliedPositions.pair_positioned source.crypto response
  exact ⟨server, created⟩

noncomputable def server (source : FixedHkdfSha512NoSaltSource)
    (response : PqxdhInitialRootLabelService.Response) : ConcreteRatchetKernel :=
  Classical.choose (server_exists source response)

/-- Every typed initial64 response creates the actual Server kernel; successful initialization is derived rather than assumed. -/
theorem server_created (source : FixedHkdfSha512NoSaltSource)
    (response : PqxdhInitialRootLabelService.Response) :
    PqxdhInitialReplyErasure.kernelOf false response = ok (server source response) :=
  Classical.choose_spec (server_exists source response)

noncomputable def root (source : FixedHkdfSha512NoSaltSource) (previousRoot : RootOutput)
    (response : PqxdhInitialRootLabelService.Response) (selected : RawCtxProtocolReveals.Owner S B) : RootOutput :=
  PqxdhInitialOriginPostPath.rootFor
    (RawCtxSelectedQueryTrace.rootVector (server source response).refined.send_chain) previousRoot response selected

def initialState (root : RootOutput) (shared : RawCtxSharedPrimitive.SharedState A)
    (privateState : N) (cache : RootOracle.QueryCache) : PqxdhInitialOriginPostPath.State A N :=
  (((shared, (∅, ⟨root, 0⟩)), []), (privateState, cache))

/-- The source starts with an empty private cache and log at depth zero, so every later predecessor scan has its actual initial validity and absence conditions. -/
theorem initial_valid (root : RootOutput) (shared : RawCtxSharedPrimitive.SharedState A)
    (privateState : N) (cache : RootOracle.QueryCache) (depth : Nat) :
    PqxdhInitialNativeRisk.Valid depth 0 (initialState root shared privateState cache) ∧
      PqxdhInitialNativeRisk.Clean (initialState root shared privateState cache) := by
  refine ⟨⟨RawCtxSelectiveFamilyLog.empty_covered shared ⟨root, 0⟩ [], Nat.zero_le depth, Nat.le_refl 0⟩, rfl⟩

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
  (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
  (ancestors disclosed : List RatchetChain)
  (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)

noncomputable def execution : PqxdhInitialNativeCarried.Execution extra M P I D K Bool Bool S B :=
  ⟨ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64,
    index, metadata, ready, post, before, empty, true⟩

noncomputable def run (stage : Nat) :=
  (PqxdhInitialSourcePublication.sequence source writer stage selectedMessage previousRoot response64 other
    sender route decode index metadata ready post before).run
      (initialState (root source previousRoot response64 selected) shared privateState cache)

noncomputable def game (stage : Nat) : ProbComp Bool :=
  PqxdhInitialPublishedEvent.sourceDecision source (root source previousRoot response64 selected) selected number ancestors disclosed <$>
    run source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected shared privateState cache stage

/-- Every experiment stage is exactly the full source execution consumed by the adjacent-hybrid sampler, with all original final fields retained. -/
theorem run_source (stage : Nat) :
    run source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected shared privateState cache stage =
    PqxdhInitialNativeAdjacent.run source writer (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode (execution response64 index metadata ready post before)
      (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) stage
      (initialState (root source previousRoot response64 selected) shared privateState cache) := rfl

/-- Every accepted target record in this experiment has its whole selected-origin directional path already cached by actual source sends. -/
theorem published_cached (stage : Nat)
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × PqxdhInitialOriginPostPath.State A N)
    (supported : result ∈ support (run source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected shared privateState cache stage))
    (published : ((selected, number), true) ∈ result.1.2.2.published) :
    RawCtxSourcePublishedPath.Cached (root source previousRoot response64 selected) number result.2.1.1.2.1 :=
  PqxdhInitialSourcePublication.publication_cached source writer stage selectedMessage previousRoot response64 other
    (server source response64) (server_created source response64) selected sender route decode index metadata ready post
    before (initialState (root source previousRoot response64 selected) shared privateState cache) result supported number published

/-- Adaptive publication positions are bounded by actual source callbacks from the empty log, with no assumed path length or collision-free chain. -/
theorem published_bound (stage qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × PqxdhInitialOriginPostPath.State A N)
    (supported : result ∈ support (run source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected shared privateState cache stage))
    (published : ((selected, number), true) ∈ result.1.2.2.published) :
    number.val ≤ 7 + qPost * 67 := by
  simpa only [initialState, List.length_nil, Nat.zero_add] using
    PqxdhInitialCounterPublication.publication_bound source writer stage selectedMessage previousRoot response64 other
      (server source response64) (server_created source response64) selected sender route decode index metadata ready post
      qPost bounded before (initialState (root source previousRoot response64 selected) shared privateState cache)
      result supported number published

/-- Cache normalization for the same actual source event has coefficient one and the concrete chronological sum, with all initial validity premises discharged. -/
theorem normalization (depth qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost) :
    ENNReal.ofReal (discreteDistance
      (game source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
        selected number ancestors disclosed shared privateState cache (depth + 2))
      (PqxdhInitialNativeAdjacent.normalized source writer (PqxdhInitialSelectedOrigin.mark source selectedMessage)
        sender route decode (execution response64 index metadata ready post before)
        (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) depth
        (initialState (root source previousRoot response64 selected) shared privateState cache) >>=
          fun result => pure (PqxdhInitialPublishedEvent.sourceDecision source (root source previousRoot response64 selected)
            selected number ancestors disclosed result))) ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  simpa only [game, run_source, execution, bind_pure_comp, Nat.zero_add] using
    PqxdhInitialNativeAdjacent.normalization_after source writer (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode (execution response64 index metadata ready post before)
      (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) depth 0 qPost bounded
      (initialState (root source previousRoot response64 selected) shared privateState cache)
      (initial_valid _ shared privateState cache depth).1 (initial_valid _ shared privateState cache depth).2
      (fun result => pure (PqxdhInitialPublishedEvent.sourceDecision source (root source previousRoot response64 selected)
        selected number ancestors disclosed result))

end BeaconcryptCore.Computational.PqxdhInitialSourceExperiment

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.server_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.server_created
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.initial_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.initial_valid
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.run_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.published_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.published_cached
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.published_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.published_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceExperiment.normalization
