import BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom
import BeaconcryptCore.Computational.PqxdhInitialSourceExperiment

/-! The first randomized source stage preserves its exact final publication and freshness through the deferred full76 draw. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceRandom
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


/-- The empty source private table with its early initial-chain response is exactly the private-only patch of the real production function. -/
theorem initial_view (root : RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput) :
    RawCtxSelectedParentTable.view (productionStream source.crypto)
      (QueryCache.cacheQuery (spec := JointKdfRO) (fun _ => none) (RawCtxFirstParentRisk.inputAddress root) output) =
    RawCtxSelectedParentPrivatePatch.privatePatch (productionStream source.crypto) root output := by
  have address : RawCtxSelectedParentPrivatePatch.targetAddress root = RawCtxFirstParentRisk.inputAddress root :=
    PqxdhInitialNativeLineageCheck.request_concrete root
  funext request
  by_cases same : request = RawCtxSelectedParentPrivatePatch.targetAddress root
  · subst request
    have hit : QueryCache.cacheQuery (spec := JointKdfRO) (fun _ => none) (RawCtxFirstParentRisk.inputAddress root) output
        (RawCtxSelectedParentPrivatePatch.targetAddress root) = some output := by
      rw [address]
      exact QueryCache.cacheQuery_self _ _ _
    simp only [RawCtxSelectedParentTable.view, hit, Option.getD_some, RawCtxSelectedParentPrivatePatch.privatePatch, if_true]
  · simp only [RawCtxSelectedParentTable.view, RawCtxSelectedParentPrivatePatch.privatePatch, if_neg same]
    rw [QueryCache.cacheQuery_of_ne (spec := JointKdfRO) _ output (by simpa only [← address] using same)]
    rfl

noncomputable def decision (output : PqxdhFullSecretInputKdf.FullOutput) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) ×
      PqxdhInitialNativeRetained.RetainedState A N RootOracle.QueryCache) : Bool :=
  PqxdhInitialNativeParentRandom.retainedDecision
    (RawCtxSelectedParentPrivatePatch.privatePatch (productionStream source.crypto) (root source previousRoot response64 selected) output)
    (root source previousRoot response64 selected) selected number ancestors disclosed result.1

noncomputable def randomRun (output : PqxdhFullSecretInputKdf.FullOutput) :=
  (simulateQ (PqxdhInitialNativeRetained.retained source writer
    (RawCtxSelectedParentPrivatePatch.privatePatch (productionStream source.crypto) (root source previousRoot response64 selected) output)
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other))
    (PqxdhInitialNativeCarried.original source (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode (execution response64 index metadata ready post before))).run (shared, (privateState, cache))

/-- The complete actual stage-one source experiment, including its original publication and byte freshness event, is the early full76 child draw against the exact private-only patched function. The original initializer and every public HKDF evaluation remain real. -/
theorem game_source (number : Std.U64) (positive : 0 < number.val) (ancestors disclosed : List RatchetChain) :
    𝒟[game source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected number ancestors disclosed shared privateState cache 1] =
    𝒟[($ᵗ PqxdhFullSecretInputKdf.FullOutput) >>= fun output =>
      decision source previousRoot response64 selected output number ancestors disclosed <$>
        randomRun source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
          selected shared privateState cache output] := by
  have equality := PqxdhInitialNativeParentRandom.source_random source writer
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other)
    (PqxdhInitialNativeCarried.original source (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode (execution response64 index metadata ready post before))
    (initialState (root source previousRoot response64 selected) shared privateState cache) rfl
    (root source previousRoot response64 selected) selected number positive ancestors disclosed (by
      intro result supported gate
      exact published_cached source writer selectedMessage previousRoot response64 other sender route decode
        index metadata ready post before selected number shared privateState cache 1 result supported gate.2)
  refine equality.trans ?_
  apply evalDist_bind_congr' ($ᵗ PqxdhFullSecretInputKdf.FullOutput)
  intro output
  change 𝒟[(fun result => PqxdhInitialNativeParentRandom.retainedDecision
    (RawCtxSelectedParentTable.view (productionStream source.crypto)
      (QueryCache.cacheQuery (spec := JointKdfRO) (fun _ => none)
        (RawCtxFirstParentRisk.inputAddress (root source previousRoot response64 selected)) output))
    (root source previousRoot response64 selected) selected number ancestors disclosed result.1) <$>
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (RawCtxSelectedParentTable.view (productionStream source.crypto)
        (QueryCache.cacheQuery (spec := JointKdfRO) (fun _ => none)
          (RawCtxFirstParentRisk.inputAddress (root source previousRoot response64 selected)) output))
      (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other))
      (PqxdhInitialNativeCarried.original source (PqxdhInitialSelectedOrigin.mark source selectedMessage)
        sender route decode (execution response64 index metadata ready post before))).run (shared, (privateState, cache))] = _
  rw [initial_view]
  rfl

end BeaconcryptCore.Computational.PqxdhInitialSourceRandom

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRandom.initial_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRandom.initial_view
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRandom.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRandom.game_source
