import BeaconcryptCore.Computational.PqxdhInitialNativeParentSupport
import BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy
import BeaconcryptCore.Computational.PqxdhInitialPreparedRisk

/-!
Both local observer endpoints are instantiated on the same complete original source experiment. Every pending cut retains its actual source support, cursor depth and missing parent. The supported original publication theorem supplies the cached lineage after either continuation, while the exact prior-input collision event supplies child absence and parent separation.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhInitialSourcePreparedSecrecy
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

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
  (depth remaining : Nat)

local notation "initial" => PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response64
local notation "mark" => PqxdhInitialSelectedOrigin.mark source selectedMessage
local notation "execution" => PqxdhInitialSourceExperiment.execution response64 index metadata ready post before
local notation "root" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "state" => (PqxdhInitialSourceExperiment.initialState root shared privateState cache, ([] : List RootOutput))
local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer (pre other) (application other) initial (selector other) (aux other)
  mark sender route decode execution depth (depth + 1) state
local notation "sourceView" => view source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "sourceSample" => sample source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "sourceAddress" => address source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected shared privateState cache depth
local notation "external" => PqxdhInitialNativeAudit.external (pre other) (application other) initial (selector other) (aux other)



/-- The native full freshness observer compiles to the identical complete source result and exact suffix checker, with candidate instrumentation erased only from the final observation. -/
theorem native_decision (input : PqxdhInitialSupportedCertificate.Supported sourceRun) (parent output : FullOutput) :
    PqxdhInitialCommonSecrecy.native source writer mark sender route decode sourceView
      (Sum.inr input, RawCtxSelectedParentEntry.fromOutput (PqxdhInitialBuilderContext.address input.val.1.original) parent)
      (nextChain parent) output =
    (fun result => PqxdhInitialNativeParentEvent.nativeDecision
      (RawCtxSelectedParentTable.view (productionStream source.crypto) input.val.2.1.1.1.2.1)
      (RawCtxSelectedParentEntry.fromOutput (PqxdhInitialBuilderContext.address input.val.1.original) parent)
      (nextChain parent) output remaining
      ((((RawCtxCursorLineage.walk input.val.2.1.1.1.2.1 input.val.2.1.1.1.2.2.depth root).map Prod.fst).getD [] ++ [input.val.2.1.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain) ancestors disclosed selected number
      (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront (RawCtxSelectedParentCalls.nativeKernel (nextChain parent))) id)
        result.1)) <$>
    (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer
      (RawCtxSelectedParentTable.view (productionStream source.crypto) input.val.2.1.1.1.2.1)
      (RawCtxSelectedParentEntry.fromOutput (PqxdhInitialBuilderContext.address input.val.1.original) parent) output
      (pre other) (application other) initial (selector other) (aux other)
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain parent))) (nextChain parent))
      (simulateQ PqxdhInitialParentObserverCompiler.compiler
        (PqxdhInitialOriginContext.stopped mark sender route decode input.val.1 (material parent)))).run
      (PqxdhInitialNativeParentRealization.nested (PqxdhInitialNativeRetained.project input.val.2.1)) := by
  exact PqxdhInitialNativeParentChecked.decision_source source writer sender route decode mark
    (sourceView).continuation (input, RawCtxSelectedParentEntry.fromOutput (PqxdhInitialBuilderContext.address input.val.1.original) parent)
    (nextChain parent) output disclosed ((sourceView).ambient input) ((sourceView).priorCandidates input)
    remaining rfl ((((RawCtxCursorLineage.walk input.val.2.1.1.1.2.1 input.val.2.1.1.1.2.2.depth root).map Prod.fst).getD [] ++ [input.val.2.1.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain)
    ancestors selected number

/-- Both resumed actual source stages inherit the original successful-publication cache theorem from their literal supported prefix and full76 parent draw. -/
theorem published_cached (input : PqxdhInitialSupportedCertificate.Supported sourceRun)
    (supported : Sum.inr input ∈ support sourceSample) (parent : FullOutput)
    (stage : Nat) (adjacent : stage = depth + 1 ∨ stage = depth + 2)
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × PqxdhInitialOriginPostPath.State A N)
    (continued : result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage external)
      ((PqxdhInitialOriginContext.frame mark sender route decode input.val.1).2
        (PqxdhInitialParentBuilderContext.reply sender route decode input.val.1.original parent))).run
          (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address input.val.1.original) parent input.val.2.1)))
    (good : PqxdhInitialPublishedEvent.Gate selected number result.1) :
    RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1 := by
  have missing := (pending_selected source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth input supported).1
  have actualCut := supported_source source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected shared privateState cache depth input
  rw [← external_source source selectedMessage previousRoot response64 other] at actualCut
  have selectedCut : RawCtxForwardScan.Cut.pending input.val.1 input.val.2.1 ∈ support
      (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state.1) := by
    rcases adjacent with early | later
    · simpa only [early] using actualCut
    · rw [later, ← PqxdhInitialNativeCarried.carried_same source writer mark sender route decode execution depth external state.1
        (PqxdhInitialSourceExperiment.initial_valid root shared privateState cache depth).1.2.1]
      exact actualCut
  have complete := PqxdhInitialNativeParentSupport.parent_supported source writer mark sender route decode execution external
    depth stage (by omega) state.1 input.val.2.1
    (PqxdhInitialSourceExperiment.initial_valid root shared privateState cache depth).1.1 input.val.1 selectedCut missing parent
    result continued
  apply PqxdhInitialSourceExperiment.published_cached source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number shared privateState cache stage result _ good.2
  rw [PqxdhInitialSourceExperiment.run_source, ← external_source source selectedMessage previousRoot response64 other]
  exact complete

noncomputable def afterParent (stage : Nat) (input : PqxdhInitialSupportedCertificate.Supported sourceRun)
    (parent : FullOutput) : ProbComp Bool :=
  PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed <$>
    (simulateQ (PqxdhInitialNativeLog.handler source writer stage external)
      ((PqxdhInitialOriginContext.frame mark sender route decode input.val.1).2
        (PqxdhInitialParentBuilderContext.reply sender route decode input.val.1.original parent))).run
          (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address input.val.1.original) parent input.val.2.1)

/-- Outside the explicit prior-input and self-address event, actual source support supplies child absence and parent separation. -/
theorem safe_pending (input : PqxdhInitialSupportedCertificate.Supported sourceRun) (parent : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉
      input.val.2.1.1.2 ++ [PqxdhInitialBuilderContext.address input.val.1.original]) :
    input.val.2.1.1.1.2.1 (RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent)) = none ∧
      RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ≠ PqxdhInitialBuilderContext.address input.val.1.original := by
  have actual := PqxdhInitialPreparedRisk.safe_pending source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode execution depth state (PqxdhInitialSourceExperiment.initial_valid root shared privateState cache depth).1.1
    input (nextChain parent) safe
  exact ⟨actual.1, actual.2.1⟩

/-- The real later-step endpoint is the actual original source event and the concrete native reduction observer, outside only the explicitly charged input-collision event. -/
theorem real_endpoint (input : PqxdhInitialSupportedCertificate.Supported sourceRun)
    (supported : Sum.inr input ∈ support sourceSample) (parent : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉
      input.val.2.1.1.2 ++ [PqxdhInitialBuilderContext.address input.val.1.original])
    (position : number.val = (depth + 1) + remaining + 1) :
    afterParent source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected number ancestors disclosed shared privateState cache depth (depth + 1) input parent =
    PqxdhInitialCommonSecrecy.native source writer mark sender route decode sourceView
      (Sum.inr input, RawCtxSelectedParentEntry.fromOutput (PqxdhInitialBuilderContext.address input.val.1.original) parent)
      (nextChain parent) (productionStream source.crypto (FixedHkdfDomain.ratchet.address (nextChain parent).toList)) := by
  have chosen := pending_selected source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth input supported
  have absent := safe_pending source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected shared privateState cache depth input parent safe
  obtain ⟨past, walked, earlier⟩ := earlier_walk source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining input
  have actualOutput : RawCtxSelectedParentTable.view (productionStream source.crypto) input.val.2.1.1.1.2.1
      (RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent)) =
      productionStream source.crypto (FixedHkdfDomain.ratchet.address (nextChain parent).toList) := by
    simp only [RawCtxSelectedParentTable.view, absent.1, Option.getD_none]
    exact congrArg (productionStream source.crypto) (PqxdhInitialNativeLineageCheck.request_concrete (nextChain parent))
  rw [← actualOutput, native_decision]
  simp only [walked, Option.map_some, Option.getD_some]
  unfold afterParent
  have equality := PqxdhInitialNativeParentRandom.frame_real source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode input.val.1 parent input.val.2.1 chosen.1 chosen.2.1 absent.2 root past walked
    selected number remaining (by omega) ancestors disclosed (fun result reached good =>
      published_cached source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
    selected number ancestors disclosed shared privateState cache depth input supported parent _ (Or.inl (by rw [chosen.2.2])) result reached good)
  simpa only [chosen.2.2] using equality

/-- The randomized later-step endpoint uses the same original source event and concrete native observer, with every publication-cache premise derived from the source execution. -/
theorem random_endpoint (input : PqxdhInitialSupportedCertificate.Supported sourceRun)
    (supported : Sum.inr input ∈ support sourceSample) (parent : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉
      input.val.2.1.1.2 ++ [PqxdhInitialBuilderContext.address input.val.1.original])
    (position : number.val = (depth + 1) + remaining + 1) :
    𝒟[afterParent source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected number ancestors disclosed shared privateState cache depth (depth + 2) input parent] =
    𝒟[($ᵗ FullOutput) >>= fun output =>
      PqxdhInitialCommonSecrecy.native source writer mark sender route decode sourceView
        (Sum.inr input, RawCtxSelectedParentEntry.fromOutput (PqxdhInitialBuilderContext.address input.val.1.original) parent)
        (nextChain parent) output] := by
  have chosen := pending_selected source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth input supported
  have absent := safe_pending source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected shared privateState cache depth input parent safe
  obtain ⟨past, walked, earlier⟩ := earlier_walk source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining input
  simp only [native_decision, walked, Option.map_some, Option.getD_some]
  unfold afterParent
  have equality := PqxdhInitialNativeParentRandom.frame_random source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode input.val.1 parent input.val.2.1 chosen.1 chosen.2.1 absent.1 absent.2 root past walked
    selected number remaining (by omega) ancestors disclosed (fun result reached good =>
      published_cached source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
        selected number ancestors disclosed shared privateState cache depth input supported parent _ (Or.inr (by rw [chosen.2.2])) result reached good)
  simpa only [chosen.2.2] using equality

end BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.native_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.native_decision
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.published_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.published_cached
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.safe_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.safe_pending
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.real_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.real_endpoint
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.random_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints.random_endpoint
