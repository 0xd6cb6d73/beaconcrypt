import BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources
import BeaconcryptCore.Computational.PqxdhInitialSourceExperiment

/-!
The supported secrecy reduction is now instantiated on the literal source experiment: the actual supplied Server kernel, empty selective table and input log, original selected-session origin marker, complete builder/post program, retained initializer and pure original publication/freshness decision. Four original external callback coin contracts remain explicit; the actual initializer's32-call bound is derived. These are query bounds, not a claim that deterministic primitive, parser, source, bookkeeping or observation work is free.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
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

def pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache) := fun query => other (.inl query)
def application : Response → Ambient A N RootOracle.QueryCache (Option Pqxdh.Bytes) :=
  fun reply => other (.inr (.inl reply))
def selector : QueryImpl extra (Ambient A N RootOracle.QueryCache) := fun query => other (.inr (.inr (.inr (.inl query))))
def aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N RootOracle.QueryCache) :=
  fun query => other (.inr (.inr (.inr (.inr query))))

local notation "initial" => PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response64
local notation "mark" => PqxdhInitialSelectedOrigin.mark source selectedMessage
local notation "execution" => PqxdhInitialSourceExperiment.execution response64 index metadata ready post before
local notation "root" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "state" => (PqxdhInitialSourceExperiment.initialState root shared privateState cache, ([] : List RootOutput))

noncomputable def observe (result : PqxdhInitialPreparedParent.Output M P I D K Bool Bool A N RootOracle.QueryCache S B) : ProbComp Bool :=
  pure (PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed result)

local notation "observation" => observe source previousRoot response64 selected number ancestors disclosed
local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer (pre other) (application other) initial (selector other) (aux other)
  mark sender route decode execution depth (depth + 1) state

noncomputable def view :=
  PqxdhInitialSourceSecrecyResources.view source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode execution depth state root ancestors disclosed selected number remaining

noncomputable def sample :=
  PqxdhInitialPreparedResources.sample source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode observation execution depth state

noncomputable def address :=
  PqxdhInitialPreparedResources.address source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode execution depth state

local notation "sourceView" => view source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "sourceSample" => sample source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "sourceAddress" => address source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected shared privateState cache depth

/-- Erasing the initializer audit yields exactly the complete original external source interface. -/
theorem external_source :
    PqxdhInitialNativeAudit.external (pre other) (application other) initial (selector other) (aux other) =
      PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other := by
  funext query
  rcases query with query | (reply | (secrets | (query | query))) <;> rfl

/-- The selected source's earlier ancestor list is the actual reached cache walk from its actual initialized directional root. -/
theorem earlier_walk (input : PqxdhInitialSupportedCertificate.Supported sourceRun) :
    ∃ past, RawCtxCursorLineage.walk input.val.2.1.1.1.2.1 input.val.2.1.1.1.2.2.depth root =
      some (past, input.val.2.1.1.1.2.2.input) ∧
      (sourceView).earlier input = (past ++ [input.val.2.1.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain ++ ancestors := by
  exact PqxdhInitialSourceSecrecyResources.earlier_walk source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode execution depth state root ancestors disclosed selected number remaining rfl input

noncomputable def actual : ProbComp Bool :=
  PqxdhInitialCommonSecrecy.actual source writer mark sender route decode sourceView sourceSample sourceAddress
noncomputable def random : ProbComp Bool :=
  PqxdhInitialCommonSecrecy.random source writer mark sender route decode sourceView sourceSample sourceAddress
noncomputable def observer := PqxdhInitialCommonSecrecy.observer source writer mark sender route decode sourceView
noncomputable def tester := PqxdhInitialCommonSecrecy.aliasTester source writer mark sender route decode sourceView

local notation "mainObserver" => observer source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "testObserver" => tester source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "actualGame" => actual source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "randomGame" => random source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining

/-- Every source-supported saved descriptor projects to the same complete original carried prefix. -/
theorem supported_source (input : PqxdhInitialSupportedCertificate.Supported sourceRun) :
    RawCtxForwardScan.Cut.pending input.val.1 input.val.2.1 ∈ support
      (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth (depth + 1)
        (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other)
        (PqxdhInitialSourceExperiment.initialState root shared privateState cache)) := by
  rw [← external_source source selectedMessage previousRoot response64 other,
    ← PqxdhInitialNativeAuditCarried.carried_projection source writer (pre other) (application other) initial
      (selector other) (aux other) mark sender route decode execution depth (depth + 1) state, support_map]
  exact ⟨.pending input.val.1 input.val.2, input.property, rfl⟩

/-- Every pending value returned by the actual prepared sampler is missing, matches its reached source cursor, and has exactly the selected cut depth. -/
theorem pending_selected (input : PqxdhInitialSupportedCertificate.Supported sourceRun)
    (supported : Sum.inr input ∈ support sourceSample) :
    input.val.2.1.1.1.2.1 (PqxdhInitialBuilderContext.address input.val.1.original) = none ∧
      RawCtxSelectiveChainGame.matched input.val.2.1.1.1.2.2 (PqxdhInitialBuilderContext.address input.val.1.original) = true ∧
      input.val.2.1.1.1.2.2.depth = depth := by
  have missing := PqxdhInitialPreparedResources.sample_missing source writer (pre other) (application other) initial
    (selector other) (aux other) mark sender route decode observation execution depth state input supported
  have cases := PqxdhInitialNativeCarried.carried_cases source writer mark sender route decode execution depth (depth + 1)
    (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other)
    (PqxdhInitialSourceExperiment.initialState root shared privateState cache) input.val.2.1
    (PqxdhInitialSourceExperiment.initial_valid root shared privateState cache depth).1.1 input.val.1
    (supported_source source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
      selected shared privateState cache depth input)
  refine ⟨missing, cases.1, ?_⟩
  rcases cases.2 with hit | miss
  · obtain ⟨response, found⟩ := hit.2
    rw [missing] at found
    cases found
  · exact miss.2

variable (qPost qPre qApplication qSelector qAux : Nat)
  (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
  (preBound : ∀ query ambientState rootCache, (pre other query ambientState rootCache).IsTotalQueryBound qPre)
  (applicationBound : ∀ query ambientState rootCache, (application other query ambientState rootCache).IsTotalQueryBound qApplication)
  (selectorBound : ∀ query ambientState rootCache, (selector other query ambientState rootCache).IsTotalQueryBound qSelector)
  (auxBound : ∀ query ambientState rootCache, (aux other query ambientState rootCache).IsTotalQueryBound qAux)

local notation "costs" => PqxdhInitialAuditedResources.retainedCosts qPre qApplication qSelector qAux

def candidateBudget : Nat := PqxdhInitialHistoryBudget.knownLength disclosed before.roles.2 + qPost + 3 * (7 + qPost * 67) +
  3 * (2 * (255 + qPost * 67) + (remaining + 1))
def sampleBudget : Nat := PqxdhInitialAuditedResources.uniformBudget costs qPost
def observerBudget : Nat := (2 * (255 + qPost * 67) + (remaining + 1)) * (64 + qPre + qApplication + 32 + qSelector + qAux)

local notation "Q" => candidateBudget before disclosed remaining qPost
local notation "U" => observerBudget remaining qPost qPre qApplication qSelector qAux
local notation "V" => sampleBudget qPost qPre qApplication qSelector qAux

noncomputable def loss (hmac : HmacSha512) : ℝ :=
  RawCtxSelectedParentHop.extractLoss hmac sourceSample sourceAddress mainObserver +
    RawCtxSelectedParentHop.hmacLoss hmac sourceSample sourceAddress mainObserver +
    3 * (RawCtxSelectedParentHop.extractLoss hmac sourceSample sourceAddress testObserver +
      RawCtxSelectedParentHop.hmacLoss hmac sourceSample sourceAddress testObserver +
      (2 ^ 352 : ℝ)⁻¹ + (Q : ℝ) / (2 ^ 256 : ℝ))

include bounded preBound applicationBound selectorBound auxBound in
/-- The exact source-selected, common-or-pending sampler and its native freshness observer satisfy the constructed Extract/HMAC bound with the source-derived candidate cap. -/
theorem bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) :
    (actualGame).boolDistAdvantage randomGame ≤
      loss source writer selectedMessage previousRoot response64 other sender route decode index metadata ready post before
        selected number ancestors disclosed shared privateState cache depth remaining qPost hmac := by
  simpa only [actual, random, loss, observer, tester, view, sample, address,
    PqxdhInitialSourceSecrecyResources.candidateBudget, PqxdhInitialSourceSecrecyResources.callbackBudget,
    PqxdhInitialSupportedCertificate.priorBudget, PqxdhInitialSourceExperiment.execution, List.length_nil, Nat.add_zero,
    candidateBudget] using
    PqxdhInitialSourceSecrecyResources.bound source writer (pre other) (application other) initial (selector other) (aux other)
      mark sender route decode execution depth state root ancestors disclosed selected number remaining qPost bounded costs
      (PqxdhInitialAuditedResources.retained_callbacks source selectedMessage previousRoot response64
        (pre other) (application other) (selector other) (aux other) qPre qApplication qSelector qAux
        preBound applicationBound selectorBound auxBound) observation hmac correct

include bounded preBound applicationBound selectorBound auxBound in
/-- The complete original prepared sampler pays the concrete source cap; its final Boolean observation adds no uniform query. -/
theorem sample_uniform : (sourceSample).IsTotalQueryBound V := by
  simpa only [sample, sampleBudget, Nat.add_zero] using
    PqxdhInitialPreparedResources.sample_uniform source writer (pre other) (application other) initial (selector other) (aux other)
      mark sender route decode observation execution depth state qPost 0 bounded costs
      (PqxdhInitialAuditedResources.retained_callbacks source selectedMessage previousRoot response64
        (pre other) (application other) (selector other) (aux other) qPre qApplication qSelector qAux
        preBound applicationBound selectorBound auxBound) (fun _ => by trivial)

include bounded preBound applicationBound selectorBound auxBound in
/-- Both concrete source reductions retain two HMAC challenge calls and the complete original source/parent/observer uniform bill; the separate tester retains every candidate evaluation. -/
theorem reduction_queries :
    (∀ forTester, let observe := PqxdhInitialCommonSecrecy.reductionObserver source writer mark sender route decode sourceView forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress) observe).IsQueryBoundP
          PqxdhFullSecretInputKdf.IsHmacUniformQuery ((V + 76) + U)) ∧
      (∀ context output result, result ∈ support
        (PqxdhInitialCommonSecrecy.observed source writer mark sender route decode sourceView context output) →
        (RawCtxFullPreimageTester.evaluate output (PqxdhInitialCommonSecrecy.candidates result)).IsTotalQueryBound Q) := by
  simpa only [sample, sampleBudget, observerBudget, view, address,
    PqxdhInitialSourceSecrecyResources.sampleBudget, PqxdhInitialSourceSecrecyResources.uniformBudget,
    PqxdhInitialSourceSecrecyResources.candidateBudget, PqxdhInitialSourceSecrecyResources.callbackBudget,
    PqxdhInitialSupportedCertificate.priorBudget, PqxdhInitialSourceExperiment.execution, List.length_nil, Nat.add_zero,
    PqxdhInitialParentObserverBudgets.Costs.cap, PqxdhInitialAuditedResources.retainedCosts, candidateBudget] using
    PqxdhInitialSourceSecrecyResources.reduction_queries source writer (pre other) (application other) initial (selector other) (aux other)
      mark sender route decode execution depth state root ancestors disclosed selected number remaining qPost bounded costs
      (PqxdhInitialAuditedResources.retained_callbacks source selectedMessage previousRoot response64
        (pre other) (application other) (selector other) (aux other) qPre qApplication qSelector qAux
        preBound applicationBound selectorBound auxBound) observation 0 (fun _ => by trivial)

include bounded preBound applicationBound selectorBound auxBound in
/-- Ordinary-game challenger costs include the original source and observer, Extract replacement, HMAC key, both random HMAC blocks and the independent child. -/
theorem challenger_queries (hmac : HmacSha512) (forTester : Bool) :
    let observe := PqxdhInitialCommonSecrecy.reductionObserver source writer mark sender route decode sourceView forTester
    let joint := RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((V + 76) + U) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((V + 76) + (64 + U)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound (64 + ((V + 76) + U)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound ((V + 76) + (64 + (64 + U))) ∧
      (RawCtxSelectedParentSecrecy.random sourceSample sourceAddress observe).IsTotalQueryBound ((V + 76) + (76 + U)) := by
  simpa only [sample, sampleBudget, observerBudget, view, address,
    PqxdhInitialSourceSecrecyResources.sampleBudget, PqxdhInitialSourceSecrecyResources.uniformBudget,
    PqxdhInitialSourceSecrecyResources.callbackBudget, Nat.add_zero,
    PqxdhInitialParentObserverBudgets.Costs.cap, PqxdhInitialAuditedResources.retainedCosts] using
    PqxdhInitialSourceSecrecyResources.challenger_queries source writer (pre other) (application other) initial (selector other) (aux other)
      mark sender route decode execution depth state root ancestors disclosed selected number remaining qPost bounded costs
      (PqxdhInitialAuditedResources.retained_callbacks source selectedMessage previousRoot response64
        (pre other) (application other) (selector other) (aux other) qPre qApplication qSelector qAux
        preBound applicationBound selectorBound auxBound) observation 0 (fun _ => by trivial) hmac forTester

end BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.external_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.external_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.earlier_walk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.earlier_walk

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.supported_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.supported_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.pending_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.pending_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.sample_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.sample_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.reduction_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy.challenger_queries
