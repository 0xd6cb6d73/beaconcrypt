import BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy
import BeaconcryptCore.Computational.PqxdhInitialPreparedResources

/-!
The full parent-to-child reduction is instantiated on the actual source-supported saved descriptor. Its earlier ancestors are obtained by executing the reached private-cache walk from the original directional root. The complete reached state, disclosure seed, publication gate and prepared source sampler are retained. The original source callback bound derives the candidate and uniform budgets; no whole-observer budget is assumed.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialSupportedCertificate RawCtxSelectedParentEntry
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

def earlierInputs (root : RootOutput) (input : Input extra M P I D K Bool Bool A N C S B) : List RootOutput :=
  ((RawCtxCursorLineage.walk input.2.1.1.1.2.1 input.2.1.1.1.2.2.depth root).map Prod.fst).getD [] ++
    [input.2.1.1.1.2.2.input]

def earlier (root : RootOutput) (ancestors : List RatchetChain)
    (input : Input extra M P I D K Bool Bool A N C S B) : List RatchetChain :=
  (earlierInputs root input).map RawCtxFreshChainCut.concreteChain ++ ancestors

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Bool Bool S B)
  (depth : Nat) (state : PqxdhInitialNativeAudit.State A N C)

local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer pre application initializer selector aux
  mark sender route decode execution depth (depth + 1) state

variable (root : RootOutput) (ancestors disclosed : List RatchetChain)
  (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (remaining : Nat)

noncomputable def view : PqxdhInitialCommonSecrecy.View (Supported sourceRun) extra M P I D K X Response Shared A N C S B where
  continuation := continuation source pre application initializer selector aux sourceRun disclosed remaining
    (fun input => PqxdhInitialPrivateCheckedFreshness.remainingEvent (earlier root ancestors input.1.val) disclosed
      (fun result => PqxdhInitialPublishedEvent.Gate selected number result.1.1))
  disclosed := disclosed
  earlier input := earlier root ancestors input.val
  ambient input := ambient input.val
  priorCandidates input := input.val.2.2
  selected := selected
  number := number
  remaining := remaining
  depth _ := rfl

local notation "sourceView" => view source writer pre application initializer selector aux mark sender route decode
  execution depth state root ancestors disclosed selected number remaining

/-- The concrete source carrier derives the earlier root walk from the original zero-depth cursor; no final lineage agreement is assumed. -/
theorem earlier_walk (initialCursor : state.1.1.1.2.2 = ⟨root, 0⟩) (input : Supported sourceRun) :
    ∃ past, RawCtxCursorLineage.walk input.val.2.1.1.1.2.1 input.val.2.1.1.1.2.2.depth root =
      some (past, input.val.2.1.1.1.2.2.input) ∧
      (sourceView).earlier input = (past ++ [input.val.2.1.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain ++ ancestors := by
  have supported : RawCtxForwardScan.Cut.pending input.val.1 input.val.2.1 ∈ support
      (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth (depth + 1)
        (PqxdhInitialNativeAudit.external pre application initializer selector aux) state.1) := by
    rw [← PqxdhInitialNativeAuditCarried.carried_projection source writer pre application initializer selector aux
      mark sender route decode execution depth (depth + 1) state, support_map]
    exact ⟨.pending input.val.1 input.val.2, input.property, rfl⟩
  obtain ⟨past, walked⟩ := PqxdhInitialPublishedEvent.carried_lineage source writer mark sender route decode execution
    depth (depth + 1) (PqxdhInitialNativeAudit.external pre application initializer selector aux)
    root state.1 input.val.2.1 initialCursor input.val.1 supported
  exact ⟨past, walked, by simp only [view, earlier, earlierInputs, walked, Option.map_some, Option.getD_some]⟩

variable (qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
  (costs : PqxdhInitialParentObserverBudgets.Costs)
  (callbacks : PqxdhInitialParentObserverBudgets.ExternalUniform costs pre application initializer selector aux)

def callbackBudget : Nat := 2 * (255 + qPost * 67) + (remaining + 1)
def uniformBudget : Nat := callbackBudget remaining qPost * costs.cap
def candidateBudget : Nat := priorBudget execution qPost state disclosed + 3 * callbackBudget remaining qPost

include bounded callbacks in
/-- The exact masked continuation uses the actual saved-history seed, so the source-derived certificate discharges both its full uniform bill and candidate cap. -/
theorem pending_bounds (context : Supported sourceRun × Entry) (output : FullOutput) :
    let work := PqxdhInitialCheckedFreshness.maskedRun source writer mark sender route decode
      (sourceView).continuation context output disclosed ((sourceView).ambient context.1) ((sourceView).priorCandidates context.1)
    work.IsTotalQueryBound (uniformBudget remaining qPost costs) ∧
      ∀ result, result ∈ support work → (PqxdhInitialParentStoppedHop.candidates result).length ≤
        candidateBudget execution state disclosed remaining qPost := by
  exact PqxdhInitialPreparedResources.pending_resources source writer pre application initializer selector aux mark sender route decode
    execution depth state qPost bounded costs callbacks disclosed remaining _ context output

include bounded callbacks in
/-- Common decisions and all supported pending continuations instantiate the full observer bill with no whole-observer resource hypothesis. -/
theorem observed_uniform (context : (Bool ⊕ Supported sourceRun) × Entry) (output : FullOutput) :
    (PqxdhInitialCommonSecrecy.observed source writer mark sender route decode sourceView context output).IsTotalQueryBound
      (uniformBudget remaining qPost costs) := by
  apply PqxdhInitialCommonSecrecy.observed_bound
  intro pending response
  exact (pending_bounds source writer pre application initializer selector aux mark sender route decode execution depth state
    root ancestors disclosed selected number remaining qPost bounded costs callbacks pending response).1

include bounded callbacks in
/-- Candidate accounting includes the actual pre-cut history and audit, every stopped callback, and every appended checker query. -/
theorem candidates_bound (context : (Bool ⊕ Supported sourceRun) × Entry) (output : FullOutput)
    (result : PqxdhInitialCommonSecrecy.Trace M P I D K A N C S B)
    (supported : result ∈ support (PqxdhInitialCommonSecrecy.observed source writer mark sender route decode sourceView context output)) :
    (PqxdhInitialCommonSecrecy.candidates result).length ≤ candidateBudget execution state disclosed remaining qPost := by
  apply PqxdhInitialCommonSecrecy.candidates_bound
  · intro pending response
    exact (pending_bounds source writer pre application initializer selector aux mark sender route decode execution depth state
      root ancestors disclosed selected number remaining qPost bounded costs callbacks pending response).2
  · exact supported

variable (observe : PqxdhInitialPreparedParent.Output M P I D K Bool Bool A N C S B → ProbComp Bool)

local notation "sourceSample" => PqxdhInitialPreparedResources.sample source writer pre application initializer selector aux
  mark sender route decode observe execution depth state
local notation "sourceAddress" => PqxdhInitialPreparedResources.address source writer pre application initializer selector aux
  mark sender route decode execution depth state
local notation "mainObserver" => PqxdhInitialCommonSecrecy.observer source writer mark sender route decode sourceView
local notation "testObserver" => PqxdhInitialCommonSecrecy.aliasTester source writer mark sender route decode sourceView

include bounded callbacks in
/-- The actual supported source sampler instantiates the full native-freshness reduction with its computed candidate cap, rather than a whole-observer hypothesis. -/
theorem bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) :
    (PqxdhInitialCommonSecrecy.actual source writer mark sender route decode sourceView sourceSample sourceAddress).boolDistance
      (PqxdhInitialCommonSecrecy.random source writer mark sender route decode sourceView sourceSample sourceAddress) ≤
      RawCtxSelectedParentHop.extractLoss hmac sourceSample sourceAddress mainObserver +
        RawCtxSelectedParentHop.hmacLoss hmac sourceSample sourceAddress mainObserver +
        3 * (RawCtxSelectedParentHop.extractLoss hmac sourceSample sourceAddress testObserver +
          RawCtxSelectedParentHop.hmacLoss hmac sourceSample sourceAddress testObserver +
          (2 ^ 352 : ℝ)⁻¹ + (candidateBudget execution state disclosed remaining qPost : ℝ) / (2 ^ 256 : ℝ)) := by
  exact PqxdhInitialCommonSecrecy.bound source hmac correct writer mark sender route decode sourceView sourceSample sourceAddress
    (candidateBudget execution state disclosed remaining qPost)
    (candidates_bound source writer pre application initializer selector aux mark sender route decode execution depth state
      root ancestors disclosed selected number remaining qPost bounded costs callbacks)

variable (qObserve : Nat) (observeBound : ∀ result, (observe result).IsTotalQueryBound qObserve)

def sampleBudget : Nat := PqxdhInitialAuditedResources.uniformBudget costs qPost + qObserve

include bounded callbacks observeBound in
/-- Both constructed HMAC adversaries pay two challenge calls and the actual complete prepared source, parent draw and stopped observer coins; the tester additionally pays the full real-HKDF candidate cap. -/
theorem reduction_queries :
    (∀ forTester, let observer := PqxdhInitialCommonSecrecy.reductionObserver source writer mark sender route decode sourceView forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress) observer).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress) observer).IsQueryBoundP
          PqxdhFullSecretInputKdf.IsHmacUniformQuery
            ((sampleBudget qPost costs qObserve + 76) + uniformBudget remaining qPost costs)) ∧
      (∀ context output result, result ∈ support
        (PqxdhInitialCommonSecrecy.observed source writer mark sender route decode sourceView context output) →
        (RawCtxFullPreimageTester.evaluate output (PqxdhInitialCommonSecrecy.candidates result)).IsTotalQueryBound
          (candidateBudget execution state disclosed remaining qPost)) := by
  exact PqxdhInitialCommonSecrecy.reduction_queries source writer mark sender route decode sourceView sourceSample sourceAddress
    (sampleBudget qPost costs qObserve) (uniformBudget remaining qPost costs) (candidateBudget execution state disclosed remaining qPost)
    (PqxdhInitialPreparedResources.sample_uniform source writer pre application initializer selector aux mark sender route decode observe
      execution depth state qPost qObserve bounded costs callbacks observeBound)
    (observed_uniform source writer pre application initializer selector aux mark sender route decode execution depth state
      root ancestors disclosed selected number remaining qPost bounded costs callbacks)
    (candidates_bound source writer pre application initializer selector aux mark sender route decode execution depth state
      root ancestors disclosed selected number remaining qPost bounded costs callbacks)

include bounded callbacks observeBound in
/-- The actual complete source bills also instantiate both ordinary primitive challengers, including Extract and HMAC keys, both random HMAC blocks and the independent full child. -/
theorem challenger_queries (hmac : HmacSha512) (forTester : Bool) :
    let observer := PqxdhInitialCommonSecrecy.reductionObserver source writer mark sender route decode sourceView forTester
    let joint := RawCtxSelectedParentSecrecy.joint sourceSample sourceAddress
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observer)).IsTotalQueryBound
        ((sampleBudget qPost costs qObserve + 76) + uniformBudget remaining qPost costs) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observer)).IsTotalQueryBound
        ((sampleBudget qPost costs qObserve + 76) + (64 + uniformBudget remaining qPost costs)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observer)).IsTotalQueryBound
        (64 + ((sampleBudget qPost costs qObserve + 76) + uniformBudget remaining qPost costs)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observer)).IsTotalQueryBound
        ((sampleBudget qPost costs qObserve + 76) + (64 + (64 + uniformBudget remaining qPost costs))) ∧
      (RawCtxSelectedParentSecrecy.random sourceSample sourceAddress observer).IsTotalQueryBound
        ((sampleBudget qPost costs qObserve + 76) + (76 + uniformBudget remaining qPost costs)) := by
  exact PqxdhInitialCommonSecrecy.challenger_queries source hmac writer mark sender route decode sourceView sourceSample sourceAddress
    (sampleBudget qPost costs qObserve) (uniformBudget remaining qPost costs)
    (PqxdhInitialPreparedResources.sample_uniform source writer pre application initializer selector aux mark sender route decode observe
      execution depth state qPost qObserve bounded costs callbacks observeBound)
    (observed_uniform source writer pre application initializer selector aux mark sender route decode execution depth state
      root ancestors disclosed selected number remaining qPost bounded costs callbacks) forTester

end BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.earlier_walk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.earlier_walk

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.pending_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.pending_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.observed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.observed_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.candidates_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.candidates_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.reduction_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources.challenger_queries
