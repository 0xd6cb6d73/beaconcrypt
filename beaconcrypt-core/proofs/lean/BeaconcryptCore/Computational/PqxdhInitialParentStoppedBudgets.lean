import BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop
import BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets

/-!
The full stopped primitive endpoint consumes the original outside-post budget, the actual initial candidate-list bound and the individual external callback costs. Its complete observer and candidate bills are derived from those source resources. The certificate contains no whole-observer, whole-source security or final freshness premise. The concrete source sampler supplies this certificate using its carried source descriptor and complete initial private state.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialParentStoppedHop PqxdhInitialParentObserverBudgets RawCtxSelectedParentEntry
open RawCtxSelectedParentHop (extractLoss hmacLoss)
variable {ι Context M P I D K X Response Shared A N C Result Origin : Type}
  {extra : OracleSpec ι} {S B : Nat}

structure Certificate
    (continuation : Continuation Context extra M P I D K X Response Shared A N C Result Origin S B) where
  qPost : Nat
  qPrior : Nat
  qCheck : Nat
  costs : Costs
  fits : ∀ context, PqxdhInitialBuilderCertificates.Fits qPost (continuation.cut context).original
  checkBound : ∀ context, checkerBudget (continuation.depth context) ≤ qCheck
  priorBound : ∀ context, (continuation.initial context).1.2.length ≤ qPrior
  external : ∀ context, ExternalUniform costs (continuation.pre context) (continuation.application context)
    (continuation.initializer context) (continuation.selector context) (continuation.aux context)

def callbackBudget
    {continuation : Continuation Context extra M P I D K X Response Shared A N C Result Origin S B}
    (certificate : Certificate continuation) : Nat := 2 * (255 + certificate.qPost * 67) + certificate.qCheck

def uniformBudget
    {continuation : Continuation Context extra M P I D K X Response Shared A N C Result Origin S B}
    (certificate : Certificate continuation) : Nat := callbackBudget certificate * certificate.costs.cap

def candidateBudget
    {continuation : Continuation Context extra M P I D K X Response Shared A N C Result Origin S B}
    (certificate : Certificate continuation) : Nat := certificate.qPrior + 3 * callbackBudget certificate

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (continuation : Continuation Context extra M P I D K X Response Shared A N C Result Origin S B)
  (certificate : Certificate continuation)

/-- The actual full stopped observer pays its source-certified callback count and each separate original external cost, without a whole-observer resource premise. -/
theorem source_uniform (context : Context × Entry) (output : FullOutput) :
    (observed source writer mark sender route decode continuation context output).IsTotalQueryBound
      (uniformBudget certificate) :=
  complete_uniform source writer (continuation.prior context.1) context.2 output
    (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
    (continuation.selector context.1) (continuation.aux context.1) certificate.costs (certificate.external context.1)
    RawCtxSelectedLiveRead.labelRead (program mark sender route decode continuation context) (callbackBudget certificate)
    ((program_total mark sender route decode continuation context certificate.qPost (certificate.fits context.1)).mono
      (Nat.add_le_add_left (certificate.checkBound context.1) _))
    (continuation.initial context)

/-- The complete original initial ledger, every stopped-source callback and every appended checker query determine the actual candidate cap. -/
theorem source_candidates (context : Context × Entry) (output : FullOutput)
    (result : Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support (observed source writer mark sender route decode continuation context output)) :
    (candidates result).length ≤ candidateBudget certificate := by
  have traceBound := trace_length
    (PqxdhInitialParentObserver.handler source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) RawCtxSelectedLiveRead.labelRead)
    (program mark sender route decode continuation context) (callbackBudget certificate)
    ((program_total mark sender route decode continuation context certificate.qPost (certificate.fits context.1)).mono
      (Nat.add_le_add_left (certificate.checkBound context.1) _))
    (continuation.initial context) result supported
  exact traceBound.trans (Nat.add_le_add_right (certificate.priorBound context) _)

/-- The full source-and-checker comparison uses the computed entire candidate cap; the certificate contains neither an alias-probability premise nor a whole-observer resource bound. -/
theorem source_bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (sample : ProbComp Context) :
    (actual source writer mark sender route decode continuation sample).boolDistAdvantage
      (random source writer mark sender route decode continuation sample) ≤
      extractLoss hmac sample (address continuation) (observer source writer mark sender route decode continuation) +
        hmacLoss hmac sample (address continuation) (observer source writer mark sender route decode continuation) +
        extractLoss hmac sample (address continuation) (aliasTester source writer mark sender route decode continuation) +
        hmacLoss hmac sample (address continuation) (aliasTester source writer mark sender route decode continuation) +
        (2 ^ 352 : ℝ)⁻¹ + (candidateBudget certificate : ℝ) / (2 ^ 256 : ℝ) :=
  PqxdhInitialParentStoppedHop.bound source writer mark sender route decode continuation hmac correct sample
    (candidateBudget certificate) (source_candidates source writer mark sender route decode continuation certificate)

/-- Both actual main/tester reductions have two HMAC challenges and the derived source/checker random bill; every tester fixed-HKDF evaluation is also counted. -/
theorem source_reduction_queries (sample : ProbComp Context) (qSample : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample) :
    (∀ forTester, let observe := reductionObserver source writer mark sender route decode continuation forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sample (address continuation)) observe).IsQueryBoundP
        IsHmacChallengeQuery 2 ∧
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sample (address continuation)) observe).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 76) + uniformBudget certificate)) ∧
      (∀ context output result, result ∈ support (observed source writer mark sender route decode continuation context output) →
        (RawCtxFullPreimageTester.evaluate output (candidates result)).IsTotalQueryBound (candidateBudget certificate)) :=
  PqxdhInitialParentStoppedHop.reduction_queries source writer mark sender route decode continuation sample
    qSample (uniformBudget certificate) (candidateBudget certificate) sampleBound
    (source_uniform source writer mark sender route decode continuation certificate)
    (source_candidates source writer mark sender route decode continuation certificate)

/-- Every Extract/HMAC challenger world consumes the computed full source/checker budget and separately pays for its actual64-byte blocks or76-byte child draw. -/
theorem source_challenger_queries (hmac : HmacSha512) (sample : ProbComp Context) (qSample : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample) (forTester : Bool) :
    let observe := reductionObserver source writer mark sender route decode continuation forTester
    let joint := RawCtxSelectedParentSecrecy.joint sample (address continuation)
    let qObserve := uniformBudget certificate
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + qObserve) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        (64 + ((qSample + 76) + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + (64 + qObserve))) ∧
      (RawCtxSelectedParentSecrecy.random sample (address continuation) observe).IsTotalQueryBound
        ((qSample + 76) + (76 + qObserve)) :=
  PqxdhInitialParentStoppedHop.challenger_queries source writer mark sender route decode continuation hmac sample
    qSample (uniformBudget certificate) sampleBound
    (source_uniform source writer mark sender route decode continuation certificate) forTester

end BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_candidates
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_reduction_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets.source_challenger_queries
