import BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy
import BeaconcryptCore.Computational.RawCtxFullPreimageTester

/-!
The candidate tests retain the actual full predecessor draw and its material-only context. Real-child guesses pay their own Extract/HMAC tester and a finite-image term; uniform-child guesses use the separate delayed-coordinate bound. The real tester evaluates the unchanged public function on the actual returned candidates. Neither a real correlated child nor the retained predecessor is silently treated as an independent source. The native composition supplies the source-reachable prefix, stopped continuation and concrete list budget.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentCandidates
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhOrderedChainHybrids RawCtxSelectedParentEntry

noncomputable def sample {Context : Type} (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) : ProbComp ((Context × Entry) × RootOutput) := do
  let context ← priorSample
  let parent ← $ᵗ FullOutput
  pure ((context, fromOutput (address context) parent), nextChain parent)

/-- The tester and main reduction receive precisely the same retained predecessor/input sampler. -/
theorem bytes_same {Context : Type} (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) :
    RawCtxFullPreimageTester.byteSampler (sample priorSample address) =
      RawCtxSelectedParentSecrecy.joint priorSample address := by
  simp only [RawCtxFullPreimageTester.byteSampler, sample, RawCtxSelectedParentSecrecy.joint, map_bind, map_pure]

/-- Real-child input recovery pays the additional exact-sampler tester advantages; it is not assigned a uniform guessing bound. -/
theorem real_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (priorSample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : Context × Entry → FullOutput → ProbComp Result) (candidates : Result → List RootOutput) :
    Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
        (sample priorSample address) observe)}[pair.1 ∈ candidates pair.2] ≤
      (2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
        (extractRealGame hmac (RawCtxSelectedParentSecrecy.joint priorSample address)
          (fullExtractReduction hmac .ratchet
            (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates))).boolDistAdvantage
        (extractUniformGame (RawCtxSelectedParentSecrecy.joint priorSample address)
          (fullExtractReduction hmac .ratchet
            (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates))) +
        (hmacPrfRealGame hmac (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address)
          (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates))).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address)
          (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates)))) := by
  simpa only [bytes_same] using RawCtxFullPreimageTester.source_alias_bound source hmac correct
    (sample priorSample address) observe candidates

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.real_bound_vcvioLegacy :
    ∀ {Context Result : Type} (source : BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : BeaconcryptCore.Computational.PqxdhSecretInputKdf.HmacSha512) (correct : BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.SourceFullCorrect source hmac) (priorSample : ProbComp Context) (address : Context → BeaconcryptCore.Computational.PqxdhJointKdf.JointKdfAddress) (observe : Context × BeaconcryptCore.Computational.RawCtxSelectedParentEntry.Entry → BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.FullOutput → ProbComp Result) (candidates : Result → List BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput), (probEvent (BeaconcryptCore.Computational.RawCtxFullPreimageTester.actual (BeaconcryptCore.Computational.RawCtxFullPreimageTester.production source) (BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.sample priorSample address) observe) fun (pair : BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput × Result) => pair.1 ∈ candidates pair.2) ≤ (2 ^ 352)⁻¹ + ENNReal.ofReal ((BeaconcryptCore.Computational.PqxdhSecretInputKdf.extractRealGame hmac (BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint priorSample address) (BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullExtractReduction hmac BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfDomain.ratchet (BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester (BeaconcryptCore.Computational.RawCtxFullPreimageTester.production source) observe candidates))).boolDistAdvantage (BeaconcryptCore.Computational.PqxdhSecretInputKdf.extractUniformGame (BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint priorSample address) (BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullExtractReduction hmac BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfDomain.ratchet (BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester (BeaconcryptCore.Computational.RawCtxFullPreimageTester.production source) observe candidates))) + (BeaconcryptCore.Computational.PqxdhSecretInputKdf.hmacPrfRealGame hmac (BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullExpandReduction BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfDomain.ratchet (BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint priorSample address) (BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester (BeaconcryptCore.Computational.RawCtxFullPreimageTester.production source) observe candidates))).boolDistAdvantage (BeaconcryptCore.Computational.PqxdhSecretInputKdf.hmacPrfRandomGame (BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullExpandReduction BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfDomain.ratchet (BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint priorSample address) (BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester (BeaconcryptCore.Computational.RawCtxFullPreimageTester.production source) observe candidates)))) :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.real_bound

noncomputable def uniform {Context Result : Type} (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → FullOutput → ProbComp Result) :=
  RawCtxSelectedParentSampler.original priorSample address (fun context => do
    let child ← $ᵗ FullOutput
    observe context child)

set_option maxRecDepth 2048 in
/-- With an independent child, the original full predecessor's omitted coordinate can be delayed past the entire adaptive candidate computation. -/
theorem uniform_bound {Context Result : Type} (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → FullOutput → ProbComp Result)
    (candidates : Result → List RootOutput) (budget : Nat)
    (bounded : ∀ context output result, result ∈ support (observe context output) →
      (candidates result).length ≤ budget) :
    Pr{let pair ← uniform priorSample address observe}[pair.1 ∈ candidates pair.2] ≤
      (budget : ENNReal) / (2 ^ 256 : ENNReal) := by
  apply RawCtxSelectedParentSecrecy.candidate_bound
  intro context result supported
  simp only [mem_support_bind_iff] at supported
  exact supported.elim fun output proof => bounded context output result proof.2

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.uniform_bound_vcvioLegacy :
    ∀ {Context Result : Type} (priorSample : ProbComp Context) (address : Context → BeaconcryptCore.Computational.PqxdhJointKdf.JointKdfAddress) (observe : Context × BeaconcryptCore.Computational.RawCtxSelectedParentEntry.Entry → BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.FullOutput → ProbComp Result) (candidates : Result → List BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput) (budget : ℕ) (bounded : ∀ (context : Context × BeaconcryptCore.Computational.RawCtxSelectedParentEntry.Entry) (output : BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.FullOutput), ∀ result ∈ MonadAttach.support (observe context output), (candidates result).length ≤ budget), (probEvent (BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.uniform priorSample address observe) fun (pair : BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput × Result) => pair.1 ∈ candidates pair.2) ≤ ↑budget / 2 ^ 256 :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.uniform_bound

/-- The additional tester pays two HMAC challenge queries, all original predecessor/observer uniform calls and its actual candidate evaluations of the real public function. -/
theorem tester_queries {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (priorSample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : Context × Entry → FullOutput → ProbComp Result) (candidates : Result → List RootOutput)
    (qSample qObserve qCandidates : Nat) (sampleBound : priorSample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve)
    (candidateBound : ∀ context output result, result ∈ support (observe context output) →
      (candidates result).length ≤ qCandidates) :
    (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address)
      (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates)).IsQueryBoundP
      IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address)
      (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates)).IsQueryBoundP
      PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 76) + qObserve) ∧
    (∀ context output result, result ∈ support (observe context output) →
      (RawCtxFullPreimageTester.evaluate output (candidates result)).IsTotalQueryBound qCandidates) := by
  exact ⟨(RawCtxSelectedParentSecrecy.reduction_bounds priorSample address _ qSample qObserve
      sampleBound (RawCtxFullPreimageTester.tester_uniform _ _ _ observeBound)).1,
    (RawCtxSelectedParentSecrecy.reduction_bounds priorSample address _ qSample qObserve
      sampleBound (RawCtxFullPreimageTester.tester_uniform _ _ _ observeBound)).2,
    RawCtxFullPreimageTester.tester_evaluation_bound observe candidates candidateBound⟩

end BeaconcryptCore.Computational.RawCtxSelectedParentCandidates

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.bytes_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.bytes_same
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.real_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.uniform_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.tester_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentCandidates.tester_queries
