import BeaconcryptCore.Computational.RawCtxInitialChildSecrecy
import BeaconcryptCore.Computational.RawCtxSelectedInputCandidates

/-!
The first child in either direction uses the exact selected half of one64-byte initializer. Real-child input guesses pay a separately constructed full76-output tester with its Extract/HMAC and finite-image terms. Only the independent-child comparison delays the hidden32-byte half past the complete adaptive candidate computation. No initial nonce or extra12-byte source draw is introduced; public HKDF stays real in the observer and tester.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitialChildCandidates
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxInitialChildSecrecy

/-- Real first-child input recovery pays an explicit full-output tester on the same actual64-byte joint sampler; no uniform guessing premise is used. -/
theorem real_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (prior : ProbComp Context) (second : Context → Bool)
    (observe : Context × RootOutput → FullOutput → ProbComp Result) (candidates : Result → List RootOutput) :
    Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
        (sample prior second) observe)}[pair.1 ∈ candidates pair.2] ≤
      (2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
        (extractRealGame hmac (joint prior second)
          (fullExtractReduction hmac .ratchet
            (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates))).boolDistAdvantage
        (extractUniformGame (joint prior second)
          (fullExtractReduction hmac .ratchet
            (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates))) +
        (hmacPrfRealGame hmac (fullExpandReduction .ratchet (joint prior second)
          (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates))).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction .ratchet (joint prior second)
          (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates)))) :=
  RawCtxFullPreimageTester.source_alias_bound source hmac correct (sample prior second) observe candidates

noncomputable def uniform {Context Result : Type} (prior : ProbComp Context) (second : Context → Bool)
    (observe : Context × RootOutput → FullOutput → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let pair ← sample prior second
  let child ← $ᵗ FullOutput
  let result ← observe pair.1 child
  pure (pair.2, result)

noncomputable def delayed {Context Result : Type} (prior : ProbComp Context)
    (observe : Context × RootOutput → FullOutput → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let context ← prior
  let other ← $ᵗ RootOutput
  let child ← $ᵗ FullOutput
  let result ← observe (context, other) child
  let target ← $ᵗ RootOutput
  pure (target, result)

/-- Either selected initial half can be delayed past the complete independent-child candidate computation while preserving all retained context and results. -/
theorem uniform_delayed {Context Result : Type} (prior : ProbComp Context) (second : Context → Bool)
    (observe : Context × RootOutput → FullOutput → ProbComp Result) :
    EvalDistEq (uniform prior second observe) (delayed prior observe) := by
  simp only [uniform, delayed, sample, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right prior (fun context => ?_)
  refine (parts_observed (second context) (fun other target => do
    let child ← $ᵗ FullOutput
    let result ← observe (context, other) child
    pure (target, result))).trans ?_
  exact EvalDistEq.bind_right ($ᵗ RootOutput) (fun other => by
    simpa only [bind_assoc] using evalSPMF_sample_comm ($ᵗ RootOutput)
      (do let child ← $ᵗ FullOutput; observe (context, other) child)
      (fun target result => pure (target, result)))

/-- The exact independent first-child experiment charges the complete adaptive candidate list once against the delayed32-byte half, with no direction or stopping factor. -/
theorem uniform_bound {Context Result : Type} (prior : ProbComp Context) (second : Context → Bool)
    (observe : Context × RootOutput → FullOutput → ProbComp Result) (candidates : Result → List RootOutput)
    (budget : Nat) (bounded : ∀ context output result, result ∈ support (observe context output) →
      (candidates result).length ≤ budget) :
    Pr{let pair ← uniform prior second observe}[pair.1 ∈ candidates pair.2] ≤
      (budget : ENNReal) / (2 ^ 256 : ENNReal) := by
  have same := (uniform_delayed prior second observe).prEvent_eq
    (fun pair : RootOutput × Result => pair.1 ∈ candidates pair.2)
  rw [same, delayed]
  refine prEvent_bind_le_of_forall_le _ _ _ (fun context => ?_)
  refine prEvent_bind_le_of_forall_le _ _ _ (fun other => ?_)
  refine prEvent_bind_le_of_forall_le _ _ _ (fun child => ?_)
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ (fun result reached => ?_)
  rw [bind_pure_comp _ ($ᵗ RootOutput), prEvent_map]
  exact (RawCtxSelectedInputCandidates.uniform_candidates (candidates result)).trans
    (ENNReal.div_le_div_right (by exact_mod_cast bounded (context, other) child result reached) _)

/-- The real-input tester uses the same actual64-byte sampler, two HMAC challenges, every observer coin and at most one complete real HKDF evaluation per candidate. -/
theorem tester_queries {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (prior : ProbComp Context) (second : Context → Bool)
    (observe : Context × RootOutput → FullOutput → ProbComp Result) (candidates : Result → List RootOutput)
    (qSample qObserve qCandidates : Nat) (sampleBound : prior.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve)
    (candidateBound : ∀ context output result, result ∈ support (observe context output) →
      (candidates result).length ≤ qCandidates) :
    (fullExpandReduction .ratchet (joint prior second)
      (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates)).IsQueryBoundP
      IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet (joint prior second)
      (RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source) observe candidates)).IsQueryBoundP
      PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 64) + qObserve) ∧
    (∀ context output result, result ∈ support (observe context output) →
      (RawCtxFullPreimageTester.evaluate output (candidates result)).IsTotalQueryBound qCandidates) := by
  exact ⟨(reduction_queries prior second _ qSample qObserve
      sampleBound (RawCtxFullPreimageTester.tester_uniform _ _ _ observeBound)).1,
    (reduction_queries prior second _ qSample qObserve
      sampleBound (RawCtxFullPreimageTester.tester_uniform _ _ _ observeBound)).2,
    RawCtxFullPreimageTester.tester_evaluation_bound observe candidates candidateBound⟩

set_option maxRecDepth 2048 in
/-- The original independent-child candidate experiment pays exactly the full prior sampler,64-byte initializer,76-byte child and complete adaptive observer budget. -/
theorem uniform_queries {Context Result : Type} (prior : ProbComp Context) (second : Context → Bool)
    (observe : Context × RootOutput → FullOutput → ProbComp Result) (qPrior qObserve : Nat)
    (priorBound : prior.IsTotalQueryBound qPrior)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (uniform prior second observe).IsTotalQueryBound ((qPrior + 64) + (76 + qObserve)) := by
  exact isTotalQueryBound_bind (sample_bound prior second qPrior priorBound) fun pair =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) fun output =>
      by simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        observeBound pair.1 output

end BeaconcryptCore.Computational.RawCtxInitialChildCandidates

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildCandidates.real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildCandidates.real_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildCandidates.uniform_delayed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildCandidates.uniform_delayed
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildCandidates.uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildCandidates.uniform_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildCandidates.tester_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildCandidates.tester_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildCandidates.uniform_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildCandidates.uniform_queries
