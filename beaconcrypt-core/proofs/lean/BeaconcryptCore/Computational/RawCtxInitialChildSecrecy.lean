import BeaconcryptCore.Computational.RawCtxInitialSecrecy
import BeaconcryptCore.Computational.RawCtxFullPreimageTester

/-!
The first evolving derivation in either direction consumes the selected half of one actual uniform 64-byte initializer. Its exact joint sampler retains the complete prior context and the other directional half. The child is the full 76-byte source output; no extra initial nonce is sampled. These component laws must be consumed by the actual initializer and family continuation, including retained initializer aliases and source freshness.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitialChildSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- False selects Server-send/Beacon-receive; true selects Beacon-send/Server-receive. The retained half is returned first. -/
def parts (second : Bool) (output : HmacBlock) : RootOutput × RootOutput :=
  if second then (PqxdhSecretInputKdf.first32 output, RawCtxSelectedInitialSampler.initialOther output)
  else (RawCtxSelectedInitialSampler.initialOther output, PqxdhSecretInputKdf.first32 output)

/-- Both orientations split the same actual initializer draw through an arbitrary complete continuation. -/
theorem parts_observed {Result : Type} (second : Bool) (next : RootOutput → RootOutput → ProbComp Result) :
    EvalDistEq
      (do let output ← $ᵗ HmacBlock
          next (parts second output).1 (parts second output).2)
        (do let other ← $ᵗ RootOutput
            let target ← $ᵗ RootOutput
            next other target) := by
  cases second
  all_goals simp only [parts, Bool.false_eq_true, ite_false, ite_true]
  case false => exact RawCtxSelectedInitialSampler.initial_observed next
  case true => exact RawCtxSelectedInitialSecond.second_observed next

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.parts_observed_vcvioLegacy :
    ∀ {Result : Type} (second : Bool) (next : BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput → BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput → ProbComp Result),
      𝒮[do
          let output ← $ᵗ BeaconcryptCore.Computational.PqxdhSecretInputKdf.HmacBlock
          next (BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.parts second output).1 (BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.parts second output).2] =
        𝒮[do
          let other ← $ᵗ BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput
          let target ← $ᵗ BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput
          next other target] :=
  by simpa only [BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] using @BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.parts_observed

noncomputable def sample {Context : Type} (prior : ProbComp Context) (second : Context → Bool) :
    ProbComp ((Context × RootOutput) × RootOutput) := do
  let context ← prior
  let output ← $ᵗ HmacBlock
  pure ((context, (parts (second context) output).1), (parts (second context) output).2)

noncomputable def joint {Context : Type} (prior : ProbComp Context) (second : Context → Bool) :
    ProbComp ((Context × RootOutput) × Pqxdh.Bytes) := RawCtxFullPreimageTester.byteSampler (sample prior second)

noncomputable def separated {Context : Type} (prior : ProbComp Context) :
    ProbComp ((Context × RootOutput) × Pqxdh.Bytes) := do
  let context ← prior
  let other ← $ᵗ RootOutput
  let target ← $ᵗ RootOutput
  pure ((context, other), target.toList)

/-- The exact selected half is uniform independently of the complete prior context and retained opposite half, including adaptive direction selection before the initializer draw. -/
theorem joint_separated {Context : Type} (prior : ProbComp Context) (second : Context → Bool) :
    EvalDistEq (joint prior second) (separated prior) := by
  simpa only [joint, RawCtxFullPreimageTester.byteSampler, sample, separated, map_bind, map_pure] using
    EvalDistEq.bind_right prior (fun context => parts_observed (second context)
      (fun other target => pure ((context, other), target.toList)))

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.joint_separated_vcvioLegacy :
    ∀ {Context : Type} (prior : ProbComp Context) (second : Context → Bool), 𝒮[BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.joint prior second] = 𝒮[BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.separated prior] :=
  by simpa only [BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] using @BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.joint_separated

noncomputable def actual {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (prior : ProbComp Context) (second : Context → Bool) (observe : FullObserver (Context × RootOutput)) : ProbComp Bool := do
  let context ← prior
  let initial ← $ᵗ HmacBlock
  observe (context, (parts (second context) initial).1)
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address (parts (second context) initial).2.toList))

noncomputable def random {Context : Type} (prior : ProbComp Context) (second : Context → Bool)
    (observe : FullObserver (Context × RootOutput)) : ProbComp Bool :=
  independentFullGame (joint prior second) observe

/-- The initial-half child game supplies the exact serialized source input, other half and full original continuation to the ordinary secret-input endpoint. -/
theorem actual_source {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (prior : ProbComp Context) (second : Context → Bool) (observe : FullObserver (Context × RootOutput)) :
    actual source prior second observe = sourceFullGame source .ratchet (joint prior second) observe := by
  simp only [actual, sourceFullGame, joint, RawCtxFullPreimageTester.byteSampler, sample,
    bind_map_left, bind_assoc, pure_bind]

/-- Each first directional derivation has coefficient-one fixed-salt Extract and ordinary two-query HMAC reductions at this exact initial-half joint sampler. -/
theorem primitive_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (prior : ProbComp Context) (second : Context → Bool) (observe : FullObserver (Context × RootOutput)) :
    (actual source prior second observe).boolDistAdvantage (random prior second observe) ≤
      (extractRealGame hmac (joint prior second) (fullExtractReduction hmac .ratchet observe)).boolDistAdvantage
        (extractUniformGame (joint prior second) (fullExtractReduction hmac .ratchet observe)) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (joint prior second) observe)).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction .ratchet (joint prior second) observe)) := by
  simpa only [actual_source, random] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet (joint prior second) observe

set_option maxRecDepth 2048 in
/-- The source sampler pays the complete prior context and exactly one 64-byte initializer draw, without a distribution-based cost transfer. -/
theorem sample_bound {Context : Type} (prior : ProbComp Context) (second : Context → Bool)
    (budget : Nat) (bounded : prior.IsTotalQueryBound budget) :
    (sample prior second).IsTotalQueryBound (budget + 64) := by
  exact isTotalQueryBound_bind bounded fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) fun output =>
      show (pure ((context, (parts (second context) output).1), (parts (second context) output).2) :
        ProbComp ((Context × RootOutput) × RootOutput)).IsTotalQueryBound 0 from trivial

/-- Serializing the selected half keeps the complete original initializer sampling budget. -/
theorem joint_bound {Context : Type} (prior : ProbComp Context) (second : Context → Bool)
    (budget : Nat) (bounded : prior.IsTotalQueryBound budget) :
    (joint prior second).IsTotalQueryBound (budget + 64) :=
  RawCtxFullPreimageTester.byteSampler_uniform _ (sample_bound prior second budget bounded)

/-- The ordinary HMAC reduction uses two challenge calls and includes all prior, actual initializer and complete observer sampling. -/
theorem reduction_queries {Context : Type} (prior : ProbComp Context) (second : Context → Bool)
    (observe : FullObserver (Context × RootOutput)) (qPrior qObserve : Nat)
    (priorBound : prior.IsTotalQueryBound qPrior)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (fullExpandReduction .ratchet (joint prior second) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
      (fullExpandReduction .ratchet (joint prior second) observe).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qPrior + 64) + qObserve) := by
  exact ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ (joint_bound prior second qPrior priorBound) observeBound⟩

set_option maxRecDepth 2048 in
/-- All source and challenger worlds count the original 64-byte initializer and their respective Extract, HMAC or independent 76-byte child draws. -/
theorem execution_queries {Context : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (prior : ProbComp Context) (second : Context → Bool) (observe : FullObserver (Context × RootOutput))
    (qPrior qObserve : Nat) (priorBound : prior.IsTotalQueryBound qPrior)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    let qSample := qPrior + 64
    (actual source prior second observe).IsTotalQueryBound (qSample + qObserve) ∧
      (extractRealGame hmac (joint prior second) (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound (qSample + qObserve) ∧
      (extractUniformGame (joint prior second) (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound (qSample + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (joint prior second) observe)).IsTotalQueryBound (64 + (qSample + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet (joint prior second) observe)).IsTotalQueryBound (qSample + (64 + (64 + qObserve))) ∧
      (random prior second observe).IsTotalQueryBound (qSample + (76 + qObserve)) := by
  refine ⟨?_, isTotalQueryBound_bind (joint_bound prior second qPrior priorBound) (fun pair => observeBound pair.1 _),
    fullExtractUniform_uniform_query_bound hmac .ratchet _ _ (joint_bound prior second qPrior priorBound) observeBound,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ (joint_bound prior second qPrior priorBound) observeBound,
    fullHmacRandom_uniform_query_bound .ratchet _ _ (joint_bound prior second qPrior priorBound) observeBound,
    independentFullGame_uniform_query_bound _ _ (joint_bound prior second qPrior priorBound) observeBound⟩
  simpa only [actual_source] using sourceFullGame_uniform_query_bound source .ratchet _ _
    (joint_bound prior second qPrior priorBound) observeBound

end BeaconcryptCore.Computational.RawCtxInitialChildSecrecy
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.parts_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.parts_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.joint_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.joint_separated

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.actual_source

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.primitive_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.sample_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.sample_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.joint_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.joint_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.reduction_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.execution_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialChildSecrecy.execution_queries
