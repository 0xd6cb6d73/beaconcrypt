-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWeightedRecordSecurity
import BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource

/-! The selected winning and selector observers are averaged over the same actual prior. Different targets retain different ideal games and separate observer-specific loss expectations. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity

theorem average {A : Type} (prior : ProbComp A) (win select : A → ProbComp Bool)
    (epsilon : ℝ≥0∞) (winLoss selectLoss : A → ℝ≥0∞)
    (pointwise : ∀ context ∈ support prior, 𝒟[win context] {true} ≤
      epsilon * 𝒟[select context] {true} + winLoss context + epsilon * selectLoss context) :
    𝒟[prior >>= win] {true} ≤ epsilon * 𝒟[prior >>= select] {true} +
      (∑' context, Pr{let sampled ← prior}[sampled = context] * winLoss context) +
      epsilon * (∑' context, Pr{let sampled ← prior}[sampled = context] * selectLoss context) := by
  simp only [← prEvent_eq_evalDist_singleton _ true] at pointwise ⊢
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  have scale (function : A → ℝ≥0∞) :
      (∑' context, Pr{let sampled ← prior}[sampled = context] * (epsilon * function context)) =
        epsilon * (∑' context, Pr{let sampled ← prior}[sampled = context] * function context) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun context => by ac_rfl
  calc
    _ ≤ ∑' context, Pr{let sampled ← prior}[sampled = context] *
        (epsilon * Pr{let won ← select context}[won = true] + winLoss context + epsilon * selectLoss context) :=
      ENNReal.tsum_le_tsum fun context => by
        by_cases supported : context ∈ support prior
        · exact mul_le_mul' le_rfl (pointwise context supported)
        · simp only [prEvent_eq_zero_of_not_mem_support _ supported, zero_mul, le_refl]
    _ = _ := by simp only [mul_add, ENNReal.tsum_add, scale]

open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeCanonicalSelector (Target selected)
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context prior provider)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget) (target : Target budget)
  (claim : Value → Option (Nat × Pqxdh.Bytes))
local notation "targetSelect" => (fun result : Value × RegistrationNativeLedger.State =>
  selected setup.source.crypto wire serverKeyId budget claim target (Prod.fst result) (Prod.snd result))
local notation "worldCount" => (budget.cap 4 + budget.cap 5)
local notation "fixedGame" => (fun context : Context KemSK => RegistrationNativeG3MaterializedTracedStartup.fullGame
  (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
  (Context.seed context) (Context.scalar context) (Context.candidate context)
  (provider setup (Fin.val (Prod.snd target)) context) none (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) bounds PqxdhDeploymentInterface.Mode.P adversary)

noncomputable def fixedWin (context : Context KemSK) : ProbComp Bool :=
  (fun outcome => @decide (RegistrationNativeSelectiveRecordTraceTarget.Hit setup context.seed context.scalar context.candidate claim outcome ∧
    RegistrationNativeSelectedRecordTrace.outcomeSelected targetSelect outcome = true) (Classical.propDecidable _)) <$> fixedGame context

noncomputable def fixedSelector (context : Context KemSK) : ProbComp Bool :=
  RegistrationNativeSelectedRecordTrace.outcomeSelected targetSelect <$> fixedGame context

variable (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)

noncomputable def fixedDelta (winning : Bool) (context : Context KemSK) : ℝ≥0∞ :=
  Pr{let marked ← (RegistrationNativeG3MaterializedStartup.audit (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds .P adversary)}[marked = true] +
  RegistrationNativeWeightedRecordSecurity.recordLoss (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds adversary budget
    allowance constructorCoins mlCoins hmac fallback
    (fun view => match winning with
      | true => RegistrationNativeWeightedRecordView.winning setup.source.crypto wire serverKeyId budget claim target view
      | false => RegistrationNativeWeightedRecordView.selection setup.source.crypto wire serverKeyId budget claim target view)

noncomputable def delta (winning : Bool) : ℝ≥0∞ :=
  ∑' context, Pr{let sampled ← prior setup budget target.2}[sampled = context] *
    fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
      allowance constructorCoins mlCoins hmac fallback winning context

theorem outcome_selection (select : Value × RegistrationNativeLedger.State → Bool)
    (outcome : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value) :
    RegistrationNativeObservableUniformSource.outcomeDecision select outcome =
      RegistrationNativeSelectedRecordTrace.outcomeSelected select outcome := by
  cases outcome <;> rfl

set_option maxHeartbeats 1200000 in
theorem fixed_bound (context : Context KemSK)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
      context.seed context.scalar context.candidate (provider setup target.2.val context) target.2.val target.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac) :
    𝒟[fixedWin setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim context] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[fixedSelector setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim context] {true} +
      fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback true context +
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback false context := by
  have result := RegistrationNativeWeightedRecordSecurity.bound (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds claim adversary budget target
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct
  simpa only [fixedWin, fixedSelector, fixedDelta,
    ← prEvent_eq_evalDist_singleton _ true, prEvent_map, Bool.and_eq_true,
    RegistrationNativeSelectiveRecordTraceTarget.event, decide_eq_true_eq] using result

set_option maxHeartbeats 1200000 in
theorem bound
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : ∀ context ∈ support (prior setup budget target.2), RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
      context.seed context.scalar context.candidate (provider setup target.2.val context) target.2.val target.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac) :
    𝒟[RegistrationNativeObservablePriorSource.selectedHit setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target claim targetSelect] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target.2 target.1.val targetSelect] {true} +
      delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback true +
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback false := by
  have averaged := average (prior setup budget target.2)
    (fixedWin setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)
    (fixedSelector setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)
    (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹)
    (fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback true)
    (fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback false)
    (fun context supported => fixed_bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
      allowance constructorCoins mlCoins hmac fallback context bounded (framed context supported) constructorBound mlBound correct)
  have winEq : (prior setup budget target.2 >>= fixedWin setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim) =
      RegistrationNativeObservablePriorSource.selectedHit setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target claim targetSelect := rfl
  have selectEq : (prior setup budget target.2 >>= fixedSelector setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim) =
      RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target.2 target.1.val targetSelect := by
    unfold RegistrationNativeObservablePriorSource.full
    apply bind_congr
    intro context
    unfold fixedSelector
    congr 1
  rw [winEq, selectEq] at averaged
  exact averaged

end BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.average' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.average

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.outcome_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.outcome_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.fixed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity.bound
