-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorRecordFixed
import BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity

/-! Both original LR observer directions are averaged over the actual shared startup prior. Every admitted test's selected-source provenance is supplied by the supported prior and actual source theorem; the winning and eligibility losses remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity

theorem average_lower {A : Type} (prior : ProbComp A) (win select : A → ProbComp Bool)
    (epsilon : ℝ≥0∞) (winLoss selectLoss : A → ℝ≥0∞)
    (pointwise : ∀ context ∈ support prior, epsilon * 𝒟[select context] {true} ≤
      𝒟[win context] {true} + winLoss context + epsilon * selectLoss context) :
    epsilon * 𝒟[prior >>= select] {true} ≤ 𝒟[prior >>= win] {true} +
      (∑' context, Pr{let sampled ← prior}[sampled = context] * winLoss context) +
      epsilon * (∑' context, Pr{let sampled ← prior}[sampled = context] * selectLoss context) := by
  simp only [← prEvent_eq_evalDist_singleton _ true] at pointwise ⊢
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  have scale (function : A → ℝ≥0∞) :
      (∑' context, Pr{let sampled ← prior}[sampled = context] * (epsilon * function context)) =
        epsilon * (∑' context, Pr{let sampled ← prior}[sampled = context] * function context) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun context => by ac_rfl
  rw [← scale]
  calc
    _ ≤ ∑' context, Pr{let sampled ← prior}[sampled = context] *
        (Pr{let won ← win context}[won = true] + winLoss context + epsilon * selectLoss context) :=
      ENNReal.tsum_le_tsum fun context => by
        by_cases supported : context ∈ support prior
        · exact mul_le_mul' le_rfl (pointwise context supported)
        · simp only [prEvent_eq_zero_of_not_mem_support _ supported, zero_mul, le_refl]
    _ = _ := by simp only [mul_add, ENNReal.tsum_add, scale]

open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context prior provider)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity)
  (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
local notation "worldCount" => budget.cap 4 + budget.cap 5
attribute [local irreducible] RegistrationNativeG3MaterializedTracedStartup.fullGame
  RegistrationNativeG3MaterializedStartup.audit RegistrationNativeWeightedRecordSecurity.recordLoss
  RegistrationNativeSecretWordKemEarly.actual RegistrationNativeLorRecordSecurity.observer
local notation "sourceObserve" => RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target

noncomputable def fixedFull (winning : Bool) (context : Context KemSK) : ProbComp Bool :=
  RegistrationNativeLorRecordFixed.full (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds adversary budget target filter guess winning

variable (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)

noncomputable def fixedDelta (winning : Bool) (context : Context KemSK) : ℝ≥0∞ :=
  RegistrationNativeLorRecordFixed.delta (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback winning

noncomputable def delta (winning : Bool) : ℝ≥0∞ :=
  ∑' context, Pr{let sampled ← prior setup budget target.2}[sampled = context] *
    fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess
      allowance constructorCoins mlCoins hmac fallback winning context

set_option maxHeartbeats 1200000 in
theorem fixed_bound (context : Context KemSK) (supported : context ∈ support (prior setup budget target.2))
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
      context.seed context.scalar context.candidate (provider setup target.2.val context) target.2.val target.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire) :
    (𝒟[fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess true context] {true} ≤
      2⁻¹ * 𝒟[fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess false context] {true} +
      fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true context +
      2⁻¹ * fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false context) ∧
    (2⁻¹ * 𝒟[fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess false context] {true} ≤
      𝒟[fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess true context] {true} +
      fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true context +
      2⁻¹ * fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false context) := by
  have recorded := RegistrationNativeLorRecordFixed.bound (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct
  obtain ⟨reserved, chosen, chosenAt, publicKey⟩ := RegistrationNativeG3NativeTargetUniform.prior_selected setup budget target.2 context supported
  have provenance (winning : Bool) := RegistrationNativeLorRecordSecurity.full_hit setup checks wire route source ensureInit identityIndex serverKeyId
    context.seed context.scalar context.profile.pairs chosen context.profile.challenge context.candidate bounds adversary budget target filter guess
    bounded reserved chosenAt readback responseReadback winning
  simp only [RegistrationNativeLorRecordSecurity.full, publicKey] at provenance
  have attached (winning : Bool) :
      𝒟[fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess winning context] {true} ≤
      𝒟[RegistrationNativeLorRecordFixed.hitFull (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
        context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds adversary budget target filter guess winning] {true} := by
    simpa only [fixedFull, RegistrationNativeLorRecordFixed.full,
      RegistrationNativeLorRecordFixed.hitFull, provider] using provenance winning
  constructor
  · exact (attached true).trans recorded.1
  · exact (mul_le_mul' (le_refl (2⁻¹ : ℝ≥0∞)) (attached false)).trans recorded.2

set_option maxHeartbeats 1200000 in
theorem bound
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : ∀ context ∈ support (prior setup budget target.2), RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
      context.seed context.scalar context.candidate (provider setup target.2.val context) target.2.val target.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire) :
    (𝒟[RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target.2 target.1.val (sourceObserve true)] {true} ≤
      2⁻¹ * 𝒟[RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target.2 target.1.val (sourceObserve false)] {true} +
      delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true +
      2⁻¹ * delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false) ∧
    (2⁻¹ * 𝒟[RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target.2 target.1.val (sourceObserve false)] {true} ≤
      𝒟[RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target.2 target.1.val (sourceObserve true)] {true} +
      delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true +
      2⁻¹ * delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false) := by
  have pointwise := fun context supported => fixed_bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback context supported bounded (framed context supported) constructorBound mlBound correct readback responseReadback
  have forward := RegistrationNativeWeightedPriorSecurity.average (prior setup budget target.2)
    (fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess true)
    (fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess false) (2⁻¹)
    (fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true)
    (fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false)
    (fun context supported => (pointwise context supported).1)
  have backward := average_lower (prior setup budget target.2)
    (fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess true)
    (fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess false) (2⁻¹)
    (fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true)
    (fixedDelta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false)
    (fun context supported => (pointwise context supported).2)
  have fullEq (winning : Bool) : (prior setup budget target.2 >>= fixedFull setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess winning) =
      RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary budget target.2 target.1.val (sourceObserve winning) := by
    unfold RegistrationNativeObservablePriorSource.full
    apply bind_congr
    intro context
    unfold fixedFull RegistrationNativeLorRecordFixed.full
    congr 1
  simpa only [fullEq, delta] using And.intro forward backward

end BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity.average_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity.average_lower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity.fixed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity.bound
