import BeaconcryptCore.Computational.VCVioForwardEvalDist
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.EvalDist.MeasureSpec
import VCVio.OracleComp.Support
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import ToMathlib.Probability.UniformOn

/-!
# Forward shim: event laws of oracle computations (VCVio pin 98dc1089)

Upstream VCVio (afa6593f) states the laws of oracle computations in the event and measure vocabulary: events after a bind are weighted sums of singleton masses (`OracleComp.prEvent_bind_eq_tsum`), oracle computations are lossless (`OracleComp.prEvent_true_eq_one`), support-restricted comparisons survive a common draw, and uniform samples have counting laws. The pin lacks these laws, so the project's proofs reach them through the deprecated façade (`probOutput_bind_eq_tsum`, `probFailure_of_liftM_PMF`, …). This module backports them under the upstream names and statements.

Pin adjustments, each documented at its declaration: upstream's single binder `[OracleSpec.AnswerMeasure spec]` (answer measures on the discrete structure) is the pin's `[∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]`, and `[OracleSpec.UniformAnswerMeasure spec]` is `[OracleSpec.IsUniformMeasureSpec spec]` with the same two measurable-space binders; laws stated upstream for the head constant `prEvent` are stated for `𝒟[·] {True}`. `SampleableType.prEvent_uniformSample` is not restated: the pin module `VCVio.OracleComp.Constructions.SampleableType.NativeMeasure` already has it with the upstream statement and is imported. The proofs are pin-specific and are discarded at the VCVio upgrade. Nothing here is assumed.
-/

open MeasureTheory ProbabilityTheory OracleComp OracleSpec
open scoped ENNReal

set_option autoImplicit false

universe u

/-! ## Integrals against measures concentrated on countable sets (upstream `ToMathlib.MeasureTheory.Integral.Countable`) -/

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {μ : Measure X}
  {s : Set X}

/-- Integrals against a measure concentrated on a countable set are sums over that set. -/
theorem lintegral_eq_tsum_of_ae_mem_countable (hs : s.Countable) (h : ∀ᵐ x ∂μ, x ∈ s)
    (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂μ = ∑' x : s, f x * μ {(x : X)} := by
  rw [← lintegral_countable f hs, Measure.restrict_eq_self_of_ae_mem h]

/-- Integrals against a measure concentrated on a countable set are sums of the singleton masses times the integrand over the whole space. -/
theorem lintegral_eq_tsum_mul_of_ae_mem_countable (hs : s.Countable) (h : ∀ᵐ x ∂μ, x ∈ s)
    (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  rw [lintegral_eq_tsum_of_ae_mem_countable hs h f,
    ← tsum_subtype_eq_of_support_subset (s := s) (f := fun x ↦ μ {x} * f x)]
  · simp only [mul_comm]
  · intro x hx
    by_contra hxs
    refine hx ?_
    simp only
    rw [measure_mono_null (Set.singleton_subset_iff.2 hxs) (ae_iff.1 h), zero_mul]

end MeasureTheory

namespace OracleComp

/-! ## Events of oracle computations (upstream `OracleComp.EvalDist.Measure`) -/

section measureSpec

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [OracleSpec.IsMeasureSpec spec] {α : Type}

/-- Oracle computations with a measure interpretation are lossless. Upstream binder `[OracleSpec.AnswerMeasure spec]`. -/
theorem prEvent_true_eq_one (mx : OracleComp spec α) : Pr{let _ ← mx}[True] = 1 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ, evalDist_apply_univ_eq_one]

/-- The complement of an event has the remaining probability: oracle computations never fail. -/
theorem prEvent_not_eq_one_sub (mx : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← mx}[¬ p x] = 1 - Pr{let x ← mx}[p x] := by
  have h := prEvent_add_prEvent_not_eq_prEvent_true mx p
  rw [prEvent_true_eq_one] at h
  exact ENNReal.eq_sub_of_add_eq (prEvent_ne_top _) (by rw [add_comm]; exact h)

/-- A lossless prefix whose result is unused leaves the event unchanged. Upstream states it for `prEvent`, which is `𝒟[·] {True}`. -/
theorem prEvent_bind_const (mx : OracleComp spec α) (my : OracleComp spec Prop) :
    𝒟[mx >>= fun _ ↦ my] {True} = 𝒟[my] {True} := by
  rw [evalDist_bind_const]

/-- A lossless prefix whose result is unused is equal in distribution to its continuation. -/
theorem EvalDistEq.bind_const {β : Type} (mx : OracleComp spec α) (my : OracleComp spec β) :
    (mx >>= fun _ ↦ my) =ᵈ my :=
  _root_.EvalDistEq.of_forall_prEvent_eq fun p ↦ by
    rw [bind_assoc]
    exact prEvent_bind_const mx (my >>= fun y ↦ pure (p y))

/-- Discarding the result of a lossless computation leaves the constant. -/
theorem EvalDistEq.map_const {β : Type} (mx : OracleComp spec α) (c : β) :
    (fun _ ↦ c) <$> mx =ᵈ (pure c : OracleComp spec β) := by
  rw [map_eq_bind_pure_comp]
  exact EvalDistEq.bind_const mx (pure c)

/-- A property of every possible output holds almost surely. -/
theorem ae_evalDist_of_forall_mem_support [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : OracleComp spec α) {p : α → Prop} (h : ∀ x ∈ support mx, p x) :
    ∀ᵐ x ∂𝒟[mx], p x :=
  evalDist.ae_of_forall_mem_support mx p MeasurableSet.of_discrete h

/-- An event containing every possible output has probability one. -/
theorem prEvent_eq_one_of_forall_mem_support (mx : OracleComp spec α) (p : α → Prop)
    (h : ∀ x ∈ support mx, p x) : Pr{let x ← mx}[p x] = 1 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, ← MeasureTheory.ae_iff_prob_eq_one Measurable.of_discrete]
  exact evalDist.ae_of_forall_mem_support mx p MeasurableSet.of_discrete h

/-- Comparing the events of continuations on every possible output compares the composed events. Upstream states it for `prEvent`, which is `𝒟[·] {True}`. -/
theorem prEvent_bind_mono_of_support (mx : OracleComp spec α) (f g : α → OracleComp spec Prop)
    (h : ∀ a ∈ support mx, 𝒟[f a] {True} ≤ 𝒟[g a] {True}) :
    𝒟[mx >>= f] {True} ≤ 𝒟[mx >>= g] {True} :=
  evalDist_bind_apply_mono_of_support mx f g (measurableSet_singleton True) h

/-- Continuation events with equal probability on every possible output give equal composed event probabilities. Upstream states it for `prEvent`, which is `𝒟[·] {True}`. -/
theorem prEvent_bind_congr_of_support (mx : OracleComp spec α) (f g : α → OracleComp spec Prop)
    (h : ∀ a ∈ support mx, 𝒟[f a] {True} = 𝒟[g a] {True}) :
    𝒟[mx >>= f] {True} = 𝒟[mx >>= g] {True} :=
  le_antisymm (prEvent_bind_mono_of_support mx f g fun a ha ↦ (h a ha).le)
    (prEvent_bind_mono_of_support mx g f fun a ha ↦ (h a ha).ge)

/-- Continuations equal in distribution on every possible output of a common draw give binds equal in distribution. -/
theorem EvalDistEq.bind_congr_of_support {β : Type} (mx : OracleComp spec α)
    {f g : α → OracleComp spec β} (h : ∀ a ∈ support mx, f a =ᵈ g a) : mx >>= f =ᵈ mx >>= g :=
  _root_.EvalDistEq.of_forall_prEvent_eq fun p ↦ by
    rw [bind_assoc, bind_assoc]
    exact prEvent_bind_congr_of_support mx _ _ fun a ha ↦ (h a ha).prEvent_eq p

/-- The output measure is concentrated on the reachable outputs. -/
theorem evalDist_ae_mem_support [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (oa : OracleComp spec α) : ∀ᵐ x ∂𝒟[oa], x ∈ support oa :=
  evalDist.ae_of_forall_mem_support oa (· ∈ support oa) MeasurableSet.of_discrete fun _ h ↦ h

end measureSpec

/-! ## Output-mass sums (upstream `OracleComp.EvalDist.Sum`) -/

section sum

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [OracleSpec.IsMeasureSpec spec] {α β : Type} [∀ t, Finite (spec.Range t)]

/-- An integral against the output measure is the sum of the singleton masses times the integrand. -/
theorem lintegral_evalDist_eq_tsum [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (oa : OracleComp spec α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂𝒟[oa] = ∑' x, Pr{let y ← oa}[y = x] * f x := by
  let : spec.Fintype := { fintypeB := fun t ↦ Fintype.ofFinite (spec.Range t) }
  rw [lintegral_eq_tsum_mul_of_ae_mem_countable (support_finite oa).countable
    (evalDist_ae_mem_support oa)]
  refine tsum_congr fun x ↦ ?_
  rw [prEvent_eq_evalDist_singleton oa x]

/-- The singleton masses of an oracle computation sum to one. -/
theorem tsum_prEvent_eq_one (oa : OracleComp spec α) : ∑' x, Pr{let y ← oa}[y = x] = 1 := by
  let : MeasurableSpace α := ⊤
  have h := lintegral_evalDist_eq_tsum oa fun _ ↦ 1
  simp only [mul_one, lintegral_const, one_mul] at h
  rw [← h, ← prEvent_true_eq_evalDist_apply_univ, prEvent_true_eq_one]

/-- The singleton masses of an oracle computation sum to at most one. -/
theorem tsum_prEvent_le_one (oa : OracleComp spec α) : ∑' x, Pr{let y ← oa}[y = x] ≤ 1 :=
  (tsum_prEvent_eq_one oa).le

/-- An event after a bind is the weighted sum, over the prefix's outputs, of the continuation's event. The prefix's output type needs no countability. -/
theorem prEvent_bind_eq_tsum (oa : OracleComp spec α) (g : α → OracleComp spec β)
    (p : β → Prop) :
    Pr{let y ← oa >>= g}[p y] = ∑' x, Pr{let z ← oa}[z = x] * Pr{let y ← g x}[p y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, lintegral_evalDist_eq_tsum]

/-- An event is the sum of the singleton masses of the outputs satisfying it. -/
theorem prEvent_eq_tsum_ite (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr{let y ← oa}[p y] = ∑' x, if p x then Pr{let y ← oa}[y = x] else 0 := by
  have h := prEvent_bind_eq_tsum oa pure p
  rw [bind_pure] at h
  rw [h]
  refine tsum_congr fun x ↦ ?_
  rw [prEvent_pure]
  split_ifs <;> simp

end sum

/-! ## Commuting independent oracle computations (upstream `OracleComp.EvalDist.Measure`) -/

section swap

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]

private theorem evalDist_query_bind_bind_swap [OracleSpec.IsMeasureSpec spec]
    [∀ t, Countable (spec.Range t)] {β γ : Type} [MeasurableSpace γ]
    (t : spec.Domain) (my : OracleComp spec β) (f : spec.Range t → β → OracleComp spec γ) :
    𝒟[query t >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ query t >>= fun a ↦ f a b] := by
  induction my using OracleComp.inductionOn with
  | pure b => simp only [pure_bind]
  | query_bind s l ih =>
    simp only [bind_assoc]
    calc
      _ = 𝒟[query s >>= fun v ↦ query t >>= fun a ↦ l v >>= fun b ↦ f a b] :=
        _root_.evalDist_bind_bind_swap (query t) (query s)
          (fun a v ↦ l v >>= fun b ↦ f a b) Measurable.of_discrete
      _ = _ := evalDist_bind_congr_of_support (query s) _ _ fun v _ ↦ ih v

/-- Independent oracle computations commute before any measurably observed continuation. Only the query answers must be countable. Upstream binder `[OracleSpec.AnswerMeasure spec]`. -/
theorem evalDist_bind_bind_swap [OracleSpec.IsMeasureSpec spec] [∀ t, Countable (spec.Range t)]
    {α β γ : Type} [MeasurableSpace γ]
    (mx : OracleComp spec α) (my : OracleComp spec β) (f : α → β → OracleComp spec γ) :
    𝒟[mx >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ mx >>= fun a ↦ f a b] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp only [pure_bind]
  | query_bind t k ih =>
    simp only [bind_assoc]
    calc
      _ = 𝒟[query t >>= fun v ↦ my >>= fun b ↦ k v >>= fun a ↦ f a b] :=
        evalDist_bind_congr_of_support (query t) _ _ fun v _ ↦ ih v
      _ = _ := evalDist_query_bind_bind_swap t my (fun v b ↦ k v >>= fun a ↦ f a b)

/-- Independent oracle computations commute under a uniform oracle specification. Upstream binder `[OracleSpec.UniformAnswerMeasure spec]`. -/
theorem evalDist_bind_bind_swap_of_uniform [OracleSpec.IsUniformMeasureSpec spec]
    {α β γ : Type} [MeasurableSpace γ]
    (mx : OracleComp spec α) (my : OracleComp spec β) (f : α → β → OracleComp spec γ) :
    𝒟[mx >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ mx >>= fun a ↦ f a b] :=
  evalDist_bind_bind_swap mx my f

/-- Independent oracle computations commute in distribution under a uniform oracle specification. Upstream binder `[OracleSpec.UniformAnswerMeasure spec]`. -/
theorem EvalDistEq.bind_bind_swap [OracleSpec.IsUniformMeasureSpec spec] {α β γ : Type}
    (mx : OracleComp spec α) (my : OracleComp spec β) (f : α → β → OracleComp spec γ) :
    (mx >>= fun a ↦ my >>= fun b ↦ f a b) =ᵈ (my >>= fun b ↦ mx >>= fun a ↦ f a b) :=
  let : MeasurableSpace γ := ⊤
  _root_.EvalDistEq.of_evalDist_eq (evalDist_bind_bind_swap_of_uniform mx my f)

end swap

/-! ## Point masses determine oracle computations (upstream `OracleComp.EvalDist.Measure`) -/

section pointMasses

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [OracleSpec.IsMeasureSpec spec] {α : Type}

/-- Over finite oracle responses, computations with equal point masses are equal in distribution: both output measures are carried by the finite union of their supports. -/
theorem evalDistEq_of_forall_prEvent_eq_output [∀ t, Finite (spec.Range t)]
    {mx my : OracleComp spec α} (h : ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x]) :
    mx =ᵈ my := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  classical
  let : spec.Fintype := { fintypeB := fun t ↦ Fintype.ofFinite (spec.Range t) }
  let : MeasurableSpace α := ⊤
  let T : Finset α := ((support_finite mx).union (support_finite my)).toFinset
  have key : ∀ oz : OracleComp spec α, support oz ⊆ ↑T → ∀ s : Set α,
      𝒟[oz] s = ∑ x ∈ T.filter (· ∈ s), Pr{let z ← oz}[z = x] := by
    intro oz hsub s
    simp_rw [prEvent_eq_evalDist_singleton]
    rw [MeasureTheory.sum_measure_singleton]
    refine measure_congr ((evalDist.ae_of_forall_mem_support oz (· ∈ support oz)
      MeasurableSet.of_discrete fun _ ha => ha).mono fun a ha => ?_)
    have haT : a ∈ T := hsub ha
    change (a ∈ s) = (a ∈ (↑(T.filter (· ∈ s)) : Set α))
    simp [haT]
  ext s -
  rw [key mx (fun a ha => by simp [T, ha]) s, key my (fun a ha => by simp [T, ha]) s]
  exact Finset.sum_congr rfl fun x _ => h x

end pointMasses

/-! ## Uniform oracle specifications (upstream `OracleComp.EvalDist.Measure`) -/

section uniformAnswerMeasure

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [OracleSpec.IsUniformMeasureSpec spec] {α : Type}

/-- Under uniform oracle semantics, an event has probability one exactly when it holds on every possible output. Upstream binder `[OracleSpec.UniformAnswerMeasure spec]`. -/
theorem prEvent_eq_one_iff (mx : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 1 ↔ ∀ x ∈ support mx, p x := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  exact evalDist_apply_setOf_eq_one_iff_forall_mem_support mx p

/-- Under uniform oracle semantics, an event has probability zero exactly when it fails on every possible output. Upstream binder `[OracleSpec.UniformAnswerMeasure spec]`. -/
theorem prEvent_eq_zero_iff (mx : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 0 ↔ ∀ x ∈ support mx, ¬ p x := by
  let : MeasurableSpace α := ⊤
  refine ⟨fun h x hx hp ↦ ?_, prEvent_eq_zero_of_forall_mem_support mx p⟩
  rw [prEvent_eq_evalDist_of_discrete] at h
  have hpos : 0 < 𝒟[mx] {x} := (mem_support_iff_evalDist_singleton_pos mx x).mp hx
  have hle : 𝒟[mx] {x} ≤ 𝒟[mx] {y | p y} :=
    measure_mono (by rintro _ rfl; exact hp)
  exact (ne_of_gt (lt_of_lt_of_le hpos hle)) h

end uniformAnswerMeasure

end OracleComp

/-! ## Uniform samples (upstream `OracleComp.Constructions.SampleableType.Measure`) -/

namespace SampleableType

/-- Every singleton of a uniform finite sample has the reciprocal cardinality mass. -/
theorem evalDist_uniformSample_singleton {α : Type} [SampleableType α] [_root_.Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (x : α) :
    𝒟[($ᵗ α : ProbComp α)] {x} = (Fintype.card α : ENNReal)⁻¹ := by
  rw [evalDist_uniformSample, uniformOn_univ_apply_singleton]

/-- The probability of drawing one particular element uniformly. -/
theorem prEvent_uniformSample_eq_singleton {α : Type} [SampleableType α] [_root_.Fintype α]
    (a : α) : Pr{let x ← $ᵗ α}[x = a] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton, evalDist_uniformSample_singleton]

/-- A bijection of sample spaces carries a uniform sample to a uniform sample. -/
theorem map_uniformSample_evalDistEq_of_bijective {α β : Type} [SampleableType α]
    [SampleableType β] {f : α → β} (hf : Function.Bijective f) :
    f <$> ($ᵗ α : ProbComp α) =ᵈ ($ᵗ β : ProbComp β) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have h : 𝒟[f <$> ($ᵗ α : ProbComp α)] = 𝒟[($ᵗ β : ProbComp β)] := by
    rw [evalDist_map_of_discrete, evalDist_uniformSample, evalDist_uniformSample]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete hf
  exact EvalDistEq.of_evalDist_eq h

end SampleableType

/--
info: 'MeasureTheory.lintegral_eq_tsum_of_ae_mem_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.lintegral_eq_tsum_of_ae_mem_countable

/--
info: 'MeasureTheory.lintegral_eq_tsum_mul_of_ae_mem_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.lintegral_eq_tsum_mul_of_ae_mem_countable

/--
info: 'OracleComp.prEvent_true_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_true_eq_one

/--
info: 'OracleComp.prEvent_not_eq_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_not_eq_one_sub

/--
info: 'OracleComp.prEvent_bind_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_const

/--
info: 'OracleComp.EvalDistEq.bind_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.bind_const

/--
info: 'OracleComp.EvalDistEq.map_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.map_const

/--
info: 'OracleComp.ae_evalDist_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.ae_evalDist_of_forall_mem_support

/--
info: 'OracleComp.prEvent_eq_one_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_one_of_forall_mem_support

/--
info: 'OracleComp.prEvent_bind_mono_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_mono_of_support

/--
info: 'OracleComp.prEvent_bind_congr_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_congr_of_support

/--
info: 'OracleComp.EvalDistEq.bind_congr_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.bind_congr_of_support

/--
info: 'OracleComp.evalDist_ae_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDist_ae_mem_support

/--
info: 'OracleComp.lintegral_evalDist_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.lintegral_evalDist_eq_tsum

/--
info: 'OracleComp.tsum_prEvent_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.tsum_prEvent_eq_one

/--
info: 'OracleComp.tsum_prEvent_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.tsum_prEvent_le_one

/--
info: 'OracleComp.prEvent_bind_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_eq_tsum

/--
info: 'OracleComp.prEvent_eq_tsum_ite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_tsum_ite

/--
info: 'OracleComp.evalDist_bind_bind_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDist_bind_bind_swap

/--
info: 'OracleComp.evalDist_bind_bind_swap_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDist_bind_bind_swap_of_uniform

/--
info: 'OracleComp.EvalDistEq.bind_bind_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.bind_bind_swap

/--
info: 'OracleComp.evalDistEq_of_forall_prEvent_eq_output' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDistEq_of_forall_prEvent_eq_output

/--
info: 'OracleComp.prEvent_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_one_iff

/--
info: 'OracleComp.prEvent_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_zero_iff

/--
info: 'SampleableType.evalDist_uniformSample_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SampleableType.evalDist_uniformSample_singleton

/--
info: 'SampleableType.prEvent_uniformSample_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SampleableType.prEvent_uniformSample_eq_singleton

/--
info: 'SampleableType.map_uniformSample_evalDistEq_of_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SampleableType.map_uniformSample_evalDistEq_of_bijective
