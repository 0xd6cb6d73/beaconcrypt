import VCVio.EvalDist.ProbabilityNotation
import VCVio.EvalDist.Monad.Measure
import VCVio.EvalDist.Defs.Support

/-!
# Forward shim: equality in distribution and event laws (VCVio pin 98dc1089)

The pinned VCVio deprecates its discrete probability API (`Pr[= x | mx]`, `Pr[p | mx]`, `𝒮[mx]`) in favour of the event notation `Pr{let x ← mx}[p x]`, which needs no measurable space on the output, and of output measures `𝒟[mx]`. Upstream VCVio (afa6593f) completes that vocabulary with equality in distribution `EvalDistEq mx my` and a library of event laws, most of which the pin lacks. This module backports them so that migrated statements and proofs use the upstream names and statements already at the pin.

Every declaration carries the upstream name in the upstream namespace and the upstream statement, with two documented pin adjustments. Upstream states a few laws for its head constant `prEvent mx` (with `mx : m Prop`); the pin has no such constant, and `Pr{…}` expands to the success mass `𝒟[mx] {True}`, so those laws are stated for `𝒟[mx] {True}`, which upstream unfolds to `prEvent mx`. Upstream `grind` annotations are not copied. One spelling differs: upstream also declares the notation `mx =ᵈ my` for `EvalDistEq mx my`; this module does not backport it, because project modules declare no notation, so statements here and in migrated modules write `EvalDistEq mx my`, which elaborates to the same term. At the upgrade the backported definition is deleted and these statements name upstream's `EvalDistEq` unchanged. The proofs are pin-specific and are discarded at the VCVio upgrade, when this module keeps only the imports of the upstream modules. Nothing here is assumed: every law is proved from the pinned VCVio and Mathlib.
-/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

universe u v v' v''

section defs

variable {m : Type → Type v} {m' : Type → Type v'} [EvalDistSemantics m] [EvalDistSemantics m']
  [Monad m] [Monad m'] {α : Type}

/-- Two computations are equal in distribution when every event has the same probability under both. Upstream writes `EvalDistEq mx my` as `mx =ᵈ my`; the notation is not backported. -/
def EvalDistEq (mx : m α) (my : m' α) : Prop :=
  ∀ p : α → Prop, Pr{let x ← mx}[p x] = Pr{let y ← my}[p y]

end defs

namespace EvalDistEq

variable {m : Type → Type v} {m' : Type → Type v'} {m'' : Type → Type v''}
  [Monad m] [Monad m'] [Monad m''] [EvalDistSemantics m] [EvalDistSemantics m']
  [EvalDistSemantics m''] {α β : Type}

/-- Equality in distribution gives every event the same probability. -/
theorem prEvent_eq {mx : m α} {my : m' α} (h : EvalDistEq mx my) (p : α → Prop) :
    Pr{let x ← mx}[p x] = Pr{let y ← my}[p y] :=
  h p

/-- Computations whose events all have the same probabilities are equal in distribution. -/
theorem of_forall_prEvent_eq {mx : m α} {my : m' α}
    (h : ∀ p : α → Prop, Pr{let x ← mx}[p x] = Pr{let y ← my}[p y]) : EvalDistEq mx my :=
  h

/-- Equality in distribution is reflexive. -/
@[refl, simp]
theorem refl (mx : m α) : EvalDistEq mx mx := fun _ ↦ rfl

/-- Equality in distribution is reflexive (implicit form). -/
protected theorem rfl {mx : m α} : EvalDistEq mx mx := refl mx

/-- Equality in distribution is symmetric. -/
@[symm]
theorem symm {mx : m α} {my : m' α} (h : EvalDistEq mx my) : EvalDistEq my mx := fun p ↦ (h p).symm

/-- Equality in distribution is transitive, also across three monads. -/
theorem trans {mx : m α} {my : m' α} {mz : m'' α} (h₁ : EvalDistEq mx my)
    (h₂ : EvalDistEq my mz) : EvalDistEq mx mz :=
  fun p ↦ (h₁ p).trans (h₂ p)

instance : @Trans (m α) (m' α) (m'' α) EvalDistEq EvalDistEq EvalDistEq := ⟨trans⟩

instance : Std.Refl (α := m α) EvalDistEq := ⟨refl⟩

instance : Std.Symm (α := m α) EvalDistEq := ⟨fun _ _ ↦ symm⟩

instance : IsTrans (m α) EvalDistEq := ⟨fun _ _ _ ↦ trans⟩

/-- A common map preserves equality in distribution. -/
theorem map [LawfulMonad m] [LawfulMonad m'] {mx : m α} {my : m' α} (h : EvalDistEq mx my)
    (f : α → β) : EvalDistEq (f <$> mx) (f <$> my) :=
  fun p ↦ by simpa only [prEvent_map] using h fun x ↦ p (f x)

section lawful

variable [LawfulMonad m] [LawfulMonad m'] [LawfulEvalDistSemantics m]
  [LawfulEvalDistSemantics m']

/-- Computations equal in distribution have the same output measure in every measurable structure on their outputs. -/
theorem evalDist_eq [MeasurableSpace α] {mx : m α} {my : m' α} (h : EvalDistEq mx my) :
    𝒟[mx] = 𝒟[my] := by
  ext s hs
  have hp : Measurable fun x : α ↦ x ∈ s := measurableSet_setOfPred.mp hs
  simpa using (prEvent_eq_evalDist mx _ hp).symm.trans ((h _).trans (prEvent_eq_evalDist my _ hp))

/-- Computations with the same output measure in a discrete structure are equal in distribution. -/
theorem of_evalDist_eq {_ : MeasurableSpace α} [DiscreteMeasurableSpace α] {mx : m α}
    {my : m' α} (h : 𝒟[mx] = 𝒟[my]) : EvalDistEq mx my := fun p ↦ by
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete, h]

/-- Equality in distribution is equality of the output measures in the discrete structure. -/
theorem _root_.evalDistEq_iff_evalDist_eq {mx : m α} {my : m' α} :
    EvalDistEq mx my ↔ (letI : MeasurableSpace α := ⊤; 𝒟[mx] = 𝒟[my]) :=
  letI : MeasurableSpace α := ⊤
  ⟨evalDist_eq, of_evalDist_eq⟩

/-- On a countable output type, equality in distribution is equality of every point mass. -/
theorem _root_.evalDistEq_iff_forall_prEvent_eq_output [Countable α] {mx : m α} {my : m' α} :
    EvalDistEq mx my ↔ ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x] := by
  let : MeasurableSpace α := ⊤
  refine ⟨fun h x ↦ h (· = x), fun h ↦ of_evalDist_eq (Measure.ext_of_singleton fun x ↦ ?_)⟩
  rw [← prEvent_eq_evalDist_singleton mx x, ← prEvent_eq_evalDist_singleton my x]
  exact h x

/-- Binds of computations and continuations equal in distribution are equal in distribution. -/
theorem bind {mx : m α} {my : m' α} (h : EvalDistEq mx my) {f : α → m β} {g : α → m' β}
    (hfg : ∀ a, EvalDistEq (f a) (g a)) : EvalDistEq (mx >>= f) (my >>= g) := by
  let : MeasurableSpace α := ⊤
  intro p
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete, h.evalDist_eq]
  exact lintegral_congr fun a ↦ hfg a p

end lawful

section sameMonad

/-- A common map is a congruence for equality in distribution within one monad. -/
@[gcongr]
theorem map_congr [LawfulMonad m] (f : α → β) {mx my : m α} (h : EvalDistEq mx my) :
    EvalDistEq (f <$> mx) (f <$> my) :=
  h.map f

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- Bind is a congruence for equality in distribution within one monad. -/
@[gcongr]
theorem bind_congr {mx my : m α} {f g : α → m β} (h : EvalDistEq mx my)
    (hfg : ∀ a, EvalDistEq (f a) (g a)) : EvalDistEq (mx >>= f) (my >>= g) :=
  h.bind hfg

/-- A computation equal in distribution may replace the first draw of a bind. -/
theorem bind_left {mx my : m α} (h : EvalDistEq mx my) (f : α → m β) :
    EvalDistEq (mx >>= f) (my >>= f) :=
  h.bind fun _ ↦ .rfl

/-- Continuations equal in distribution may replace one another after a common draw. -/
theorem bind_right (mx : m α) {f g : α → m β} (hfg : ∀ a, EvalDistEq (f a) (g a)) :
    EvalDistEq (mx >>= f) (mx >>= g) :=
  EvalDistEq.rfl.bind hfg

end sameMonad

end EvalDistEq

/-! ## Event laws of `ProbabilityNotation` absent at the pin -/

section notationLaws

variable {m : Type → Type v}

/-- An impossible final observation has zero mass, including after a failed computation. -/
theorem prEvent_false [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) : Pr{let _ ← mx}[False] = 0 :=
  prEvent_eq_zero_of_forall_not mx (fun _ ↦ False) (fun _ ↦ id)

/-- An event of a pure computation has probability one exactly when it holds. -/
theorem prEvent_pure [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] {α : Type} (a : α) (p : α → Prop) [Decidable (p a)] :
    Pr{let x ← (pure a : m α)}[p x] = if p a then 1 else 0 := by
  rw [pure_bind, evalDist_pure]
  by_cases h : p a <;> simp [h]

/-- Every event probability is at most one. Upstream states it for `prEvent mx`, which is `𝒟[mx] {True}`. -/
@[simp]
theorem prEvent_le_one [EvalDistSemantics m] (mx : m Prop) : 𝒟[mx] {True} ≤ 1 :=
  (measure_mono (Set.subset_univ _)).trans (evalDist_apply_univ_le_one mx)

/-- Every event probability is finite. Upstream states it for `prEvent mx`, which is `𝒟[mx] {True}`. -/
@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem prEvent_ne_top [EvalDistSemantics m] (mx : m Prop) : 𝒟[mx] {True} ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one mx)

/-- Every event probability is finite. Upstream states it for `prEvent mx`, which is `𝒟[mx] {True}`. -/
@[simp]
theorem prEvent_lt_top [EvalDistSemantics m] (mx : m Prop) : 𝒟[mx] {True} < ⊤ :=
  (prEvent_ne_top mx).lt_top

/-- The trivially true event is the successful mass of the computation, in any measurable structure on its outputs. -/
theorem prEvent_true_eq_evalDist_apply_univ [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α : Type} [MeasurableSpace α] (mx : m α) :
    Pr{let _ ← mx}[True] = 𝒟[mx] Set.univ := by
  rw [prEvent_eq_evalDist mx (fun _ ↦ True) measurable_const]
  rfl

/-- A prefix whose result is unused scales the event by its successful mass. Upstream states it for `prEvent`, which is `𝒟[·] {True}`. -/
theorem prEvent_bind_const [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α : Type} (mx : m α) (my : m Prop) :
    𝒟[mx >>= fun _ ↦ my] {True} = Pr{let _ ← mx}[True] * 𝒟[my] {True} := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ, evalDist_bind_const, Measure.smul_apply, smul_eq_mul]

/-- After a draw from a finite type, an event is the finite sum of the draw's point masses times the conditional event probabilities. -/
theorem prEvent_bind_eq_sum_fintype [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type} [Fintype α] (mx : m α) (f : α → m β)
    (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∑ a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, MeasureTheory.lintegral_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, prEvent_eq_evalDist_singleton]

/-- After a draw from a countable type, an event is the sum of the draw's point masses times the conditional event probabilities. -/
theorem prEvent_bind_eq_tsum_of_countable [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type} [Countable α] (mx : m α) (f : α → m β)
    (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∑' a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, MeasureTheory.lintegral_countable']
  refine tsum_congr fun a => ?_
  rw [mul_comm, ← prEvent_eq_evalDist_singleton]

end notationLaws

/-! ## Event algebra and union bounds (upstream `ProbabilityBounds`) -/

section eventAlgebra

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}

/-- Union bound for two events after a common draw. -/
theorem prEvent_or_le (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x ∨ q x] ≤ Pr{let x ← mx}[p x] + Pr{let x ← mx}[q x] := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_of_discrete]
  exact (measure_mono (by intro x hx; exact hx)).trans (measure_union_le {x | p x} {x | q x})

/-- Union bound over a finite index set. -/
theorem prEvent_exists_finset_le {ι : Type} (s : Finset ι) (mx : m α) (p : ι → α → Prop) :
    Pr{let x ← mx}[∃ i ∈ s, p i x] ≤ ∑ i ∈ s, Pr{let x ← mx}[p i x] := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_of_discrete]
  refine (measure_mono ?_).trans (measure_biUnion_finset_le s fun i ↦ {x | p i x})
  intro x hx
  obtain ⟨i, hi, hp⟩ := hx
  exact Set.mem_biUnion hi hp

/-- Union bound over a finite type. -/
theorem prEvent_exists_le {ι : Type} [Fintype ι] (mx : m α) (p : ι → α → Prop) :
    Pr{let x ← mx}[∃ i, p i x] ≤ ∑ i, Pr{let x ← mx}[p i x] := by
  simpa using prEvent_exists_finset_le Finset.univ mx p

/-- An event splits along a second predicate. -/
theorem prEvent_eq_prEvent_and_add_prEvent_and_not (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[p x ∧ q x] + Pr{let x ← mx}[p x ∧ ¬ q x] := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_of_discrete]
  rw [← measure_union (Set.disjoint_left.mpr fun x hx hx' ↦ hx'.2 hx.2) MeasurableSet.of_discrete]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  exact ⟨fun hp ↦ (em (q x)).imp (fun hq ↦ ⟨hp, hq⟩) (fun hq ↦ ⟨hp, hq⟩),
    fun h ↦ h.elim And.left And.left⟩

/-- An event is bounded by a second one plus the part outside it. -/
theorem prEvent_le_prEvent_add_prEvent_and_not (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] + Pr{let x ← mx}[p x ∧ ¬ q x] := by
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not mx p q]
  exact add_le_add_left (prEvent_mono mx (fun x ↦ p x ∧ q x) q fun x hx ↦ hx.2) _

/-- An event and its negation partition the successful mass. -/
theorem prEvent_add_prEvent_not_eq_prEvent_true (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] + Pr{let x ← mx}[¬p x] = Pr{let _ ← mx}[True] := by
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not mx (fun _ ↦ True) p]
  simp only [true_and]

/-- A conjunction is bounded by its first conjunct. -/
theorem prEvent_and_le_left (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x ∧ q x] ≤ Pr{let x ← mx}[p x] :=
  prEvent_mono mx _ _ fun _ hx ↦ hx.1

/-- A conjunction is bounded by its second conjunct. -/
theorem prEvent_and_le_right (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x ∧ q x] ≤ Pr{let x ← mx}[q x] :=
  prEvent_mono mx _ _ fun _ hx ↦ hx.2

end eventAlgebra

/-! ## Conditioning on a common draw (upstream `ProbabilityBounds`) -/

section conditioning

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}

/-- A uniform bound on the event of every continuation bounds the event after a common draw. No losslessness of the draw is needed. -/
theorem prEvent_bind_le_of_forall_le (mx : m α) (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ ε := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ a, Pr{let y ← f a}[q y] ∂𝒟[mx]
      ≤ ∫⁻ _, ε ∂𝒟[mx] := lintegral_mono h
    _ = ε * 𝒟[mx] Set.univ := lintegral_const ε
    _ ≤ ε := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- A pointwise comparison of continuation events survives a common draw. -/
theorem prEvent_bind_mono_of_forall_le {γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop) (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y]) :
    Pr{let y ← mx >>= f}[p y] ≤ Pr{let y ← mx >>= g}[q y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  exact lintegral_mono h

/-- A pointwise split of a continuation event into two other continuation events survives a common draw. -/
theorem prEvent_bind_le_add_of_forall_le {γ δ : Type} (mx : m α) (f : α → m β)
    (g : α → m γ) (k : α → m δ) (p : β → Prop) (q : γ → Prop) (r : δ → Prop)
    (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y] + Pr{let y ← k a}[r y]) :
    Pr{let y ← mx >>= f}[p y] ≤ Pr{let y ← mx >>= g}[q y] + Pr{let y ← mx >>= k}[r y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    prEvent_bind_eq_lintegral_of_discrete, ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_mono h

/-- A uniform lower bound on the event of every continuation bounds the event after a lossless common draw. -/
theorem le_prEvent_bind_of_forall_le (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ε ≤ Pr{let y ← f a}[q y]) :
    ε ≤ Pr{let y ← mx >>= f}[q y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ] at hmx
  rw [prEvent_bind_eq_lintegral_of_discrete]
  calc ε = ∫⁻ _, ε ∂𝒟[mx] := by rw [lintegral_const, hmx, mul_one]
    _ ≤ _ := lintegral_mono h

/-- Conditioning on a predicate of the common draw: the continuation event is bounded by the predicate's probability plus the conditional bound weighted by the predicate's complement. -/
theorem prEvent_bind_le_prEvent_add_mul_prEvent_not (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε * Pr{let a ← mx}[¬ p a] := by
  classical
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  have hpt : ∀ a, Pr{let y ← f a}[q y] ≤
      ({a | p a} : Set α).indicator (fun _ ↦ 1) a +
        ({a | ¬ p a} : Set α).indicator (fun _ ↦ ε) a := by
    intro a
    by_cases hpa : p a
    · rw [Set.indicator_of_mem (show a ∈ {a | p a} from hpa),
        Set.indicator_of_notMem (show a ∉ {a | ¬ p a} from not_not.mpr hpa), add_zero]
      exact prEvent_le_one _
    · rw [Set.indicator_of_notMem (show a ∉ {a | p a} from hpa),
        Set.indicator_of_mem (show a ∈ {a | ¬ p a} from hpa), zero_add]
      exact h a hpa
  calc ∫⁻ a, Pr{let y ← f a}[q y] ∂𝒟[mx]
      ≤ ∫⁻ a, ({a | p a} : Set α).indicator (fun _ ↦ 1) a +
          ({a | ¬ p a} : Set α).indicator (fun _ ↦ ε) a ∂𝒟[mx] := lintegral_mono hpt
    _ = 𝒟[mx] {a | p a} + ε * 𝒟[mx] {a | ¬ p a} := by
      rw [lintegral_add_left (Measurable.of_discrete),
        lintegral_indicator MeasurableSet.of_discrete,
        lintegral_indicator MeasurableSet.of_discrete]
      simp [lintegral_const]

/-- A continuation event vanishing outside a predicate of the common draw is bounded by the predicate's probability. -/
theorem prEvent_bind_le_prEvent_of_forall_eq_zero (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] := by
  simpa using prEvent_bind_le_prEvent_add_mul_prEvent_not mx f p q (ε := 0)
    fun a ha ↦ (h a ha).le

/-- A continuation event bounded by `ε` outside a predicate of the common draw is bounded by the predicate's probability plus `ε`. -/
theorem prEvent_bind_le_prEvent_add (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε :=
  (prEvent_bind_le_prEvent_add_mul_prEvent_not mx f p q h).trans
    (add_le_add_right (mul_le_of_le_one_right' (prEvent_le_one _)) _)

end conditioning

/-! ## Reachable continuations through core attachment (upstream `ProbabilityBounds`) -/

section attach

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [WeaklyLawfulMonadAttach m] {α β : Type}

/-- A bind factors through the attachment of its possible outputs. -/
theorem bind_eq_attach_bind (mx : m α) (f : α → m β) :
    mx >>= f = MonadAttach.attach mx >>= fun a ↦ f a.1 := by
  conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [bind_map_left]

variable [EvalDistSemantics m]

/-- The trivially true event is unchanged by attachment. -/
theorem prEvent_true_attach (mx : m α) :
    Pr{let _ ← MonadAttach.attach mx}[True] = Pr{let _ ← mx}[True] := by
  conv_rhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [prEvent_map]

variable [LawfulEvalDistSemantics m]

/-- Implication between events only on the possible outputs bounds their probabilities. -/
theorem prEvent_mono_of_support (mx : m α) (p q : α → Prop)
    (h : ∀ a ∈ support mx, p a → q a) :
    Pr{let a ← mx}[p a] ≤ Pr{let a ← mx}[q a] := by
  conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  conv_rhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun a ha ↦ h a.1 a.2 ha

/-- Events that agree on every possible output have equal probability. -/
theorem prEvent_congr_of_support (mx : m α) (p q : α → Prop)
    (h : ∀ a ∈ support mx, p a ↔ q a) :
    Pr{let a ← mx}[p a] = Pr{let a ← mx}[q a] :=
  le_antisymm (prEvent_mono_of_support mx p q fun a ha ↦ (h a ha).1)
    (prEvent_mono_of_support mx q p fun a ha ↦ (h a ha).2)

/-- An event avoiding every possible output has probability zero. -/
theorem prEvent_eq_zero_of_forall_mem_support (mx : m α) (p : α → Prop)
    (h : ∀ a ∈ support mx, ¬ p a) : Pr{let a ← mx}[p a] = 0 :=
  (prEvent_congr_of_support mx p (fun _ ↦ False) fun a ha ↦ iff_false_intro (h a ha)).trans
    (prEvent_eq_zero_of_forall_not mx _ fun _ ↦ id)

/-- An unreachable output has probability zero. -/
theorem prEvent_eq_zero_of_not_mem_support (mx : m α) {x : α} (hx : x ∉ support mx) :
    Pr{let y ← mx}[y = x] = 0 :=
  prEvent_eq_zero_of_forall_mem_support mx _ fun _ hy h ↦ hx (h ▸ hy)

/-- A bound on the event of every reachable continuation bounds the event after the draw. -/
theorem prEvent_bind_le_of_forall_le_of_support (mx : m α) (f : α → m β) (q : β → Prop)
    {ε : ℝ≥0∞} (h : ∀ a ∈ support mx, Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ ε := by
  rw [bind_eq_attach_bind mx f]
  exact prEvent_bind_le_of_forall_le _ _ q fun a ↦ h a.1 a.2

/-- A comparison of continuation events on the possible outputs survives a common draw. -/
theorem prEvent_bind_mono_of_forall_le_of_support {γ : Type} (mx : m α) (f : α → m β)
    (g : α → m γ) (p : β → Prop) (q : γ → Prop)
    (h : ∀ a ∈ support mx, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y]) :
    Pr{let y ← mx >>= f}[p y] ≤ Pr{let y ← mx >>= g}[q y] := by
  rw [bind_eq_attach_bind mx f, bind_eq_attach_bind mx g]
  exact prEvent_bind_mono_of_forall_le _ _ _ p q fun a ↦ h a.1 a.2

/-- A lower bound on the event of every reachable continuation bounds the event after a lossless draw. -/
theorem le_prEvent_bind_of_forall_le_of_support (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ε ≤ Pr{let y ← f a}[q y]) :
    ε ≤ Pr{let y ← mx >>= f}[q y] := by
  rw [bind_eq_attach_bind mx f]
  exact le_prEvent_bind_of_forall_le _ (by rwa [prEvent_true_attach]) _ q fun a ↦ h a.1 a.2

/-- Conditioning on a predicate of the reachable common draw. -/
theorem prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε * Pr{let a ← mx}[¬ p a] := by
  rw [bind_eq_attach_bind mx f]
  have := prEvent_bind_le_prEvent_add_mul_prEvent_not (MonadAttach.attach mx) (fun a ↦ f a.1)
    (fun a ↦ p a.1) q fun a ha ↦ h a.1 a.2 ha
  refine this.trans (le_of_eq ?_)
  conv_rhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [prEvent_map, prEvent_map]

/-- A continuation event vanishing outside a predicate of the reachable draw is bounded by the predicate's probability. -/
theorem prEvent_bind_le_prEvent_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] := by
  simpa using prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support mx f p q (ε := 0)
    fun a ha hp ↦ (h a ha hp).le

/-- A continuation event bounded outside a predicate of the reachable draw. -/
theorem prEvent_bind_le_prEvent_add_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε :=
  (prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support mx f p q h).trans
    (add_le_add_right (mul_le_of_le_one_right' (prEvent_le_one _)) _)

end attach

/-! ## Reachability and measurable observations (upstream `Monad/Measure`) -/

namespace evalDist

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {α : Type u} [MeasurableSpace α] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m]

/-- A measurable predicate holding on every possible output holds almost everywhere under the successful-output measure. -/
theorem ae_of_forall_mem_support (mx : m α) (p : α → Prop)
    (hp : MeasurableSet {x | p x}) (h : ∀ x ∈ support mx, p x) :
    ∀ᵐ x ∂𝒟[mx], p x := by
  rw [← WeaklyLawfulMonadAttach.map_attach (x := mx),
    evalDist_map (MonadAttach.attach mx) measurable_subtype_coe,
    ae_map_iff measurable_subtype_coe.aemeasurable hp]
  exact Filter.Eventually.of_forall fun x ↦ h x.1 x.2

end evalDist

/--
info: 'EvalDistEq.prEvent_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.prEvent_eq

/--
info: 'EvalDistEq.of_forall_prEvent_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.of_forall_prEvent_eq

/--
info: 'EvalDistEq.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.refl

/--
info: 'EvalDistEq.rfl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.rfl

/--
info: 'EvalDistEq.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.symm

/--
info: 'EvalDistEq.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.trans

/--
info: 'EvalDistEq.map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.map

/--
info: 'EvalDistEq.evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.evalDist_eq

/--
info: 'EvalDistEq.of_evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.of_evalDist_eq

/--
info: 'evalDistEq_iff_evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evalDistEq_iff_evalDist_eq

/--
info: 'evalDistEq_iff_forall_prEvent_eq_output' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evalDistEq_iff_forall_prEvent_eq_output

/--
info: 'EvalDistEq.bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind

/--
info: 'EvalDistEq.map_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.map_congr

/--
info: 'EvalDistEq.bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind_congr

/--
info: 'EvalDistEq.bind_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind_left

/--
info: 'EvalDistEq.bind_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind_right

/--
info: 'prEvent_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_false

/--
info: 'prEvent_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_pure

/--
info: 'prEvent_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_le_one

/--
info: 'prEvent_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_ne_top

/--
info: 'prEvent_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_lt_top

/--
info: 'prEvent_true_eq_evalDist_apply_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_true_eq_evalDist_apply_univ

/--
info: 'prEvent_bind_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_const

/--
info: 'prEvent_bind_eq_sum_fintype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_eq_sum_fintype

/--
info: 'prEvent_bind_eq_tsum_of_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_eq_tsum_of_countable

/--
info: 'prEvent_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_or_le

/--
info: 'prEvent_exists_finset_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_exists_finset_le

/--
info: 'prEvent_exists_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_exists_le

/--
info: 'prEvent_eq_prEvent_and_add_prEvent_and_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_eq_prEvent_and_add_prEvent_and_not

/--
info: 'prEvent_le_prEvent_add_prEvent_and_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_le_prEvent_add_prEvent_and_not

/--
info: 'prEvent_add_prEvent_not_eq_prEvent_true' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_add_prEvent_not_eq_prEvent_true

/--
info: 'prEvent_and_le_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_and_le_left

/--
info: 'prEvent_and_le_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_and_le_right

/--
info: 'prEvent_bind_le_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_of_forall_le

/--
info: 'prEvent_bind_mono_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_mono_of_forall_le

/--
info: 'prEvent_bind_le_add_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_add_of_forall_le

/--
info: 'le_prEvent_bind_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms le_prEvent_bind_of_forall_le

/--
info: 'prEvent_bind_le_prEvent_add_mul_prEvent_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add_mul_prEvent_not

/--
info: 'prEvent_bind_le_prEvent_of_forall_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_of_forall_eq_zero

/--
info: 'prEvent_bind_le_prEvent_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add

/--
info: 'bind_eq_attach_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms bind_eq_attach_bind

/--
info: 'prEvent_true_attach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_true_attach

/--
info: 'prEvent_mono_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_mono_of_support

/--
info: 'prEvent_congr_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_congr_of_support

/--
info: 'prEvent_eq_zero_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_eq_zero_of_forall_mem_support

/--
info: 'prEvent_eq_zero_of_not_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_eq_zero_of_not_mem_support

/--
info: 'prEvent_bind_le_of_forall_le_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_of_forall_le_of_support

/--
info: 'prEvent_bind_mono_of_forall_le_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_mono_of_forall_le_of_support

/--
info: 'le_prEvent_bind_of_forall_le_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms le_prEvent_bind_of_forall_le_of_support

/--
info: 'prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support

/--
info: 'prEvent_bind_le_prEvent_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_of_support

/--
info: 'prEvent_bind_le_prEvent_add_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add_of_support

/--
info: 'evalDist.ae_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evalDist.ae_of_forall_mem_support
