import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Sum
import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
import BeaconcryptCore.Computational.BooleanDistance

/-!
# Total variation of complete discrete observations

The distance fixes the discrete measurable structure inside its definition so that every part of an arbitrary protocol state remains observable. Its laws use VCVio's native measure semantics and preserve the project's real-valued statistical bounds.
-/

open MeasureTheory OracleComp OracleSpec
open scoped ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational

universe v

/-- Real total variation when every subset of the complete output is observable. -/
noncomputable def discreteDistance {m : Type → Type v} [EvalDistSemantics m] {α : Type}
    (p q : m α) : ℝ :=
  letI : MeasurableSpace α := ⊤
  measureTVDist p q

section Basic
variable {m : Type → Type v} [EvalDistSemantics m] {α : Type}

/-- Total variation is nonnegative. -/
theorem discreteDistance_nonneg (p q : m α) : 0 ≤ discreteDistance p q :=
  letI : MeasurableSpace α := ⊤
  measureTVDist_nonneg p q

/-- Successful-output subprobability measures have distance at most one. -/
theorem discreteDistance_le_one (p q : m α) : discreteDistance p q ≤ 1 :=
  letI : MeasurableSpace α := ⊤
  measureTVDist_le_one p q

/-- A computation has zero distance from itself. -/
@[simp] theorem discreteDistance_self (p : m α) : discreteDistance p p = 0 :=
  letI : MeasurableSpace α := ⊤
  measureTVDist_self p

/-- Complete-output distance is symmetric. -/
theorem discreteDistance_comm (p q : m α) : discreteDistance p q = discreteDistance q p :=
  letI : MeasurableSpace α := ⊤
  measureTVDist_comm p q

/-- Complete-output distance satisfies the triangle inequality. -/
theorem discreteDistance_triangle (p q r : m α) :
    discreteDistance p r ≤ discreteDistance p q + discreteDistance q r :=
  letI : MeasurableSpace α := ⊤
  measureTVDist_triangle p q r

/-- The real distance is the real value of the native extended distance on the discrete output. -/
theorem discreteDistance_eq_toReal (p q : m α) :
    discreteDistance p q =
      (letI : MeasurableSpace α := ⊤; (measureETVDist p q).toReal) :=
  letI : MeasurableSpace α := ⊤
  measureTVDist_eq_toReal_measureETVDist p q

/-- Converting the real distance back to an extended bound loses no information. -/
theorem ofReal_discreteDistance_eq (p q : m α) :
    ENNReal.ofReal (discreteDistance p q) =
      (letI : MeasurableSpace α := ⊤; measureETVDist p q) :=
  letI : MeasurableSpace α := ⊤
  (congrArg ENNReal.ofReal (measureTVDist_eq_toReal_measureETVDist p q)).trans
    (ENNReal.ofReal_toReal (measureETVDist_ne_top p q))

end Basic

section Lawful
variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type}

/-- A common observation cannot increase complete-output distance. -/
theorem discreteDistance_map_le (f : α → β) (p q : m α) :
    discreteDistance (f <$> p) (f <$> q) ≤ discreteDistance p q :=
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  measureTVDist_map_le p q f .of_discrete

omit [LawfulMonad m] in
/-- A common continuation cannot increase complete-output distance. -/
theorem discreteDistance_bind_right_le (f : α → m β) (p q : m α) :
    discreteDistance (p >>= f) (q >>= f) ≤ discreteDistance p q :=
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  measureTVDist_bind_le p q f .of_discrete

/-- Any event's real probabilities differ by at most the complete-output distance. -/
theorem abs_prEvent_toReal_sub_le_discreteDistance_event (p q : m α) (event : α → Prop) :
    |(Pr{let x ← p}[event x]).toReal - (Pr{let x ← q}[event x]).toReal| ≤
      discreteDistance p q :=
  letI : MeasurableSpace α := ⊤
  abs_prEvent_toReal_sub_le_measureTVDist p q event .of_discrete

/-- Every event probability is bounded by the other game's event and their distance. -/
theorem prEvent_le_prEvent_add_ofReal_discreteDistance (p q : m α) (event : α → Prop) :
    Pr{let x ← p}[event x] ≤ Pr{let x ← q}[event x] + ENNReal.ofReal (discreteDistance p q) :=
  letI : MeasurableSpace α := ⊤
  (ofReal_discreteDistance_eq p q).symm ▸
    prEvent_le_prEvent_add_measureETVDist p q event .of_discrete

/-- The real success probabilities of Boolean computations differ by at most their distance. -/
theorem abs_prEvent_toReal_sub_le_discreteDistance (p q : m Bool) :
    |(Pr{let b ← p}[b = true]).toReal - (Pr{let b ← q}[b = true]).toReal| ≤
      discreteDistance p q :=
  abs_prEvent_toReal_sub_le_discreteDistance_event p q (· = true)

/-- The singleton-mass form of the Boolean success discrepancy bound. -/
theorem abs_evalDist_true_toReal_sub_le_discreteDistance (p q : m Bool) :
    |(𝒟[p] {true}).toReal - (𝒟[q] {true}).toReal| ≤ discreteDistance p q := by
  simpa only [prEvent_eq_evalDist_singleton] using
    abs_prEvent_toReal_sub_le_discreteDistance p q

/-- Equality in distribution of both games preserves their complete-output distance. -/
theorem discreteDistance_congr {p p' q q' : m α} (hp : p =ᵈ p') (hq : q =ᵈ q') :
    discreteDistance p q = discreteDistance p' q' :=
  letI : MeasurableSpace α := ⊤
  congrArg₂ Measure.tvDist hp.evalDist_eq hq.evalDist_eq

end Lawful

/-- The project Boolean advantage is bounded by the distance of the complete Boolean laws. -/
theorem boolDistance_le_discreteDistance (p q : ProbComp Bool) :
    p.boolDistance q ≤ discreteDistance p q :=
  abs_evalDist_true_toReal_sub_le_discreteDistance p q

section Oracle
universe u
variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [OracleSpec.UniformAnswerMeasure spec]
  {α β : Type}

/-- A shared prefix averages the real distances of its continuations. -/
theorem discreteDistance_bind_left_le (p : OracleComp spec α) (f g : α → OracleComp spec β) :
    discreteDistance (p >>= f) (p >>= g) ≤
      ∑' a, (Pr{let x ← p}[x = a]).toReal * discreteDistance (f a) (g a) :=
  letI : MeasurableSpace β := ⊤
  letI : ∀ t, Finite (spec.Range t) := fun t => UniformAnswerMeasure.finite_range t
  OracleComp.measureTVDist_bind_left_le_tsum p f g

/-- A uniform bound only on reachable continuations suffices after a shared prefix. -/
theorem discreteDistance_bind_left_le_const (p : OracleComp spec α)
    (f g : α → OracleComp spec β) (c : ℝ)
    (h : ∀ a ∈ support p, discreteDistance (f a) (g a) ≤ c) :
    discreteDistance (p >>= f) (p >>= g) ≤ c :=
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : ∀ t, Nonempty (spec.Range t) := fun t => UniformAnswerMeasure.nonempty_range t
  have hc : 0 ≤ c :=
    (discreteDistance_nonneg (f (OracleComp.support_nonempty p).choose)
      (g (OracleComp.support_nonempty p).choose)).trans
        (h _ (OracleComp.support_nonempty p).choose_spec)
  have hbound : ∀ᵐ a ∂𝒟[p], measureETVDist (f a) (g a) ≤ ENNReal.ofReal c :=
    (OracleComp.evalDist_ae_mem_support p).mono fun a ha =>
      (ofReal_discreteDistance_eq (f a) (g a)) ▸ ENNReal.ofReal_le_ofReal (h a ha)
  have hdist : measureETVDist (p >>= f) (p >>= g) ≤ ENNReal.ofReal c :=
    (measureETVDist_bind_bind_le_lintegral p f g .of_discrete .of_discrete
      (fun _ => ENNReal.ofReal c) hbound).trans_eq (by simp)
  (ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist).trans_eq (ENNReal.toReal_ofReal hc)

/-- An extended bound on reachable continuations survives their shared prefix. -/
theorem ofReal_discreteDistance_bind_left_le_const (p : OracleComp spec α)
    (f g : α → OracleComp spec β) (ε : ℝ≥0∞)
    (h : ∀ a ∈ support p, ENNReal.ofReal (discreteDistance (f a) (g a)) ≤ ε) :
    ENNReal.ofReal (discreteDistance (p >>= f) (p >>= g)) ≤ ε :=
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  have hbound : ∀ᵐ a ∂𝒟[p], measureETVDist (f a) (g a) ≤ ε :=
    (OracleComp.evalDist_ae_mem_support p).mono fun a ha =>
      (ofReal_discreteDistance_eq (f a) (g a)) ▸ h a ha
  (ofReal_discreteDistance_eq (p >>= f) (p >>= g)).trans_le
    ((measureETVDist_bind_bind_le_lintegral p f g .of_discrete .of_discrete
      (fun _ => ε) hbound).trans_eq (by simp))

/-- An extended bound on every continuation survives their shared prefix. -/
theorem ofReal_discreteDistance_bind_left_le_const' (p : OracleComp spec α)
    (f g : α → OracleComp spec β) (ε : ℝ≥0∞)
    (h : ∀ a, ENNReal.ofReal (discreteDistance (f a) (g a)) ≤ ε) :
    ENNReal.ofReal (discreteDistance (p >>= f) (p >>= g)) ≤ ε :=
  ofReal_discreteDistance_bind_left_le_const p f g ε fun a _ => h a

/-- A uniform bound on all continuations survives their shared prefix. -/
theorem discreteDistance_bind_left_le_const' (p : OracleComp spec α)
    (f g : α → OracleComp spec β) (c : ℝ) (h : ∀ a, discreteDistance (f a) (g a) ≤ c) :
    discreteDistance (p >>= f) (p >>= g) ≤ c :=
  letI : MeasurableSpace β := ⊤
  letI : ∀ t, Finite (spec.Range t) := fun t => UniformAnswerMeasure.finite_range t
  letI : ∀ t, Nonempty (spec.Range t) := fun t => UniformAnswerMeasure.nonempty_range t
  let a := (OracleComp.support_nonempty p).choose
  OracleComp.measureTVDist_bind_left_le_of_forall_le p f g
    ((discreteDistance_nonneg (f a) (g a)).trans (h a)) h

/-- Continuations equal in distribution outside a bad prefix event cost at most that event. -/
theorem discreteDistance_bind_left_event_le (p : OracleComp spec α)
    (f g : α → OracleComp spec β) (bad : α → Prop)
    (h : ∀ a, ¬bad a → f a =ᵈ g a) :
    discreteDistance (p >>= f) (p >>= g) ≤ (Pr{let x ← p}[bad x]).toReal :=
  letI : MeasurableSpace β := ⊤
  letI : ∀ t, Finite (spec.Range t) := fun t => UniformAnswerMeasure.finite_range t
  OracleComp.measureTVDist_bind_left_le_prEvent_of_evalDistEq p f g bad h

/-- The same bad-event bound in the extended nonnegative arithmetic used by security bounds. -/
theorem ofReal_discreteDistance_bind_left_event_le (p : OracleComp spec α)
    (f g : α → OracleComp spec β) (bad : α → Prop)
    (h : ∀ a, ¬bad a → f a =ᵈ g a) :
    ENNReal.ofReal (discreteDistance (p >>= f) (p >>= g)) ≤ Pr{let x ← p}[bad x] :=
  (ENNReal.ofReal_le_ofReal (discreteDistance_bind_left_event_le p f g bad h)).trans_eq
    (ENNReal.ofReal_toReal (prEvent_ne_top _))

end Oracle

section UntilBad
variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
  [OracleSpec.AnswerMeasure spec'] {α σ : Type}

/-- Good-event agreement and sticky bad events bound the distance of complete simulated states. -/
theorem discreteDistance_simulateQ_run_le_prEvent_bad
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    discreteDistance ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀) ≤
      (Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2]).toReal :=
  letI : MeasurableSpace (α × σ) := ⊤
  ENNReal.toReal_mono (prEvent_ne_top _)
    (OracleComp.ProgramLogic.Relational.measureETVDist_simulateQ_run_le_prEvent_bad
      impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀)

/-- The complete-state identical-until-bad bound in extended nonnegative arithmetic. -/
theorem ofReal_discreteDistance_simulateQ_run_le_prEvent_bad
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    ENNReal.ofReal (discreteDistance ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀)) ≤
      Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  (ENNReal.ofReal_le_ofReal (discreteDistance_simulateQ_run_le_prEvent_bad
    impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀)).trans_eq
      (ENNReal.ofReal_toReal (prEvent_ne_top _))

end UntilBad

end BeaconcryptCore.Computational


/--
info: 'BeaconcryptCore.Computational.discreteDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance

/--
info: 'BeaconcryptCore.Computational.discreteDistance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_nonneg

/--
info: 'BeaconcryptCore.Computational.discreteDistance_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_le_one

/--
info: 'BeaconcryptCore.Computational.discreteDistance_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_self

/--
info: 'BeaconcryptCore.Computational.discreteDistance_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_comm

/--
info: 'BeaconcryptCore.Computational.discreteDistance_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_triangle

/--
info: 'BeaconcryptCore.Computational.discreteDistance_eq_toReal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_eq_toReal

/--
info: 'BeaconcryptCore.Computational.ofReal_discreteDistance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.ofReal_discreteDistance_eq

/--
info: 'BeaconcryptCore.Computational.discreteDistance_map_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_map_le

/--
info: 'BeaconcryptCore.Computational.discreteDistance_bind_right_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_bind_right_le

/--
info: 'BeaconcryptCore.Computational.abs_prEvent_toReal_sub_le_discreteDistance_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.abs_prEvent_toReal_sub_le_discreteDistance_event

/--
info: 'BeaconcryptCore.Computational.prEvent_le_prEvent_add_ofReal_discreteDistance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.prEvent_le_prEvent_add_ofReal_discreteDistance

/--
info: 'BeaconcryptCore.Computational.abs_prEvent_toReal_sub_le_discreteDistance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.abs_prEvent_toReal_sub_le_discreteDistance

/--
info: 'BeaconcryptCore.Computational.abs_evalDist_true_toReal_sub_le_discreteDistance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.abs_evalDist_true_toReal_sub_le_discreteDistance

/--
info: 'BeaconcryptCore.Computational.discreteDistance_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_congr

/--
info: 'BeaconcryptCore.Computational.boolDistance_le_discreteDistance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.boolDistance_le_discreteDistance

/--
info: 'BeaconcryptCore.Computational.discreteDistance_bind_left_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_bind_left_le

/--
info: 'BeaconcryptCore.Computational.discreteDistance_bind_left_le_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_bind_left_le_const

/--
info: 'BeaconcryptCore.Computational.ofReal_discreteDistance_bind_left_le_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.ofReal_discreteDistance_bind_left_le_const

/--
info: 'BeaconcryptCore.Computational.ofReal_discreteDistance_bind_left_le_const'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.ofReal_discreteDistance_bind_left_le_const'

/--
info: 'BeaconcryptCore.Computational.discreteDistance_bind_left_le_const'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_bind_left_le_const'

/--
info: 'BeaconcryptCore.Computational.discreteDistance_bind_left_event_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_bind_left_event_le

/--
info: 'BeaconcryptCore.Computational.ofReal_discreteDistance_bind_left_event_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.ofReal_discreteDistance_bind_left_event_le

/--
info: 'BeaconcryptCore.Computational.discreteDistance_simulateQ_run_le_prEvent_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.discreteDistance_simulateQ_run_le_prEvent_bad

/--
info: 'BeaconcryptCore.Computational.ofReal_discreteDistance_simulateQ_run_le_prEvent_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.ofReal_discreteDistance_simulateQ_run_le_prEvent_bad
