import BeaconcryptCore.Computational.VCVioForwardEvalDist
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
# Transitional bridge between the deprecated and the forward probability vocabulary (VCVio pin 98dc1089)

This is the only project module allowed to contain the deprecated VCVio probability syntax (`Pr[= x | mx]`, `Pr[p | mx]`, `𝒮[mx]`), each use under an explicit `set_option linter.deprecated false in`. It relates the deprecated forms to the forward vocabulary of `VCVioForwardEvalDist`:

* `Pr[= x | mx] = Pr{let y ← mx}[y = x]` and `Pr[p | mx] = Pr{let x ← mx}[p x]`, with no measurable-space hypothesis on the output type;
* `𝒮[mx] = 𝒮[my] ↔ EvalDistEq mx my`;
* the measure forms `Pr[= x | mx] = 𝒟[mx] {x}` (measurable singletons) and `Pr[p | mx] = 𝒟[mx] {x | p x}` (discrete outputs).

The primary bridges are stated for `ProbComp`, so that the pin's `DiscreteEvalDistCompatible` link, which upstream removes, stays inside the bridge's proofs; versions for any monad with that link (suffix `_of_compatible`) and for oracle computations over a variable uniform specification (prefix `oracleComp_`) cover the remaining cases. Migrated proofs use these lemmas, by name in `rw` or `simp only`, where a statement outside the current migration stage, or a VCVio lemma, is still stated in the deprecated form; every such use names `VCVioLegacy`, so the remaining uses are greppable and counted. The module contains lemmas only: no notation, tactic, command or other metaprogram. The migration's statement certificates and the generator of its transitional twins are scratch tooling outside the build, which uses these lemmas. The module is transitional: it is deleted at the VCVio upgrade, after which no deprecated form exists. Nothing here is assumed: every bridge is proved from the pinned VCVio.
-/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

universe v v'

namespace BeaconcryptCore.VCVioLegacy

/-! ## Bridges for an arbitrary monad with the pin's discrete compatibility

These are stated for every monad with the pinned semantic classes and the pin's `DiscreteEvalDistCompatible` link, which upstream removes. A proof that uses them carries that instance in its term, so migrated proofs use the `ProbComp` and oracle forms below, which keep the link inside the bridge. -/

set_option linter.deprecated false in
/-- The deprecated output probability is the singleton mass of the output measure, for outputs with measurable singletons (any compatible monad). -/
theorem probOutput_eq_evalDist_singleton_of_compatible {m : Type → Type v} [MonadLiftT m SPMF]
    [EvalDistSemantics m] [DiscreteEvalDistCompatible m] {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (mx : m α) (x : α) : Pr[= x | mx] = 𝒟[mx] {x} :=
  (evalDist_apply_singleton mx x).symm

set_option linter.deprecated false in
/-- The deprecated event probability is the mass of the event under the output measure, for discrete outputs (any compatible monad). -/
theorem probEvent_eq_evalDist_setOf_of_compatible {m : Type → Type v} [MonadLiftT m SPMF]
    [EvalDistSemantics m] [DiscreteEvalDistCompatible m] {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (mx : m α) (p : α → Prop) : Pr[p | mx] = 𝒟[mx] {x | p x} :=
  (evalDist_apply_setOf mx p).symm

set_option linter.deprecated false in
/-- The deprecated output probability is the forward singleton event (any compatible monad); no measurable space on the output is needed. -/
theorem probOutput_eq_prEvent_of_compatible {m : Type → Type v} [Monad m] [LawfulMonad m]
    [MonadLiftT m SPMF] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [DiscreteEvalDistCompatible m] {α : Type} (mx : m α) (x : α) :
    Pr[= x | mx] = Pr{let y ← mx}[y = x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton mx x, probOutput_eq_evalDist_singleton_of_compatible]

set_option linter.deprecated false in
/-- The deprecated event probability is the forward event (any compatible monad); no measurable space on the output is needed. -/
theorem probEvent_eq_prEvent_of_compatible {m : Type → Type v} [Monad m] [LawfulMonad m]
    [MonadLiftT m SPMF] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [DiscreteEvalDistCompatible m] {α : Type} (mx : m α) (p : α → Prop) :
    Pr[p | mx] = Pr{let x ← mx}[p x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete mx p, probEvent_eq_evalDist_setOf_of_compatible]

set_option linter.deprecated false in
/-- Equal deprecated output distributions are equality in distribution (any two compatible monads); no measurable space on the output is needed. -/
theorem evalSPMF_eq_iff_evalDistEq_of_compatible {m : Type → Type v} {m' : Type → Type v'}
    [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m'] [MonadLiftT m SPMF]
    [MonadLiftT m' SPMF] [EvalDistSemantics m] [EvalDistSemantics m'] [LawfulEvalDistSemantics m]
    [LawfulEvalDistSemantics m'] [DiscreteEvalDistCompatible m] [DiscreteEvalDistCompatible m']
    {α : Type} (mx : m α) (my : m' α) : 𝒮[mx] = 𝒮[my] ↔ EvalDistEq mx my := by
  constructor
  · intro h p
    rw [← probEvent_eq_prEvent_of_compatible, ← probEvent_eq_prEvent_of_compatible]
    unfold probEvent
    rw [h]
  · intro h
    refine evalSPMF_ext fun x ↦ ?_
    rw [probOutput_eq_prEvent_of_compatible, probOutput_eq_prEvent_of_compatible]
    exact h (· = x)

/-! ## Bridges for `ProbComp`

The primary bridges. Their statements use `ProbComp`'s own instances, so they rewrite the terms of project statements directly, and the compatibility link stays inside their proofs. -/

set_option linter.deprecated false in
/-- The deprecated output probability of a probabilistic computation is the forward singleton event. -/
theorem probOutput_eq_prEvent {α : Type} (mx : ProbComp α) (x : α) :
    Pr[= x | mx] = Pr{let y ← mx}[y = x] :=
  probOutput_eq_prEvent_of_compatible mx x

set_option linter.deprecated false in
/-- The deprecated event probability of a probabilistic computation is the forward event. -/
theorem probEvent_eq_prEvent {α : Type} (mx : ProbComp α) (p : α → Prop) :
    Pr[p | mx] = Pr{let x ← mx}[p x] :=
  probEvent_eq_prEvent_of_compatible mx p

set_option linter.deprecated false in
/-- Equal deprecated output distributions of probabilistic computations are equality in distribution. -/
theorem evalSPMF_eq_iff_evalDistEq {α : Type} (mx my : ProbComp α) :
    𝒮[mx] = 𝒮[my] ↔ EvalDistEq mx my :=
  evalSPMF_eq_iff_evalDistEq_of_compatible mx my

set_option linter.deprecated false in
/-- The deprecated output probability of a probabilistic computation is the singleton mass of its output measure. -/
theorem probOutput_eq_evalDist_singleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : ProbComp α) (x : α) : Pr[= x | mx] = 𝒟[mx] {x} :=
  probOutput_eq_evalDist_singleton_of_compatible mx x

set_option linter.deprecated false in
/-- The singleton mass of a probabilistic computation's output measure is the deprecated output probability (the reverse bridge, for proofs whose statement is still deprecated). -/
theorem evalDist_singleton_eq_probOutput {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : ProbComp α) (x : α) : 𝒟[mx] {x} = Pr[= x | mx] :=
  (probOutput_eq_evalDist_singleton_of_compatible mx x).symm

set_option linter.deprecated false in
/-- The deprecated event probability of a probabilistic computation is the mass of the event, for discrete outputs. -/
theorem probEvent_eq_evalDist_setOf {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : ProbComp α) (p : α → Prop) : Pr[p | mx] = 𝒟[mx] {x | p x} :=
  probEvent_eq_evalDist_setOf_of_compatible mx p

/-! ## Bridges for oracle computations with uniform answers

For oracle computations over a specification with uniform answers that is a variable with an `[IsUniformSpec spec]` hypothesis. Their statements use the semantics available in that context, the pin's `SPMF` adapter; for a concrete specification with measurable answer types, whose computations use VCVio's native free-monad semantics, use the bridges for any compatible monad instead. -/

set_option linter.deprecated false in
/-- The deprecated output probability of an oracle computation with uniform answers is the forward singleton event. -/
theorem oracleComp_probOutput_eq_prEvent {ι : Type} {spec : OracleSpec ι} [spec.IsUniformSpec]
    {α : Type} (mx : OracleComp spec α) (x : α) : Pr[= x | mx] = Pr{let y ← mx}[y = x] :=
  probOutput_eq_prEvent_of_compatible mx x

set_option linter.deprecated false in
/-- The deprecated event probability of an oracle computation with uniform answers is the forward event. -/
theorem oracleComp_probEvent_eq_prEvent {ι : Type} {spec : OracleSpec ι} [spec.IsUniformSpec]
    {α : Type} (mx : OracleComp spec α) (p : α → Prop) : Pr[p | mx] = Pr{let x ← mx}[p x] :=
  probEvent_eq_prEvent_of_compatible mx p

set_option linter.deprecated false in
/-- Equal deprecated output distributions of oracle computations with uniform answers are equality in distribution. -/
theorem oracleComp_evalSPMF_eq_iff_evalDistEq {ι : Type} {spec : OracleSpec ι} [spec.IsUniformSpec]
    {α : Type} (mx my : OracleComp spec α) : 𝒮[mx] = 𝒮[my] ↔ EvalDistEq mx my :=
  evalSPMF_eq_iff_evalDistEq_of_compatible mx my

end BeaconcryptCore.VCVioLegacy

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton

/--
info: 'BeaconcryptCore.VCVioLegacy.evalDist_singleton_eq_probOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.evalDist_singleton_eq_probOutput

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf

/--
info: 'BeaconcryptCore.VCVioLegacy.oracleComp_probOutput_eq_prEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.oracleComp_probOutput_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.oracleComp_probEvent_eq_prEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.oracleComp_probEvent_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.oracleComp_evalSPMF_eq_iff_evalDistEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.oracleComp_evalSPMF_eq_iff_evalDistEq
