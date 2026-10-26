/-
Copyright (c) 2026 Quang Dao. All rights reserved.
The private support and pointwise induction helpers are adapted from VCVio's
ProgramLogic/Relational/SimulateQ.lean, released under the Apache 2.0 license
in that dependency's LICENSE. Changes: local names and public arbitrary-initial
output/event corollaries.
-/

import VCVio.ProgramLogic.Relational.SimulateQ
import BeaconcryptCore.Computational.VCVioForwardOracleComp
import BeaconcryptCore.Computational.DiscreteDistance

/-!
Exact agreement of arbitrary events restricted to the original good final state. Both simulations retain the same complete result/state type, and their common initial bad flag may already be set. The only premises are the existing non-bad one-step output agreement and sticky bad flags. No probability bound on disclosures or conditioning on freshness is introduced. The private support and pointwise inductions reproduce the checked VCVio heterogeneous identical-until-bad argument because its corresponding output-good helper is private; no VCVio source is modified.

The statements use native event probabilities under an arbitrary specification with uniform answer measures. The inductive proofs use VCVio's sums of singleton event probabilities directly; they require no legacy probability adapter or measurable structure on the complete result and state.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.StatefulGoodEvent
variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [UniformAnswerMeasure spec']
variable {α σ : Type}

omit [UniformAnswerMeasure spec'] in
private lemma support_bad
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_mono : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (p : σ × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((simulateQ impl oa).run p), z.2.2 = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hp
  | query_bind t cont ih =>
      intro z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion,
        exists_prop] at hz
      obtain ⟨⟨u, p'⟩, h_mem, h_z⟩ := hz
      have hp' : p'.2 = true := h_mono t p hp (u, p') h_mem
      exact ih u p' hp' z h_z

private lemma output_bad_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_mono : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (p : σ × Bool) (hp : p.2 = true) (x : α) (s : σ) :
    Pr{let y ← (simulateQ impl oa).run p}[y = (x, (s, false))] = 0 := by
  refine prEvent_eq_zero_of_not_mem_support _ fun h => ?_
  simpa using support_bad impl h_mono oa p hp (x, (s, false)) h

private lemma output_good_false
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr{let x ← (impl₁ t).run (s, false)}[x = (u, (s', false))] =
        Pr{let x ← (impl₂ t).run (s, false)}[x = (u, (s', false))])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) :
    Pr{let y ← (simulateQ impl₁ oa).run (s₀, false)}[y = (x, (s, false))] =
      Pr{let y ← (simulateQ impl₂ oa).run (s₀, false)}[y = (x, (s, false))] := by
  let : ∀ t, Finite (spec'.Range t) := fun t => UniformAnswerMeasure.finite_range t
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    simp only [simulateQ_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
    refine tsum_congr ?_
    rintro ⟨u, ⟨s', b⟩⟩
    cases b with
    | true =>
      have h₁ := output_bad_zero impl₁ h_mono₁ (oa u) (s', true) rfl x s
      have h₂ := output_bad_zero impl₂ h_mono₂ (oa u) (s', true) rfl x s
      simp [h₁, h₂]
    | false =>
      rw [h_agree_good t s₀ u s', ih u s']

/-- Every complete good output has the same unconditioned probability, including when the common initial flag is already bad. -/
theorem output_good
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr{let x ← (impl₁ t).run (s, false)}[x = (u, (s', false))] =
        Pr{let x ← (impl₂ t).run (s, false)}[x = (u, (s', false))])
    (sticky₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (sticky₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (client : OracleComp spec α) (initial : σ × Bool) (value : α) (state : σ) :
    Pr{let x ← (simulateQ impl₁ client).run initial}[x = (value, (state, false))] =
      Pr{let x ← (simulateQ impl₂ client).run initial}[x = (value, (state, false))] := by
  cases initial with
  | mk s flag =>
    cases flag with
    | false => exact output_good_false impl₁ impl₂ agree_good sticky₁ sticky₂ client s value state
    | true => rw [output_bad_zero impl₁ sticky₁ client (s, true) rfl,
        output_bad_zero impl₂ sticky₂ client (s, true) rfl]

/-- An arbitrary event restricted to the original good final flag has exactly the same unconditioned probability in both complete simulations. -/
theorem event_good
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr{let x ← (impl₁ t).run (s, false)}[x = (u, (s', false))] =
        Pr{let x ← (impl₂ t).run (s, false)}[x = (u, (s', false))])
    (sticky₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (sticky₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (client : OracleComp spec α) (initial : σ × Bool) (event : α × σ × Bool → Prop) :
    Pr{let result ← (simulateQ impl₁ client).run initial}[event result ∧ result.2.2 = false] =
    Pr{let result ← (simulateQ impl₂ client).run initial}[event result ∧ result.2.2 = false] := by
  let : ∀ t, Finite (spec'.Range t) := fun t => UniformAnswerMeasure.finite_range t
  classical
  have good := output_good impl₁ impl₂ agree_good sticky₁ sticky₂ client initial
  rw [prEvent_eq_tsum_ite, prEvent_eq_tsum_ite]
  refine tsum_congr ?_
  rintro ⟨value, state, flag⟩
  cases flag <;> simp [good value state]

/-- Complete-output real distance is bounded by the original final bad-flag probability. -/
theorem distance_le_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr{let x ← (impl₁ t).run (s, false)}[x = (u, (s', false))] =
        Pr{let x ← (impl₂ t).run (s, false)}[x = (u, (s', false))])
    (sticky₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (sticky₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (client : OracleComp spec α) (initial : σ × Bool) :
    discreteDistance ((simulateQ impl₁ client).run initial)
        ((simulateQ impl₂ client).run initial) ≤
      (Pr{let result ← (simulateQ impl₁ client).run initial}[result.2.2 = true]).toReal := by
  let : ∀ t, Finite (spec'.Range t) := fun t => UniformAnswerMeasure.finite_range t
  exact discreteDistance_simulateQ_run_le_prEvent_bad
    impl₁ impl₂ (fun state => state.2 = true)
    (fun query state hgood q => by
      rcases state with ⟨state, flag⟩
      have hflag : flag = false := by simpa using hgood
      subst flag
      exact OracleComp.ProgramLogic.Relational.prEvent_and_not_flag_eq_of_forall_prEvent_eq
        (agree_good query state) q)
    sticky₁ sticky₂ client initial

/-- Sticky simulations with the same complete good outputs have the same final bad-flag probability. -/
theorem bad_probability_eq
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr{let x ← (impl₁ t).run (s, false)}[x = (u, (s', false))] =
        Pr{let x ← (impl₂ t).run (s, false)}[x = (u, (s', false))])
    (sticky₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (sticky₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (client : OracleComp spec α) (initial : σ × Bool) :
    Pr{let result ← (simulateQ impl₁ client).run initial}[result.2.2 = true] =
      Pr{let result ← (simulateQ impl₂ client).run initial}[result.2.2 = true] := by
  let : ∀ t, Finite (spec'.Range t) := fun t => UniformAnswerMeasure.finite_range t
  exact OracleComp.ProgramLogic.Relational.prEvent_simulateQ_run_bad_eq
    impl₁ impl₂ (fun state => state.2 = true)
    (fun query state hgood q => by
      rcases state with ⟨state, flag⟩
      have hflag : flag = false := by simpa using hgood
      subst flag
      exact OracleComp.ProgramLogic.Relational.prEvent_and_not_flag_eq_of_forall_prEvent_eq
        (agree_good query state) q)
    sticky₁ sticky₂ client initial

end BeaconcryptCore.Computational.StatefulGoodEvent

/--
info: 'BeaconcryptCore.Computational.StatefulGoodEvent.output_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.StatefulGoodEvent.output_good

/--
info: 'BeaconcryptCore.Computational.StatefulGoodEvent.event_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.StatefulGoodEvent.event_good

/--
info: 'BeaconcryptCore.Computational.StatefulGoodEvent.distance_le_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.StatefulGoodEvent.distance_le_bad

/--
info: 'BeaconcryptCore.Computational.StatefulGoodEvent.bad_probability_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.StatefulGoodEvent.bad_probability_eq
