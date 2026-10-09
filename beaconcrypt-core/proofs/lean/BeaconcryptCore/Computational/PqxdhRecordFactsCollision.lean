-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFresh

/-!
# Adaptive uniform-digest collision accounting

This module develops statistical counting tools for the private commitment and shared random-oracle outputs of the record worlds. Its generic sampling games are information-theoretic tools, not additional cryptographic contracts; their connection to the actual record interpreters is a separate obligation.
-/

open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsCollision

variable {α : Type} [SampleableType α] [Fintype α] [MeasurableSpace α]
  [DiscreteMeasurableSpace α]

/-- A fresh uniform draw hits a fixed finite candidate set with exactly its cardinality divided by the range size. -/
theorem uniform_finset (candidates : Finset α) :
    𝒟[($ᵗ α : ProbComp α)] (candidates : Set α) =
      (candidates.card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.evalDist_uniformSample, uniformOn_univ]
  rw [Measure.count_apply_finset, div_eq_mul_inv]

/-- Repeated candidates can only reduce the chance of a fresh uniform hit. -/
theorem uniform_list [DecidableEq α] (candidates : List α) :
    𝒟[($ᵗ α : ProbComp α)] {value | value ∈ candidates} ≤
      (candidates.length : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  have exactSet := uniform_finset candidates.toFinset
  simpa only [List.coe_toFinset] using exactSet.le.trans (mul_le_mul (Nat.cast_le.mpr candidates.toFinset_card_le) le_rfl (by positivity) (by positivity))

omit [SampleableType α] [Fintype α] in
/-- A continuation bounded away from a bad prefix costs that prefix probability plus its conditional bound. Both computations retain every adaptive draw. -/
theorem bind_le_bad_add {β : Type} [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (work : ProbComp α) (next : α → ProbComp β) (bad : Set α) (event : Set β)
    (cap : ℝ≥0∞) (bounded : ∀ value, value ∉ bad → 𝒟[next value] event ≤ cap) :
    𝒟[work >>= next] event ≤ 𝒟[work] bad + cap := by
  rw [evalDist_bind_of_discrete, Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable)]
  refine (lintegral_mono (g := fun value => bad.indicator (fun _ => (1 : ℝ≥0∞)) value + cap) ?_).trans ?_
  · intro value
    by_cases hit : value ∈ bad
    · simpa only [Set.indicator_of_mem hit] using
        ((measure_mono (Set.subset_univ event)).trans (evalDist_apply_univ_le_one (next value))).trans
          (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ cap from bot_le))
    · simpa only [Set.indicator_of_notMem hit, zero_add] using bounded value hit
  · simp only [lintegral_add_left Measurable.of_discrete, lintegral_const,
      OracleComp.evalDist_apply_univ_eq_one, mul_one]
    exact add_le_add (lintegral_indicator_one_le bad) le_rfl

/-- A uniform-draw continuation can fail only on the candidate list or through its explicit off-list bound. -/
theorem uniform_bind_list [DecidableEq α] {β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] (candidates : List α) (next : α → ProbComp β)
    (event : Set β) (cap : ℝ≥0∞)
    (bounded : ∀ value, value ∉ candidates → 𝒟[next value] event ≤ cap) :
    𝒟[($ᵗ α : ProbComp α) >>= next] event ≤
      (candidates.length : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ + cap := by
  exact (bind_le_bad_add _ next {value | value ∈ candidates} event cap bounded).trans
    (add_le_add (uniform_list candidates) le_rfl)

omit [SampleableType α] [Fintype α] in
/-- Averaging a uniform continuation bound retains that bound, without assuming a fixed prefix. -/
theorem bind_le {β : Type} [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (work : ProbComp α) (next : α → ProbComp β) (event : Set β)
    (cap : ℝ≥0∞) (bounded : ∀ value, 𝒟[next value] event ≤ cap) :
    𝒟[work >>= next] event ≤ cap := by
  simpa using bind_le_bad_add work next ∅ event cap (fun value _ => bounded value)

abbrev DigestSpec (α : Type) : OracleSpec Bool := fun _ => α

/-- Two independently counted digest draws, plus the client's arbitrary finite public coins. The Boolean tag is chosen before the fresh digest is returned: true marks a target commitment and false an ordinary hash output. -/
abbrev DrawSpec (α : Type) : OracleSpec (Bool ⊕ unifSpec.Domain) :=
  DigestSpec α + unifSpec

/-- The full chronological value lists and an absorbing collision flag. Ordinary-to-ordinary equality alone is not a bad event. -/
structure History (α : Type) where
  targets : List α
  ordinary : List α
  bad : Bool

def History.empty : History α := ⟨[], [], false⟩

/-- Add the actual new digest and charge exactly collisions involving a target draw. -/
def History.insert [DecidableEq α] (state : History α) (target : Bool) (value : α) : History α :=
  if target then
    ⟨value :: state.targets, state.ordinary,
      state.bad || decide (value ∈ state.targets ++ state.ordinary)⟩
  else
    ⟨state.targets, value :: state.ordinary,
      state.bad || decide (value ∈ state.targets)⟩

/-- Literal independent uniform digest service; coin replies and the complete history are retained. This is a statistical experiment, not a cryptographic assumption. -/
noncomputable def interpreter [DecidableEq α] :
    QueryImpl (DrawSpec α) (StateT (History α) ProbComp)
  | .inl target => fun state => do
      let value ← $ᵗ α
      pure (value, state.insert target value)
  | .inr coin => fun state => do
      let value ← unifSpec.query coin
      pure (value, state)

/-- Counts of remaining target and ordinary draws. Coins have their own source/reduction bill and do not add a digest-collision opportunity. -/
def enabled : (Bool ⊕ unifSpec.Domain) → Nat × Nat → Prop
  | .inl true, budget => 0 < budget.1
  | .inl false, budget => 0 < budget.2
  | .inr _, _ => True

def debit : (Bool ⊕ unifSpec.Domain) → Nat × Nat → Nat × Nat
  | .inl true, budget => (budget.1 - 1, budget.2)
  | .inl false, budget => (budget.1, budget.2 - 1)
  | .inr _, budget => budget

/-- Remaining collision opportunities. At empty history the value is `targets * (targets + ordinary)`; the asymmetric potential charges each cross-pool pair once. -/
def potential (targets ordinary priorTargets priorOrdinary : Nat) : Nat :=
  targets * (priorTargets + priorOrdinary + targets + ordinary) + ordinary * priorTargets

/-- A target draw pays for comparison to all prior values and the remaining potential. -/
theorem target_potential (targets ordinary priorTargets priorOrdinary : Nat) :
    priorTargets + priorOrdinary + potential targets ordinary (priorTargets + 1) priorOrdinary ≤
      potential (targets + 1) ordinary priorTargets priorOrdinary := by
  unfold potential
  nlinarith

/-- An ordinary draw compares only with earlier targets, and charges each cross-pool pair once. -/
theorem ordinary_potential (targets ordinary priorTargets priorOrdinary : Nat) :
    priorTargets + potential targets ordinary priorTargets (priorOrdinary + 1) =
      potential targets (ordinary + 1) priorTargets priorOrdinary := by
  simp [potential, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Adaptive target/ordinary collision bound from a clean history, with separate all-reply query caps and arbitrary intervening coins. This theorem concerns the explicit independent-draw interpreter above; source correspondence remains required. -/
theorem run_bound [DecidableEq α] {X : Type} (client : OracleComp (DrawSpec α) X)
    (targets ordinary : Nat) (bounded : client.IsQueryBound (targets, ordinary) enabled debit)
    (state : History α) (clean : state.bad = false) :
    𝒟[(fun result : X × History α => result.2.bad) <$>
      (simulateQ (interpreter (α := α)) client).run state] {true} ≤
      (potential targets ordinary state.targets.length state.ordinary.length : ℝ≥0∞) *
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
  induction client using OracleComp.inductionOn generalizing targets ordinary state with
  | pure value =>
    simp [simulateQ_pure, StateT.run_pure, clean]
  | query_bind query next ih =>
    simp only [isQueryBound_query_bind_iff] at bounded
    cases query with
    | inl target =>
      cases target with
      | true =>
        simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxHybrid.stateT_bind_apply, interpreter,
          StateT.run, map_bind, bind_assoc, pure_bind]
        refine (uniform_bind_list (state.targets ++ state.ordinary) _ {true}
          ((potential (targets - 1) ordinary (state.targets.length + 1) state.ordinary.length : ℝ≥0∞) *
            (Fintype.card α : ℝ≥0∞)⁻¹) ?_).trans ?_
        · intro value missed
          have cleanNext : (state.insert true value).bad = false := by
            simp [History.insert, clean, missed]
          simpa only [StateT.run, History.insert, Bool.true_eq, ↓reduceIte, List.length_cons] using
            ih value (targets - 1) ordinary (bounded.2 value) (state.insert true value) cleanNext
        · rw [← add_mul, List.length_append, ← Nat.cast_add]
          apply mul_le_mul (Nat.cast_le.mpr ?_) le_rfl (by positivity) (by positivity)
          have positive : 0 < targets := bounded.1
          have remaining : targets - 1 + 1 = targets := by omega
          simpa only [remaining] using target_potential (targets - 1) ordinary state.targets.length state.ordinary.length
      | false =>
        simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxHybrid.stateT_bind_apply, interpreter,
          StateT.run, map_bind, bind_assoc, pure_bind]
        refine (uniform_bind_list state.targets _ {true}
          ((potential targets (ordinary - 1) state.targets.length (state.ordinary.length + 1) : ℝ≥0∞) *
            (Fintype.card α : ℝ≥0∞)⁻¹) ?_).trans ?_
        · intro value missed
          have cleanNext : (state.insert false value).bad = false := by
            simp [History.insert, clean, missed]
          simpa only [StateT.run, History.insert, Bool.false_eq_true, ↓reduceIte, List.length_cons] using
            ih value targets (ordinary - 1) (bounded.2 value) (state.insert false value) cleanNext
        · rw [← add_mul, ← Nat.cast_add]
          apply mul_le_mul (Nat.cast_le.mpr ?_) le_rfl (by positivity) (by positivity)
          have positive : 0 < ordinary := bounded.1
          have remaining : ordinary - 1 + 1 = ordinary := by omega
          simpa only [remaining] using (ordinary_potential targets (ordinary - 1) state.targets.length state.ordinary.length).le
    | inr coin =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxHybrid.stateT_bind_apply, interpreter,
        StateT.run, map_bind, bind_assoc, pure_bind]
      apply bind_le
      intro value
      simpa only [StateT.run] using ih value targets ordinary (bounded.2 value) state clean

/-- From the empty history, adaptive collisions involving target draws cost `S * (S + H)` over the digest range; ordinary-to-ordinary collisions are not charged. -/
theorem empty_bound [DecidableEq α] {X : Type} (client : OracleComp (DrawSpec α) X)
    (targets ordinary : Nat) (bounded : client.IsQueryBound (targets, ordinary) enabled debit) :
    𝒟[(fun result : X × History α => result.2.bad) <$>
      (simulateQ (interpreter (α := α)) client).run History.empty] {true} ≤
      ((targets * (targets + ordinary) : Nat) : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simpa only [History.empty, potential, List.length_nil, Nat.add_zero, Nat.zero_add,
    Nat.mul_zero] using run_bound client targets ordinary bounded History.empty rfl

/-- The same statistical game at the exact 512-bit CTX digest type. This does not by itself identify the production binding event with a digest collision. -/
theorem ctxDigest_bound {X : Type} (client : OracleComp (DrawSpec CtxRomAuth.CtxDigest) X)
    (targets ordinary : Nat) (bounded : client.IsQueryBound (targets, ordinary) enabled debit) :
    𝒟[(fun result : X × History CtxRomAuth.CtxDigest => result.2.bad) <$>
      (simulateQ interpreter client).run History.empty] {true} ≤
      ((targets * (targets + ordinary) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  let _ : MeasurableSpace CtxRomAuth.CtxDigest := ⊤
  let _ : DiscreteMeasurableSpace CtxRomAuth.CtxDigest := ⟨fun _ => by simp⟩
  simpa only [CtxRomAuth.ctxDigest_card, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using
    empty_bound client targets ordinary bounded

end BeaconcryptCore.Computational.PqxdhRecordFactsCollision

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.uniform_finset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.uniform_finset

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.uniform_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.uniform_list

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.bind_le_bad_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.bind_le_bad_add

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.uniform_bind_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.uniform_bind_list

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.bind_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.bind_le

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.target_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.target_potential

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.ordinary_potential' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.ordinary_potential

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.run_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.empty_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.empty_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollision.ctxDigest_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollision.ctxDigest_bound
