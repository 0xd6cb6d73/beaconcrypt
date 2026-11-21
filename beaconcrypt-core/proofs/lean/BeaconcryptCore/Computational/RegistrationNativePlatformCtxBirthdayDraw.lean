-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCollision
/-! One shared digest history pays each unordered pair once. The adaptive bound retains every public coin and supports an arbitrary known earlier singleton without resampling its value. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw
open PqxdhRecordFactsCollision (History DrawSpec enabled debit interpreter)
variable {Digest : Type} [SampleableType Digest] [Fintype Digest] [MeasurableSpace Digest]
  [DiscreteMeasurableSpace Digest] [DecidableEq Digest]

def potential (future prior : Nat) : Nat := future * prior + future.choose 2

omit [SampleableType Digest] [Fintype Digest] [MeasurableSpace Digest] [DiscreteMeasurableSpace Digest] [DecidableEq Digest] in
/-- A fresh draw is compared to every prior value, with each unordered pair charged once. -/
theorem potential_step (future prior : Nat) :
    prior + potential future (prior + 1) = potential (future + 1) prior := by
  simp only [potential, Nat.choose_succ_succ, Nat.choose_one_right]
  ring

/-- Every adaptive future digest query has the exact birthday potential, with all interleaved public coins and the complete earlier history retained. -/
theorem run_bound {A : Type} (work : OracleComp (DrawSpec Digest) A) (future : Nat)
    (bounded : work.IsQueryBound (future, 0) enabled debit)
    (before : History Digest) (clean : before.bad = false) :
    𝒟[(fun result : A × History Digest => result.2.bad) <$>
      (simulateQ interpreter work).run before] {true} ≤
      (potential future (before.targets.length + before.ordinary.length) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  induction work using OracleComp.inductionOn generalizing future before with
  | pure value => simp [simulateQ_pure, StateT.run_pure, clean]
  | query_bind query next ih =>
    rw [isQueryBound_query_bind_iff] at bounded
    cases query with
    | inl target => cases target with
      | false => have impossible : 0 < (0 : Nat) := bounded.1; omega
      | true =>
        simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxHybrid.stateT_bind_apply,
          interpreter, StateT.run, map_bind, bind_assoc, pure_bind]
        refine (PqxdhRecordFactsCollision.uniform_bind_list (before.targets ++ before.ordinary) _ {true}
          ((potential (future - 1) (before.targets.length + before.ordinary.length + 1) : ℝ≥0∞) *
            (Fintype.card Digest : ℝ≥0∞)⁻¹) ?_).trans ?_
        · intro digest missed
          have cleanNext : (before.insert true digest).bad = false := by
            simp [History.insert, clean, missed]
          simpa only [StateT.run, History.insert, Bool.true_eq, ↓reduceIte, List.length_cons,
            Nat.add_right_comm] using
            ih digest (future - 1) (bounded.2 digest) (before.insert true digest) cleanNext
        · rw [← add_mul, List.length_append, ← Nat.cast_add]
          apply mul_le_mul (Nat.cast_le.mpr ?_) le_rfl (by positivity) (by positivity)
          have positive : 0 < future := bounded.1
          have remaining : future - 1 + 1 = future := by omega
          exact (potential_step (future - 1) (before.targets.length + before.ordinary.length)).le.trans
            (by rw [remaining])
    | inr coin =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxHybrid.stateT_bind_apply,
        interpreter, StateT.run, map_bind, bind_assoc, pure_bind]
      apply PqxdhRecordFactsCollision.bind_le
      intro value
      simpa only [StateT.run] using ih value future (bounded.2 value) before clean

/-- An arbitrary reached earlier singleton is retained, with no empty-cache replacement or independence assumption on its value. -/
theorem singleton_bound {A : Type} (work : OracleComp (DrawSpec Digest) A) (future : Nat)
    (bounded : work.IsQueryBound (future, 0) enabled debit) (digest : Digest) :
    𝒟[(fun result : A × History Digest => result.2.bad) <$>
      (simulateQ interpreter work).run ⟨[digest], [], false⟩] {true} ≤
      ((future + 1).choose 2 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have same : potential future 1 = (future + 1).choose 2 := by
    simp only [potential, Nat.mul_one, Nat.choose_succ_succ, Nat.choose_one_right]
  simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero, same] using
    run_bound work future bounded ⟨[digest], [], false⟩ rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw.potential_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw.potential_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw.run_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw.singleton_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw.singleton_bound
