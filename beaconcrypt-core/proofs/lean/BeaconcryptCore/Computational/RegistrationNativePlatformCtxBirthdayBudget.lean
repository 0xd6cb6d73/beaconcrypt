-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler
/-! Every physical CTX miss consumes one hash-query allowance. Cache hits keep that allowance for the statistical compiler; actual public coin calls remain unchanged. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBudget
open RegistrationNativePlatformCtxBackend (Spec State)
open RegistrationNativePlatformCtxBirthdayCompiler (compiler)
open PqxdhRecordFactsCollision (enabled debit)
variable {A : Type}

def IsHash : Spec.Domain → Prop
  | .inl _ => True
  | .inr _ => False
instance : DecidablePred IsHash := fun query => by cases query <;> simp only [IsHash] <;> infer_instance

/-- The literal counted compiler cannot create more digest draws than actual hash calls, through every possible adaptive reply and cache alias. -/
theorem compiler_bound (work : OracleComp Spec A) (future : Nat)
    (bounded : work.IsQueryBoundP IsHash future) (before : State) :
    ((simulateQ compiler work).run before).IsQueryBound (future, 0) enabled debit := by
  induction work using OracleComp.inductionOn generalizing future before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    cases query with
    | inl bytes =>
      simp only [IsHash, not_true_eq_false, false_or, ite_true] at bounded
      cases found : before.1 ((), bytes) with
      | none =>
        simp only [compiler, StateT.run, found, bind_assoc, pure_bind, isQueryBound_query_bind_iff]
        exact ⟨bounded.1, fun digest => ih (digest, 64) (future - 1) (bounded.2 (digest, 64))
          (before.1.cacheQuery ((), bytes) digest, before.2 ++ [bytes])⟩
      | some digest =>
        simp only [compiler, StateT.run, found, pure_bind]
        apply PqxdhRecordFactsCollisionOracle.draw_budget_mono _ (future - 1, 0) (future, 0) ⟨Nat.sub_le _ _, le_rfl⟩
        exact ih (digest, 0) (future - 1) (bounded.2 (digest, 0)) (before.1, before.2 ++ [bytes])
    | inr query =>
      simp only [IsHash, not_false_eq_true, true_or, ite_false] at bounded
      simp only [compiler, StateT.run, bind_assoc, pure_bind, isQueryBound_query_bind_iff]
      exact ⟨trivial, fun reply => ih reply future (bounded.2 reply) before⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBudget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBudget.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBudget.compiler_bound
