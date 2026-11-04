-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts

/-! Weighted resource transport through the actual two-level native owner/environment state. The complete state and every typed failure continuation are retained; these local syntax lemmas only assemble proved primitive bills. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedContext
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono weighted_indicator weighted_simulate)
variable {ι κ S T X Y : Type} {source : OracleSpec ι} {target : OracleSpec κ}

/-- A literal typed query pays exactly its supplied nonnegative cost. -/
theorem query_bound (cost : source.Domain → Nat) (query : source.Domain) :
    Weighted cost (source.query query : OracleComp source _) (cost query) := by
  simp [Weighted]

/-- Repacking a return value changes no resource query. -/
theorem map_bound (cost : source.Domain → Nat) (work : OracleComp source X) (f : X → Y)
    (count : Nat) (bounded : Weighted cost work count) : Weighted cost (f <$> work) count := by
  simpa only [bind_pure_comp, Nat.add_zero] using
    weighted_bind cost work (fun x => pure (f x)) count 0 bounded (fun _ => by trivial)

/-- Two nested actual source state coordinates retain the same additive literal bill. -/
theorem run_bound (sourceCost : source.Domain → Nat) (targetCost : target.Domain → Nat)
    (impl : QueryImpl source (StateT S (StateT T (OracleComp target))))
    (work : OracleComp source X) (count : Nat) (first : S) (second : T)
    (bounded : Weighted sourceCost work count)
    (step : ∀ query first second, Weighted targetCost (((impl query).run first).run second) (sourceCost query)) :
    Weighted targetCost (((simulateQ impl work).run first).run second) count := by
  induction work using OracleComp.inductionOn generalizing first second count with
  | pure value => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact weighted_mono _ _ _ _ (weighted_bind targetCost _ _ _ _ (step query first second)
        (fun result => ih result.1.1 (first := result.1.2) (second := result.2) (count := count - sourceCost query) (bounded.2 result.1.1))) (by omega)

/-- One direct probability sampler pays its exact constant per-draw weight. -/
theorem probability_bound (cost : ℕ → Nat) (coefficient : Nat) (same : ∀ query, cost query = coefficient)
    (work : ProbComp X) (count : Nat) (bounded : work.IsTotalQueryBound count) :
    Weighted cost work (coefficient * count) := by
  have weighted := weighted_indicator (fun _ => True) coefficient work count ((isQueryBoundP_true_iff _ _).mpr bounded)
  convert weighted using 1
  funext query
  simp only [same, ite_true]

end BeaconcryptCore.Computational.RegistrationNativeWeightedContext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedContext.query_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedContext.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedContext.map_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedContext.map_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedContext.run_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedContext.run_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedContext.probability_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedContext.probability_bound
