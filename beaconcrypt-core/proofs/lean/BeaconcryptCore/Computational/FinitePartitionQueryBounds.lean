import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exact weighted selective query accounting over a finite partition, retaining arbitrary complete StateT results and all possible reply continuations. -/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.FinitePartitionQueryBounds

def bill {Kind : Type} [Fintype Kind] (cost budget : Kind → Nat) : Nat :=
  ∑ kind, cost kind * budget kind

/-- One query consumes exactly the cost of its own positive budget coordinate. -/
theorem bill_step {Kind : Type} [Fintype Kind] [DecidableEq Kind]
    (cost budget : Kind → Nat) (kind : Kind) (positive : 0 < budget kind) :
    cost kind + bill cost (Function.update budget kind (budget kind - 1)) = bill cost budget := by
  simp only [bill, Function.apply_update (fun k n => cost k * n) budget kind (budget kind - 1),
    Finset.sum_update_of_mem (Finset.mem_univ kind)]
  have split : (∑ k, cost k * budget k) = cost kind * budget kind +
      ∑ k ∈ Finset.univ \ {kind}, cost k * budget k := by
    simpa only [Function.update_eq_self] using Finset.sum_update_of_mem
      (Finset.mem_univ kind) (fun k => cost k * budget k) (cost kind * budget kind)
  rw [split, ← Nat.add_assoc, Nat.add_comm (cost kind), ← Nat.mul_succ,
    Nat.succ_eq_add_one, Nat.sub_add_cancel positive]

/-- Separate selective caps imply one shared structural budget for every possible reply continuation. -/
theorem structural {Kind ι Result : Type} [DecidableEq Kind] {spec : OracleSpec ι}
    (classify : spec.Domain → Kind) (client : OracleComp spec Result) (budget : Kind → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => classify query = kind) (budget kind)) :
    IsQueryBound client budget (fun query current => 0 < current (classify query))
      (fun query current => Function.update current (classify query) (current (classify query) - 1)) := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind query next ih =>
    simp only [isQueryBoundP_query_bind_iff] at bounded
    rw [isQueryBound_query_bind_iff]
    refine ⟨by simpa using (bounded (classify query)).1, fun answer => ih answer _ ?_⟩
    intro kind
    by_cases same : classify query = kind
    · subst kind
      simpa only [Function.update_self, if_true] using (bounded (classify query)).2 answer
    · simpa only [Function.update_of_ne (Ne.symm same), same, if_false] using (bounded kind).2 answer

/-- Exact finite weighted composition retains the arbitrary result and complete interpreted state. -/
theorem weighted_bound {Kind ι κ Result State : Type} [Fintype Kind] [DecidableEq Kind]
    {spec : OracleSpec ι} {target : OracleSpec κ}
    (classify : spec.Domain → Kind) (cost budget : Kind → Nat)
    (impl : QueryImpl spec (StateT State (OracleComp target)))
    (predicate : target.Domain → Prop) [DecidablePred predicate]
    (client : OracleComp spec Result)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => classify query = kind) (budget kind))
    (step : ∀ query state, ((impl query).run state).IsQueryBoundP predicate (cost (classify query)))
    (state : State) :
    ((simulateQ impl client).run state).IsQueryBoundP predicate (∑ kind, cost kind * budget kind) := by
  exact (structural classify client budget bounded).simulateQ_run_of_step
    (combine := Nat.add) (mapBudget := bill cost) (stepBudget := fun query _ => cost (classify query))
    (fun first rest => isQueryBoundP_bind first (fun value _ => rest value))
    (fun query _ state _ => step query state)
    (fun query budget positive => bill_step cost budget (classify query) positive) state

end BeaconcryptCore.Computational.FinitePartitionQueryBounds

/-- info: 'BeaconcryptCore.Computational.FinitePartitionQueryBounds.bill_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.FinitePartitionQueryBounds.bill_step

/-- info: 'BeaconcryptCore.Computational.FinitePartitionQueryBounds.structural' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.FinitePartitionQueryBounds.structural

/-- info: 'BeaconcryptCore.Computational.FinitePartitionQueryBounds.weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.FinitePartitionQueryBounds.weighted_bound
