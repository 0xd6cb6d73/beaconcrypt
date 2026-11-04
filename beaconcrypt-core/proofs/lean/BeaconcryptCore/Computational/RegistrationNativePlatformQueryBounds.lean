-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety
/-! Predicate query budgets compose through the actual two mutable state layers. A counted source request costs at most one target request, and every uncounted source request costs zero on every reply and poststate. -/
open CoreModels Aeneas OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds
variable {I J State Platform Value : Type} {spec : OracleSpec I} {target : OracleSpec J}

theorem simulate_bound
    (predicate : I → Prop) [DecidablePred predicate]
    (counted : J → Prop) [DecidablePred counted]
    (handler : QueryImpl spec (StateT State (StateT Platform (OracleComp target))))
    (steps : ∀ query native platform,
      (((handler query).run native).run platform).IsQueryBoundP counted (if predicate query then 1 else 0))
    (work : OracleComp spec Value) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap)
    (before : State) (previous : Platform) :
    (((simulateQ handler work).run before).run previous).IsQueryBoundP counted cap := by
  induction work using OracleComp.inductionOn generalizing cap before previous with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_bind]
      have total : (if predicate query then 1 else 0) + (if predicate query then cap - 1 else cap) = cap := by
        by_cases condition : predicate query
        · have positive := bounded.1.resolve_left (not_not_intro condition)
          simp only [condition, ite_true]
          omega
        · simp only [condition, ite_false, Nat.zero_add]
      simpa only [total] using isQueryBoundP_bind (steps query before previous)
        (fun result _ => ih result.1.1 _ (bounded.2 result.1.1) result.1.2 result.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds.simulate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds.simulate_bound
