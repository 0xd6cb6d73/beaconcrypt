-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathMap

/-! A literal state projection that commutes with every interpreted callback commutes with the complete adaptive program. No source probability or event equality is assumed by applications: their concrete callback law supplies the projection. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeTargetStateMap
variable {Index : Type} {spec : OracleSpec Index} {Before After Value : Type}

/-- Pointwise source erasure transports every actual adaptive continuation while preserving its public result. -/
theorem program (project : Before → After)
    (first : QueryImpl spec (StateT Before ProbComp)) (second : QueryImpl spec (StateT After ProbComp))
    (step : ∀ query before, Prod.map id project <$> (first query).run before = (second query).run (project before))
    (work : OracleComp spec Value) (before : Before) :
    Prod.map id project <$> (simulateQ first work).run before = (simulateQ second work).run (project before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← step query before, bind_map_left]
      apply bind_congr
      intro reached
      exact ih reached.1 reached.2
end BeaconcryptCore.Computational.RegistrationNativeTargetStateMap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTargetStateMap.program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTargetStateMap.program
