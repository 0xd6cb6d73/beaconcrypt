-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform

/-! Compositional input independence for an idempotent analysis projection. Both executions retain the same complete projected output; the lemmas do not erase an operational state field or assume an entire source-program simulation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence
variable {S Value Next Query : Type} {spec : OracleSpec Query}

def Stable (projection : S → S) (work : StateT S ProbComp Value) : Prop :=
  ∀ before, Prod.map id projection <$> work.run before =
    Prod.map id projection <$> work.run (projection before)

/-- Pure native steps preserve every idempotently projected source coordinate. -/
theorem pure_stable (projection : S → S) (idempotent : ∀ before, projection (projection before) = projection before)
    (value : Value) : Stable projection (pure value) := by
  intro before
  simp only [StateT.run_pure, map_pure, Prod.map, id_eq, idempotent]

/-- Adaptive sequencing preserves input independence while retaining the actual reached state between both operations. -/
theorem bind_stable (projection : S → S) (work : StateT S ProbComp Value)
    (next : Value → StateT S ProbComp Next)
    (first : Stable projection work) (following : ∀ value, Stable projection (next value)) :
    Stable projection (work >>= next) := by
  intro before
  simp only [StateT.run_bind, map_bind]
  calc
    _ = work.run before >>= fun result => Prod.map id projection <$> (next result.1).run (projection result.2) := by
      apply bind_congr
      intro result
      exact following result.1 result.2
    _ = (Prod.map id projection <$> work.run before) >>= fun result => Prod.map id projection <$> (next result.1).run result.2 := by
      rw [bind_map_left]
      rfl
    _ = (Prod.map id projection <$> work.run (projection before)) >>= fun result => Prod.map id projection <$> (next result.1).run result.2 := by
      rw [first before]
    _ = work.run (projection before) >>= fun result => Prod.map id projection <$> (next result.1).run (projection result.2) := by
      rw [bind_map_left]
      rfl
    _ = _ := by
      apply bind_congr
      intro result
      exact (following result.1 result.2).symm

/-- Every ordered native oracle continuation inherits the proved local callback laws. -/
theorem program_stable (projection : S → S)
    (idempotent : ∀ before, projection (projection before) = projection before)
    (implementation : QueryImpl spec (StateT S ProbComp))
    (callbacks : ∀ query, Stable projection (implementation query))
    (work : OracleComp spec Value) : Stable projection (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_stable projection idempotent value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_stable projection _ _ (callbacks query) ih

end BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence.pure_stable' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence.pure_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence.bind_stable' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence.bind_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence.program_stable' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence.program_stable
