-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldView

/-! Operational noninterference under an explicit private analysis view composes through actual adaptive continuations. Both returned states are projected; no counter equality is asserted. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationStateView
variable {State Value Result I : Type} {spec : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def Stable (view : State → State) (work : StateT State m Value) : Prop :=
  ∀ before, Prod.map id view <$> work.run before =
    Prod.map id view <$> work.run (view before)

/-- A pure return observes no private analysis coordinate. -/
theorem pure_stable (view : State → State) (idem : ∀ before, view (view before) = view before)
    (value : Value) : Stable view (pure value : StateT State m Value) := by
  intro before
  simp only [StateT.run_pure, map_pure, Prod.map, id_eq, idem]

/-- Actual continuation execution preserves noninterference, including all reached poststates. -/
theorem bind_stable (view : State → State) (work : StateT State m Value)
    (next : Value → StateT State m Result) (first : Stable view work)
    (rest : ∀ value, Stable view (next value)) : Stable view (work >>= next) := by
  intro before
  simp only [StateT.run_bind, map_bind]
  calc
    _ = (Prod.map id view <$> work.run before) >>= fun result =>
        Prod.map id view <$> (next result.1).run result.2 := by
      rw [bind_map_left]
      apply bind_congr
      intro result
      exact rest result.1 result.2
    _ = (Prod.map id view <$> work.run (view before)) >>= fun result =>
        Prod.map id view <$> (next result.1).run result.2 := by rw [first before]
    _ = _ := by
      rw [bind_map_left]
      apply bind_congr
      intro result
      exact (rest result.1 result.2).symm

/-- Per-query operational laws retain their full original adaptive program. -/
theorem program_stable (view : State → State) (idem : ∀ before, view (view before) = view before)
    (implementation : QueryImpl spec (StateT State m))
    (step : ∀ query, Stable view (implementation query)) (work : OracleComp spec Value) :
    Stable view (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_stable view idem value
  | query_bind query next ih =>
      simpa only [simulateQ_bind, simulateQ_spec_query] using
        bind_stable view (implementation query) (fun reply => simulateQ implementation (next reply))
          (step query) ih

end BeaconcryptCore.Computational.RegistrationStateView

/-- info: 'BeaconcryptCore.Computational.RegistrationStateView.pure_stable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationStateView.pure_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationStateView.bind_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationStateView.bind_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationStateView.program_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationStateView.program_stable
