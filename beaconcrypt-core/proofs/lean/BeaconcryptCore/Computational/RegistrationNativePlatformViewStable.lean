-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityReceiptView

/-! Compositional input independence for an idempotent analysis projection. Both executions retain the same complete projected output; the lemmas do not erase an operational state field or assume an entire source-program simulation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformViewStable
variable {S Value Next Query : Type} {spec : OracleSpec Query}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def Stable (projection : S → S) (work : StateT S m Value) : Prop :=
  ∀ before, Prod.map id projection <$> work.run before =
    Prod.map id projection <$> work.run (projection before)

/-- Pure native steps preserve every idempotently projected source coordinate. -/
theorem pure_stable (projection : S → S) (idempotent : ∀ before, projection (projection before) = projection before)
    (value : Value) : Stable projection (pure value : StateT S m Value) := by
  intro before
  simp only [StateT.run_pure, map_pure, Prod.map, id_eq, idempotent]

/-- Adaptive sequencing preserves input independence while retaining the actual reached state between both operations. -/
theorem bind_stable (projection : S → S) (work : StateT S m Value)
    (next : Value → StateT S m Next)
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
    (implementation : QueryImpl spec (StateT S m))
    (callbacks : ∀ query, Stable projection (implementation query))
    (work : OracleComp spec Value) : Stable projection (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_stable projection idempotent value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_stable projection _ _ (callbacks query) ih



/-- Public result conversion preserves the same projected-state law. -/
theorem map_stable (projection : S → S) (idempotent : ∀ before, projection (projection before) = projection before)
    (work : StateT S m Value) (observe : Value → Next) (stable : Stable projection work) :
    Stable projection (observe <$> work) := by
  simpa only [bind_pure_comp] using bind_stable projection work (fun value => pure (observe value)) stable
    (fun value => pure_stable projection idempotent (observe value))

/-- A pure state update commutes exactly with the named analysis view. -/
theorem modify_stable (projection update : S → S)
    (commutes : ∀ before, projection (update before) = projection (update (projection before))) :
    Stable projection (modify update : StateT S m Unit) := by
  intro before
  simpa only [StateT.run_modify, map_pure, Prod.map_def, id_eq] using
    congrArg (fun after : S => (pure ((), after) : m (Unit × S))) (commutes before)

/-- Reading only a preserved field does not inspect the erased private payloads. -/
theorem read_stable (projection : S → S) (idempotent : ∀ before, projection (projection before) = projection before)
    (select : S → Value) (reads : ∀ before, select (projection before) = select before) :
    Stable projection (fun before => pure (select before, before) : StateT S m Value) := by
  intro before
  simp only [StateT.run, map_pure, Prod.map_def, id_eq, idempotent, reads]
end BeaconcryptCore.Computational.RegistrationNativePlatformViewStable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.pure_stable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.pure_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.bind_stable' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.bind_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.program_stable' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.program_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.map_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.map_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.modify_stable' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.modify_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.read_stable' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformViewStable.read_stable
