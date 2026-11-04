-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds
/-! Packing the native and external platform state is an exact monadic change of representation. It preserves full values and both poststates under arbitrary adaptive simulation, and preserves predicate query bounds. This lets executable stopped reductions observe the full permitted pair without discarding allocation history. -/
open CoreModels Aeneas OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
variable {State Platform Value Next I : Type} {spec : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def pack (work : StateT State (StateT Platform m) Value) : StateT (State × Platform) m Value :=
  fun before => (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2

theorem pure_pack (value : Value) : pack (pure value : StateT State (StateT Platform m) Value) = pure value := by
  funext before
  simp only [pack, StateT.run_pure, map_pure]
  rfl

theorem bind_pack (work : StateT State (StateT Platform m) Value)
    (next : Value → StateT State (StateT Platform m) Next) :
    pack (work >>= next) = pack work >>= fun value => pack (next value) := by
  funext before
  change ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((work >>= next).run before.1).run before.2) = (do
      let result ← (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2
      (fun result => (result.1.1, (result.1.2, result.2))) <$> ((next result.1).run result.2.1).run result.2.2)
  rw [StateT.run_bind, StateT.run_bind]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]

theorem simulate_pack (handler : QueryImpl spec (StateT State (StateT Platform m))) (work : OracleComp spec Value) :
    pack (simulateQ handler work) = simulateQ (fun query => pack (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_pack value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_pack, ih]

omit [Monad m] [LawfulMonad m] in
theorem query_bound (predicate : I → Prop) [DecidablePred predicate]
    (work : StateT State (StateT Platform (OracleComp spec)) Value) (cap : Nat) (before : State × Platform) :
    ((pack work).run before).IsQueryBoundP predicate cap ↔
      ((work.run before.1).run before.2).IsQueryBoundP predicate cap := by
  simp only [pack, StateT.run, isQueryBoundP_map_iff]
end BeaconcryptCore.Computational.RegistrationNativePlatformPackedState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.pure_pack' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.pure_pack

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.bind_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.bind_pack

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.simulate_pack' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.simulate_pack

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.query_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPackedState.query_bound
