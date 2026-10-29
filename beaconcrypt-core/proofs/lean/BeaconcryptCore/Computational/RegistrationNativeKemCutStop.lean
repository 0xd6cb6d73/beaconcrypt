-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCut

/-! A complete first-getter cut is exactly an execution that survives aborting the exposed KEM query. This operational equivalence and its stateful support transfer let concrete native success establish cut reachability without an assumed prefix or whole-game simulation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCutStop
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemCut (Cut scan)
variable {κ KemSK Value : Type} {ambient : OracleSpec κ}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def complete : Cut ambient KemSK Value → Option Value
  | .complete value => some value
  | .pending _ _ => none

def stop (implementation : QueryImpl (Spec ambient KemSK) m) :
    QueryImpl (Spec ambient KemSK) (OptionT m)
  | .inl query => OptionT.lift (implementation (.inl query))
  | .inr (.inl query) => OptionT.lift (implementation (.inr (.inl query)))
  | .inr (.inr _) => failure

/-- A first selected getter suspends before its reply; exactly the completed cuts survive the corresponding aborting interpreter. -/
theorem scan_stop (implementation : QueryImpl (Spec ambient KemSK) m)
    (work : OracleComp (Spec ambient KemSK) Value) :
    complete <$> scan implementation work 0 = (simulateQ (stop implementation) work).run := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      change complete <$> pure (Cut.complete value) = pure (some value)
      rw [map_pure]
      rfl
  | query_bind query next ih =>
      rcases query with query | (query | key)
      · simp only [RegistrationNativeKemCut.scan_other, map_bind, simulateQ_bind, simulateQ_spec_query,
          stop, OptionT.run_bind, OptionT.run_lift, Option.elimM, Option.elim_some, bind_assoc, pure_bind, ih]
      · simp only [RegistrationNativeKemCut.scan_pool, map_bind, simulateQ_bind, simulateQ_spec_query,
          stop, OptionT.run_bind, OptionT.run_lift, Option.elimM, Option.elim_some, bind_assoc, pure_bind, ih]
      · simp only [RegistrationNativeKemCut.scan_target, map_pure, complete, simulateQ_bind,
          simulateQ_spec_query, stop, OptionT.run_bind, OptionT.run_failure, Option.elimM, Option.elim_none, pure_bind]

/-- Interpreting a suspended source cut preserves its complete exact native continuation and all earlier stateful effects. -/
theorem scan_simulate (implementation : QueryImpl (Spec ambient KemSK) m)
    (work : OracleComp (Spec ambient KemSK) Value) (index : Nat) :
    simulateQ implementation (scan (fun query => ((Spec ambient KemSK).query query : OracleComp (Spec ambient KemSK) _)) work index) =
      scan implementation work index := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure value => rfl
  | query_bind query next ih =>
      rcases query with query | (query | key)
      · simp only [RegistrationNativeKemCut.scan_other, simulateQ_bind, simulateQ_spec_query, ih]
      · simp only [RegistrationNativeKemCut.scan_pool, simulateQ_bind, simulateQ_spec_query, ih]
      · cases index with
        | zero => simp only [RegistrationNativeKemCut.scan_target, simulateQ_pure]
        | succ index => simp only [RegistrationNativeKemCut.scan_prior, simulateQ_bind, simulateQ_spec_query, ih]

/-- A complete cut reached by the actual stateful source is supported by its literal abort-at-first-getter source syntax. -/
theorem completed_support {S : Type}
    (implementation : QueryImpl (Spec ambient KemSK) (StateT S ProbComp))
    (work : OracleComp (Spec ambient KemSK) Value) (value : Value) (before after : S)
    (supported : (Cut.complete value, after) ∈ support ((scan implementation work 0).run before)) :
    some value ∈ support ((simulateQ (stop (fun query =>
      ((Spec ambient KemSK).query query : OracleComp (Spec ambient KemSK) _))) work).run) := by
  have original : Cut.complete value ∈ support
      (scan (fun query => ((Spec ambient KemSK).query query : OracleComp (Spec ambient KemSK) _)) work 0) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ before
    rw [StateT.run'_eq, scan_simulate, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  rw [← scan_stop, support_map]
  exact Set.mem_image_of_mem complete original

end BeaconcryptCore.Computational.RegistrationNativeKemCutStop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutStop.scan_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutStop.scan_stop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutStop.scan_simulate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutStop.scan_simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutStop.completed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutStop.completed_support
