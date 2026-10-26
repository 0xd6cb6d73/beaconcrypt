-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxSharedPrefixScan

/-! Interpret the unchanged shared prefix scanner with its entire backend state, preserving every backend history and complete continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedPrefixBackend
open AdaptiveCtxSharedHash RawCtxForwardAnnotation RawCtxForwardCoverage RawCtxForwardScan
variable {ι Local Backend Tag Result : Type} {base : OracleSpec ι}

/-- The entire local/backend pair is the native state of this evaluated compiler. -/
noncomputable def handler (backend : QueryImpl HashSpec (StateT Backend ProbComp))
    (impl : QueryImpl base (StateT Local (OracleComp HashSpec))) : QueryImpl base (StateT (Local × Backend) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ backend ((impl query).run before.1)).run before.2

/-- Retain the original complete or pending cut and both parts of the reached state. -/
def restore (result : Cut Tag Result Local × Backend) : Cut Tag Result (Local × Backend) :=
  match result.1 with
  | .complete value state => .complete value (state, result.2)
  | .pending tag state => .pending tag (state, result.2)

/-- The actual compiler and whole backend, including its histories and bookkeeping, commute with the unchanged scanner. This is a complete program equality and uses no marginal-state law. -/
theorem evaluated
    (privateQuery : base.Domain → Bool) (selected : base.Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp HashSpec)))
    (backend : QueryImpl HashSpec (StateT Backend ProbComp))
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (state : Local) (before : Backend) :
    restore <$> (simulateQ backend (RawCtxSharedPrefixScan.scan privateQuery selected selection impl client covered state)).run before =
      scan privateQuery (fun query current => selected query current.1)
        (fun query current chosen => selection query current.1 chosen) (handler backend impl) client covered (state, before) := by
  induction client using OracleComp.inductionOn generalizing state before with
  | pure value => rfl
  | query_bind query next ih =>
    cases chosen : selected query.2 state with
    | true =>
      rw [scan_cut privateQuery (fun query current => selected query current.1)
        (fun query current chosen => selection query current.1 chosen) (handler backend impl) query next covered _ chosen]
      change restore <$> (simulateQ backend (if chosen : selected query.2 state = true then _ else _)).run before = _
      rw [dite_eq_left chosen]
      rfl
    | false =>
      rw [scan_other privateQuery (fun query current => selected query current.1)
        (fun query current chosen => selection query current.1 chosen) (handler backend impl) query next covered _ chosen]
      change restore <$> (simulateQ backend (if chosen : selected query.2 state = true then _ else _)).run before = _
      rw [dite_eq_right (by rw [chosen]; decide)]
      simp only [simulateQ_bind, StateT.run_bind, map_bind]
      rw [show (handler backend impl query.2).run (state, before) =
        (fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ backend ((impl query.2).run state)).run before from rfl, bind_map_left]
      exact bind_congr fun result => ih result.1.1 (covered.2 result.1.1) result.1.2 result.2

end BeaconcryptCore.Computational.RawCtxSharedPrefixBackend

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPrefixBackend.evaluated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrefixBackend.evaluated
