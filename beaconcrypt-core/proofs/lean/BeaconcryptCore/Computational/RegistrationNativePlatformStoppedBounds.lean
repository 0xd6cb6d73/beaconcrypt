-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativeMldsaStop
/-! An executable first-candidate freeze on the exact packed native/platform state cannot add counted requests. The observer can inspect the full packed state; the same source cap holds for any fixed post-stop replies and every failed pre-stop callback. -/
open CoreModels Aeneas OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformStoppedBounds
open RegistrationNativePlatformPackedState (pack)
variable {I J State Platform Value Candidate : Type} {spec : OracleSpec I} {target : OracleSpec J}

theorem stopped
    (predicate : I → Prop) [DecidablePred predicate]
    (counted : J → Prop) [DecidablePred counted]
    (handler : QueryImpl spec (StateT State (StateT Platform (OracleComp target))))
    (steps : ∀ query native platform,
      (((handler query).run native).run platform).IsQueryBoundP counted (if predicate query then 1 else 0))
    (observe : RegistrationNativeMldsaStop.Observer (spec := spec) (State := State × Platform) (Candidate := Candidate))
    (defaultReply : (query : spec.Domain) → spec.Range query)
    (work : OracleComp spec Value) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap)
    (before : State × Platform) (previous : Option Candidate) :
    ((simulateQ (RegistrationNativeMldsaStop.freeze (fun query => pack (handler query)) observe defaultReply) work).run
      (before, previous)).IsQueryBoundP counted cap := by
  have step (query : spec.Domain) (current : (State × Platform) × Option Candidate) :
      ((RegistrationNativeMldsaStop.freeze (fun query => pack (handler query)) observe defaultReply query).run current).IsQueryBoundP counted
        (if predicate query then 1 else 0) := by
    rcases current with ⟨current, previous⟩
    cases previous with
    | some candidate => exact isQueryBoundP_pure _ _ _
    | none =>
        simpa only [RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor, StateT.run,
          bind_pure_comp, isQueryBoundP_map_iff, pack] using steps query current.1 current.2
  apply bounded.simulateQ_run_of_step
  · intro query included current
    simpa only [included, ite_true] using step query current
  · intro query excluded current
    simpa only [excluded, ite_false] using step query current
end BeaconcryptCore.Computational.RegistrationNativePlatformStoppedBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformStoppedBounds.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformStoppedBounds.stopped
