import BeaconcryptCore.Computational.PqxdhInitialCurrentPost

/-!
Evaluation of the private initializer service commutes with the entire current post scheduler. Its cache stays in the ambient state monad while the original role, shared primitive and private identity state remain intact. This exact operational equality preserves full callback distributions and introduces no generator-order or marginal-distribution assumption.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPostInterpretation
open PqxdhInitialGenericPost
variable {ι ι₀ M P I D K A N Result : Type} {extra : OracleSpec ι} {spec : OracleSpec ι₀} {S B : Nat}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def work {State Value : Type} (interpret : QueryImpl spec m)
    (computation : StateT State (OracleComp spec) Value) : StateT State m Value :=
  fun state => simulateQ interpret (computation.run state)

/-- Evaluating the private initializer service retains each original record, selector and whole-owner operation with its complete poststate. -/
theorem native_step
    (interpret : QueryImpl spec m)
    (records : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) (OracleComp spec)))
    (selector : QueryImpl extra (StateT N (OracleComp spec)))
    (owner : Pqxdh.Bytes → RawCtxBeaconLifecycle.State I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) (OracleComp spec)
        (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D K)) :
    interpret.mapStateTBase (nativePost records selector owner) =
      nativePost (interpret.mapStateTBase records) (interpret.mapStateTBase selector)
        (fun raw state => work interpret (owner raw state)) := by
  funext query state
  rcases query with (query | query) | query
  case inl.inl =>
    simp only [QueryImpl.mapStateTBase, nativePost, StateT.run, StateT.mk, simulateQ_map]
  case inl.inr =>
    simp only [QueryImpl.mapStateTBase, nativePost, StateT.run, StateT.mk, simulateQ_map]
  case inr =>
    cases query
    simp only [QueryImpl.mapStateTBase, nativePost, work, StateT.run, StateT.mk, simulateQ_map]

/-- The entire original adaptive post client evaluates in the same ambient initializer/cache interpreter with every intermediate private state retained. -/
theorem native_schedule
    (interpret : QueryImpl spec m)
    (records : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) (OracleComp spec)))
    (selector : QueryImpl extra (StateT N (OracleComp spec)))
    (owner : Pqxdh.Bytes → RawCtxBeaconLifecycle.State I D K →
      StateT (RawCtxSharedPrimitive.SharedState A × N) (OracleComp spec)
        (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D K))
    (client : OracleComp (Spec extra S B) Result) (state : NativeState M P I D K A N S B) :
    simulateQ interpret ((simulateQ (nativePost records selector owner) client).run state) =
      (simulateQ (nativePost (interpret.mapStateTBase records) (interpret.mapStateTBase selector)
        (fun raw before => work interpret (owner raw before))) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, native_step]

end BeaconcryptCore.Computational.PqxdhInitialPostInterpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostInterpretation.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostInterpretation.native_step
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostInterpretation.native_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostInterpretation.native_schedule
