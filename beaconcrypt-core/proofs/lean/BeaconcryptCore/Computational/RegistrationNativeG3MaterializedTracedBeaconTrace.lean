-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconComplete

/-! The complete local Beacon observer is the original outer G2 observer through ordinary routing. It retains actual preparation, demand, public encapsulation and installation events on every local callback, including arbitrary optional failure replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconTrace
variable {n : Nat} {KemSK Value : Type}
abbrev Spec (n : Nat) (KemSK : Type) := RegistrationBeaconReferenceCompiler.Spec n KemSK

def begin : (Spec n KemSK).Domain → RegistrationNativeG2Trace.State → RegistrationNativeG2Trace.State
  | .inl message, before => RegistrationNativeG2Trace.begin (n := n) (KemSK := Unit) (.inl (.inl message)) before
  | .inr (.inl (.inl message)), before => RegistrationNativeG2Trace.begin (n := n) (KemSK := Unit) (.inl (.inr (.inl (.inl message)))) before
  | .inr (.inl (.inr (.inr query))), before => RegistrationNativeG2Trace.begin
      (RegistrationNativeG3MaterializedTracedServerCommon.effectQuery query) before
  | _, before => before

def finish : (query : (Spec n KemSK).Domain) → (Spec n KemSK).Range query → RegistrationNativeG2Trace.State → RegistrationNativeG2Trace.State
  | .inr (.inl (.inr (.inr query))), reply, before => RegistrationNativeG2Trace.finish
      (RegistrationNativeG3MaterializedTracedServerCommon.effectQuery query) reply before
  | .inr (.inr (.inr (.inr key))), reply, before =>
      { before with events := before.events ++ [.encapsulate false key reply.1 reply.2] }
  | _, _, before => before

def handler : QueryImpl (Spec n KemSK) (StateT RegistrationNativeG2Trace.State (OracleComp (Spec n KemSK))) := fun query before =>
  (fun reply => (reply, finish query reply (begin query before))) <$> (Spec n KemSK).query query

/-- Each actual ordinary local callback retains exactly the original frontend trace update and literal reply. -/
theorem query_source (query : (Spec n KemSK).Domain) (before : RegistrationNativeG2Trace.State) :
    (simulateQ RegistrationNativeG2Trace.handler
      (RegistrationNativePublicFrontend.liftLocal false query)).run before =
      simulateQ (RegistrationNativePublicFrontend.liftLocal false) ((handler query).run before) := by
  rcases query with message | (message | (publication | effect)) | (other | (pool | key))
  all_goals simp only [RegistrationNativePublicFrontend.liftLocal, RegistrationNativePublicFrontend.liftRoutedKem,
    RegistrationNativeKemRouting.route, Bool.false_eq_true, ite_false, simulateQ_spec_query,
    RegistrationNativeG2Trace.handler, handler, StateT.run, simulateQ_map, begin, finish]
  all_goals try rfl
  cases effect with
  | inl coin => rfl
  | inr capability => cases capability <;> rfl

/-- The entire actual Beacon local program and all mutable continuations carry the original chronological observer. -/
theorem program_source (work : OracleComp (Spec n KemSK) Value) (before : RegistrationNativeG2Trace.State) :
    (simulateQ RegistrationNativeG2Trace.handler (simulateQ (RegistrationNativePublicFrontend.liftLocal false) work)).run before =
      simulateQ (RegistrationNativePublicFrontend.liftLocal false) ((simulateQ handler work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      rw [query_source query before]
      simp only [simulateQ_spec_query, bind_map_left, handler, StateT.run, simulateQ_map]
      apply bind_congr
      intro reply
      exact ih reply (finish query reply (begin query before))
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconTrace.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconTrace.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconTrace.program_source
