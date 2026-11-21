-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnvBuild

/-! The original full frontend G2 trace restricts exactly to the demand/effect leaves of the actual inlined Server build. This observer forwards the same literal local query once and retains the actual reply; it introduces no synthetic installation or descriptor event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace
variable {n : Nat} {KemSK Value : Type}
abbrev Spec (n : Nat) (KemSK : Type) := RegistrationBeaconReferenceCompiler.Spec n KemSK

def Allowed : (Spec n Unit).Domain → Prop
  | .inr (.inl (.inl _)) | .inr (.inl (.inr (.inr _))) => True
  | _ => False

def begin : (Spec n KemSK).Domain → RegistrationNativeG2Trace.State → RegistrationNativeG2Trace.State
  | .inr (.inl (.inl message)), before => RegistrationNativeG2Trace.begin (n := n) (KemSK := Unit)
      (.inl (.inr (.inl (.inl message)))) before
  | .inr (.inl (.inr (.inr query))), before => RegistrationNativeG2Trace.begin
      (RegistrationNativeG3MaterializedTracedServerCommon.effectQuery query) before
  | _, before => before

def finish : (query : (Spec n KemSK).Domain) → (Spec n KemSK).Range query →
    RegistrationNativeG2Trace.State → RegistrationNativeG2Trace.State
  | .inr (.inl (.inr (.inr query))), reply, before => RegistrationNativeG2Trace.finish
      (RegistrationNativeG3MaterializedTracedServerCommon.effectQuery query) reply before
  | _, _, before => before

def handler : QueryImpl (Spec n KemSK) (StateT RegistrationNativeG2Trace.State (OracleComp (Spec n KemSK))) := fun query before =>
  (fun reply => (reply, finish query reply (begin query before))) <$> (Spec n KemSK).query query

theorem query_source (query : (Spec n KemSK).Domain) (allowed : Allowed query) (before : RegistrationNativeG2Trace.State) :
    (simulateQ RegistrationNativeG2Trace.handler
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false) (((Spec n KemSK).query query : OracleComp (Spec n KemSK) _)))).run before =
      simulateQ (RegistrationNativePublicFrontend.liftLocal false) ((handler query).run before) := by
  rcases query with message | (message | (publication | effect)) | kem
  · exact allowed.elim
  · simp only [simulateQ_spec_query, RegistrationNativePublicFrontend.liftLocal, RegistrationNativeG2Trace.handler,
      handler, StateT.run, simulateQ_map, begin, finish]
    rfl
  · exact allowed.elim
  · simp only [simulateQ_spec_query, RegistrationNativePublicFrontend.liftLocal, RegistrationNativeG2Trace.handler,
      handler, StateT.run, simulateQ_map, begin, finish]
    cases effect with
    | inl coin => rfl
    | inr capability => cases capability <;> rfl
  · exact allowed.elim

/-- The actual outer chronological observer commutes to the literal local Server computation on every adaptive continuation. -/
theorem program_source (work : OracleComp (Spec n KemSK) Value) (allowed : AllQueriesSatisfy work Allowed)
    (before : RegistrationNativeG2Trace.State) :
    (simulateQ RegistrationNativeG2Trace.handler
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false) work)).run before =
      simulateQ (RegistrationNativePublicFrontend.liftLocal false) ((simulateQ handler work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      obtain ⟨current, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [simulateQ_bind, StateT.run_bind]
      rw [query_source query current before]
      simp only [simulateQ_spec_query, bind_map_left, handler, StateT.run, simulateQ_map, ]
      apply bind_congr
      intro reply
      exact ih reply (later reply) (finish query reply (begin query before))

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace.program_source
