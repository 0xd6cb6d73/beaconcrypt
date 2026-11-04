-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram

/-! Source-key translation for generation-free private signing programs. Ordinary randomness and every complete signing request are retained. The total helper returns failure for a generation query; the controller equalities using it must therefore check that generation is absent. Actual generation is handled separately by the dynamic private table and its new-row receipt. No equality of closed source signers is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaMap (Map credential)
open RegistrationNativeMldsaProgram (Spec)
variable {left right : Source} {State Value Next : Type} {n : Nat}

def translation (mapping : Map left right) : QueryImpl (Spec left) (OracleComp (Spec right))
  | .inl query => (Spec right).query (.inl query)
  | .inr (.sign current request) => (Spec right).query (.inr (.sign (credential mapping current) request))
  | .inr .generate => pure (none, 0)

def transform (mapping : Map left right) (work : OracleComp (Spec left) Value) : OracleComp (Spec right) Value :=
  simulateQ (translation mapping) work

def transformState (mapping : Map left right) (work : StateT State (OracleComp (Spec left)) Value) :
    StateT State (OracleComp (Spec right)) Value := fun before => transform mapping (work.run before)

theorem transform_lift (mapping : Map left right) (work : ProbComp Value) :
    transform mapping (RegistrationNativeMldsaProgram.lift work) = RegistrationNativeMldsaProgram.lift work := by
  have restriction : translation mapping ∘ₛ RegistrationNativeMldsaProgram.ordinary =
      RegistrationNativeMldsaProgram.ordinary (source := right) := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativeMldsaProgram.ordinary, simulateQ_spec_query, translation]
  rw [transform, RegistrationNativeMldsaProgram.lift, ← QueryImpl.simulateQ_compose, restriction]
  rfl

theorem state_lift (mapping : Map left right) (work : StateT State ProbComp Value) :
    transformState mapping (RegistrationNativeMldsaProgram.liftState work) = RegistrationNativeMldsaProgram.liftState work := by
  funext before
  exact transform_lift mapping (work.run before)

theorem state_pure (mapping : Map left right) (value : Value) :
    transformState mapping (pure value : StateT State _ Value) = pure value := by
  funext before
  simp only [transformState, transform, StateT.run_pure, simulateQ_pure]
  rfl

theorem state_bind (mapping : Map left right) (work : StateT State (OracleComp (Spec left)) Value)
    (next : Value → StateT State (OracleComp (Spec left)) Next) :
    transformState mapping (work >>= next) = (transformState mapping work >>= fun value => transformState mapping (next value)) := by
  funext before
  simp only [transformState, transform, StateT.run_bind, simulateQ_bind]
  rfl

theorem state_simulate {Query : Type} {spec : OracleSpec Query} (mapping : Map left right)
    (implementation : QueryImpl spec (StateT State (OracleComp (Spec left)))) (work : OracleComp spec Value) :
    transformState mapping (simulateQ implementation work) =
      simulateQ (fun query => transformState mapping (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, state_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, state_bind, ih]

/-- Named signing requests retain their optional reply and literal actual accounting receipt. -/
theorem state_sign (mapping : Map left right) (accounting : RegistrationNativeMldsaCapability.Accounting)
    (current : Credential left) (request : beaconcrypt_core.registration.MldsaSigningRequest) :
    transformState mapping (RegistrationNativeMldsaProgram.call (n := n) accounting (.sign current request)) =
      RegistrationNativeMldsaProgram.call accounting (.sign (credential mapping current) request) := by
  funext before
  simp only [transformState, transform, RegistrationNativeMldsaProgram.call, StateT.run,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, translation]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.transform_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.transform_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap.state_sign
