-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
import Cslib.Foundations.Control.Monad.IsMonadHom

/-! The corrected native platform profile keeps its private native state and public platform state in separate StateT layers. Ordinary platform strategies use only ordinary randomness; named ML leaves remain the existing free capabilities. Evaluation retains both states and true source draw counts, without identifying this profile with the legacy native handler. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
open RegistrationNativeMldsaProgram (Spec)
variable {source : RegistrationNativeMldsa.Source} {Native Platform Value Next : Type}

abbrev M (source : RegistrationNativeMldsa.Source) (Platform : Type) :=
  StateT Platform (OracleComp (Spec source))

noncomputable def evaluate (work : StateT Native (M source Platform) Value) :
    StateT Native (StateT Platform ProbComp) Value := fun before =>
  RegistrationNativeMldsaProgram.evalState (work.run before)

def lift (work : StateT Native (StateT Platform ProbComp) Value) :
    StateT Native (M source Platform) Value := fun before =>
  RegistrationNativeMldsaProgram.liftState (work.run before)

def inject (work : StateT Native (OracleComp (Spec source)) Value) :
    StateT Native (M source Platform) Value := fun before => StateT.lift (work.run before)

def coins : QueryImpl unifSpec (StateT Platform ProbComp) := fun query => StateT.lift (unifSpec.query query)

def ordinary : QueryImpl unifSpec (M source Platform) := fun query =>
  StateT.lift (RegistrationNativeMldsaProgram.ordinary query)

/-- Evaluation keeps both private-native and external-platform coordinates of ordinary source work. -/
theorem evaluate_lift (work : StateT Native (StateT Platform ProbComp) Value) :
    evaluate (source := source) (lift work) = work := by
  funext before
  exact RegistrationNativeMldsaProgram.eval_liftState (work.run before)

theorem evaluate_pure (value : Value) :
    evaluate (source := source) (pure value : StateT Native (M source Platform) Value) = pure value := by
  funext before previous
  rfl

theorem evaluate_bind (work : StateT Native (M source Platform) Value)
    (next : Value → StateT Native (M source Platform) Next) :
    evaluate (work >>= next) = (evaluate work >>= fun value => evaluate (next value)) := by
  funext before
  simp only [evaluate, StateT.run_bind, RegistrationNativeMldsaProgram.eval_bind]
  rfl

theorem evaluate_hom : Cslib.IsMonadHom
    (StateT Native (M source Platform)) (StateT Native (StateT Platform ProbComp)) evaluate :=
  .mk' evaluate_pure evaluate_bind

/-- Reified ML operations retain their actual private accounting while the external platform state is unchanged. -/
theorem evaluate_inject (work : StateT Native (OracleComp (Spec source)) Value) :
    evaluate (Platform := Platform) (inject work) = fun before =>
      StateT.lift ((RegistrationNativeMldsaProgram.evalState work).run before) := by
  funext before previous
  change simulateQ RegistrationNativeMldsaProgram.actual (do
    let value ← work.run before
    pure (value, previous)) = (do
      let value ← RegistrationNativeMldsaProgram.evaluate (work.run before)
      pure (value, previous))
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- Ordinary native coins in the actual platform profile leave its separate allocator state unchanged. -/
theorem lift_coins (work : ProbComp Value) :
    simulateQ (coins (Platform := Platform)) work = StateT.lift work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, coins, ih]
      funext before
      simp only [StateT.monad_bind_def, StateT.bind, StateT.lift, bind_assoc, pure_bind]

theorem ordinary_lift (work : ProbComp Value) :
    simulateQ (ordinary (source := source) (Platform := Platform)) work =
      StateT.lift (RegistrationNativeMldsaProgram.lift work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, RegistrationNativeMldsaProgram.lift, simulateQ_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, ordinary, ih,
        RegistrationNativeMldsaProgram.lift, simulateQ_bind, simulateQ_spec_query]
      funext before
      simp only [StateT.monad_bind_def, StateT.bind, StateT.lift, bind_assoc, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_hom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_inject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.evaluate_inject

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.lift_coins' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.lift_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.ordinary_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram.ordinary_lift
