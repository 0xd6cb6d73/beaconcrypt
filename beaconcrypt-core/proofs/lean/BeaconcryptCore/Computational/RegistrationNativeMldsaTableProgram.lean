-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap

/-! The actual opaque capability program is interpreted by its private key table, with ordinary source randomness forwarded literally. Evaluation retains both the native state and table across every continuation. Named generation/sign leaves expose their exact original source distribution and actual accounting count; no complete opaque-profile correspondence is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource Pool Live birth record)
open RegistrationNativeMldsaCapability (Accounting advance)
variable {n : Nat} {State Value Next : Type} (source : Source)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

noncomputable def handler : QueryImpl (RegistrationNativeMldsaProgram.Spec (handleSource source)) (StateT (Pool source) ProbComp)
  | .inl query => StateT.lift (unifSpec.query query)
  | .inr query => RegistrationNativeMldsaOpaque.actual source query

noncomputable def evaluate (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source) :
    ProbComp (Value × Pool source) := (simulateQ (handler source) work).run before

noncomputable def runState (work : StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value)
    (current : State) (before : Pool source) : ProbComp ((Value × State) × Pool source) :=
  evaluate source (work.run current) before

theorem ordinary (work : ProbComp Value) (before : Pool source) :
    evaluate source (RegistrationNativeMldsaProgram.lift work) before = (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [evaluate, RegistrationNativeMldsaProgram.lift, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [evaluate, RegistrationNativeMldsaProgram.lift, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeMldsaProgram.ordinary, handler, StateT.run_bind, StateT.run_lift]
      simp only [bind_assoc, pure_bind, map_bind]
      apply bind_congr
      intro reply
      exact ih reply before

theorem run_pure (value : Value) (current : State) (before : Pool source) :
    runState source (pure value) current before = pure ((value, current), before) := by
  simp only [runState, evaluate, StateT.run_pure, simulateQ_pure]

theorem run_bind (work : StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value)
    (next : Value → StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Next)
    (current : State) (before : Pool source) :
    runState source (work >>= next) current before = (do
      let result ← runState source work current before
      runState source (next result.1.1) result.1.2 result.2) := by
  simp only [runState, evaluate, StateT.run_bind, simulateQ_bind]

theorem run_liftState (work : StateT State ProbComp Value) (current : State) (before : Pool source) :
    runState source (RegistrationNativeMldsaProgram.liftState work) current before =
      (fun result => (result, before)) <$> work.run current :=
  ordinary source _ before

set_option backward.isDefEq.respectTransparency false in
theorem generate_source (accounting : Accounting) (current : PqxdhRecordLiftWorld.State n) (before : Pool source) :
    runState source (RegistrationNativeMldsaProgram.call accounting .generate) current before =
      (fun generated =>
        let born := birth source before generated
        ((born.1.1, advance accounting current born.1.2), born.2)) <$>
        RegistrationNativeMldsaCapability.actual source .generate := by
  simp only [runState, evaluate, RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, handler]
  rw [map_apply]
  simp only [RegistrationNativeMldsaOpaque.actual, Functor.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sign_source (accounting : Accounting) (current : PqxdhRecordLiftWorld.State n) (before : Pool source)
    (handle : Credential (handleSource source)) (key : Credential source) (live : Live source before handle key)
    (request : beaconcrypt_core.registration.MldsaSigningRequest) :
    runState source (RegistrationNativeMldsaProgram.call accounting (.sign handle request)) current before =
      (fun result => ((result.1, advance accounting current result.2), record source before handle request result.1)) <$>
        RegistrationNativeMldsaCapability.actual source (.sign key request) := by
  simp only [runState, evaluate, RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, handler]
  rw [map_apply]
  have leaf := RegistrationNativeMldsaOpaque.sign_source source before handle key live request
  simp only [StateT.run] at leaf
  rw [leaf]
  simp only [Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.run_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.run_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.run_liftState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.run_liftState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.generate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.generate_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.sign_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram.sign_source
