-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram

/-! Actual private-table execution threads the native state, public platform state and private key table independently. Ordinary platform work cannot issue a named ML operation or inspect its private table; injected existing ML source programs leave the external state unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativePlatformMldsaProgram (M)
variable {Native Platform Value Next : Type} (source : Source)

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

noncomputable def runState (work : StateT Native (M (handleSource source) Platform) Value)
    (before : Native) (previous : Platform) (pool : Pool source) : ProbComp (((Value × Native) × Platform) × Pool source) :=
  RegistrationNativeMldsaTableProgram.evaluate source ((work.run before).run previous) pool

/-- Every adaptive continuation receives the literal reached native state, external state and private table. -/
theorem run_bind (work : StateT Native (M (handleSource source) Platform) Value)
    (next : Value → StateT Native (M (handleSource source) Platform) Next)
    (before : Native) (previous : Platform) (pool : Pool source) :
    runState source (work >>= next) before previous pool = (do
      let result ← runState source work before previous pool
      runState source (next result.1.1.1) result.1.1.2 result.1.2 result.2) := by
  simp only [runState, StateT.run_bind, RegistrationNativeMldsaTableProgram.evaluate,
    simulateQ_bind, StateT.run_bind]

/-- Ordinary stateful platform work retains the exact native and external poststate while leaving private ML rows and logs unchanged. -/
theorem run_lift (work : StateT Native (StateT Platform ProbComp) Value)
    (before : Native) (previous : Platform) (pool : Pool source) :
    runState source (RegistrationNativePlatformMldsaProgram.lift work) before previous pool =
      (fun result => (result, pool)) <$> ((work.run before).run previous) := by
  change RegistrationNativeMldsaTableProgram.runState source
    (RegistrationNativeMldsaProgram.liftState (work.run before)) previous pool = _
  exact RegistrationNativeMldsaTableProgram.run_liftState source (work.run before) previous pool

/-- Injecting an actual existing ML controller retains the external platform state through its complete private-table interpretation. -/
theorem run_inject (work : StateT Native (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value)
    (before : Native) (previous : Platform) (pool : Pool source) :
    runState source (RegistrationNativePlatformMldsaProgram.inject work) before previous pool =
      (fun result => ((result.1, previous), result.2)) <$>
        RegistrationNativeMldsaTableProgram.runState source work before pool := by
  simp only [runState, RegistrationNativePlatformMldsaProgram.inject, StateT.run, lift_apply,
    RegistrationNativeMldsaTableProgram.runState, RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, map_apply]
  rfl
theorem run_pure (value : Value) (before : Native) (previous : Platform) (pool : Pool source) :
    runState source (pure value) before previous pool = pure (((value, before), previous), pool) := by
  simp only [runState, StateT.run_pure, RegistrationNativeMldsaTableProgram.evaluate, simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_inject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_inject

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram.run_pure
