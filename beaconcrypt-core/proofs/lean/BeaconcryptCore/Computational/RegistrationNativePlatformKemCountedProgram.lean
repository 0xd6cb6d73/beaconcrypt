-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram

/-! The actual counted indexed KEM interpreter threads the source client, common external platform and private pool independently. Ordinary platform actions retain their exact poststates; injected actual native controllers retain their complete private draw costs without touching the platform. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram
open PqxdhServerAuthExperiment (Setup)
open PqxdhLiveKemBirth (Pool)
open RegistrationNativeKemCountedProgram (Spec)
variable {ι KemSK Native Platform Value Next : Type} {base : OracleSpec ι}

abbrev M (KemSK Platform : Type) := StateT Platform (OracleComp (Spec KemSK))

def lift (work : StateT Native (StateT Platform ProbComp) Value) : StateT Native (M KemSK Platform) Value :=
  fun before => RegistrationNativeKemCountedProgram.liftState (work.run before)

def inject (work : StateT Native (OracleComp (Spec KemSK)) Value) : StateT Native (M KemSK Platform) Value :=
  fun before => StateT.lift (work.run before)

def ordinary : QueryImpl unifSpec (M KemSK Platform) := fun query => StateT.lift (RegistrationNativeKemCountedProgram.ordinary query)

noncomputable def runState (setup : Setup base KemSK) (work : StateT Native (M KemSK Platform) Value)
    (before : Native) (previous : Platform) (pool : Pool KemSK) : ProbComp (((Value × Native) × Platform) × Pool KemSK) :=
  RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem ((work.run before).run previous) pool

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := bind_pure_comp _ _

/-- Every adaptive continuation receives the literal reached source client, platform and private pool. -/
theorem run_bind (setup : Setup base KemSK) (work : StateT Native (M KemSK Platform) Value)
    (next : Value → StateT Native (M KemSK Platform) Next)
    (before : Native) (previous : Platform) (pool : Pool KemSK) :
    runState setup (work >>= next) before previous pool = (do
      let result ← runState setup work before previous pool
      runState setup (next result.1.1.1) result.1.1.2 result.1.2 result.2) := by
  simp only [runState, StateT.run_bind, RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind]

/-- Ordinary stateful platform actions leave private KEM rows and histories unchanged and retain every actual source/platform poststate. -/
theorem run_lift (setup : Setup base KemSK) (work : StateT Native (StateT Platform ProbComp) Value)
    (before : Native) (previous : Platform) (pool : Pool KemSK) :
    runState setup (lift work) before previous pool = (fun result => (result, pool)) <$> ((work.run before).run previous) := by
  change RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem
    (RegistrationNativeKemCountedProgram.liftState (work.run before)) previous pool = _
  exact RegistrationNativeKemCountedProgram.run_liftState setup.baseImpl setup.kem (work.run before) previous pool

/-- Actual indexed native source work retains the external platform state throughout the complete private-pool interpretation. -/
theorem run_inject (setup : Setup base KemSK) (work : StateT Native (OracleComp (Spec KemSK)) Value)
    (before : Native) (previous : Platform) (pool : Pool KemSK) :
    runState setup (inject work) before previous pool = (fun result => ((result.1, previous), result.2)) <$>
      RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem work before pool := by
  simp only [runState, inject, StateT.run, lift_apply, RegistrationNativeKemCountedProgram.runState,
    RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, map_apply]
  rfl

/-- A literal source return changes none of the three state coordinates. -/
theorem run_pure (setup : Setup base KemSK) (value : Value) (before : Native) (previous : Platform) (pool : Pool KemSK) :
    runState setup (pure value) before previous pool = pure (((value, before), previous), pool) := by
  simp only [runState, StateT.run_pure, RegistrationNativeKemCountedProgram.evaluate, simulateQ_pure]

def arrange (result : (((Value × Native) × Platform) × Pool KemSK)) : Value × ((Native × Platform) × Pool KemSK) :=
  (result.1.1.1, ((result.1.1.2, result.1.2), result.2))

noncomputable def execute (setup : Setup base KemSK) (work : StateT Native (M KemSK Platform) Value) :
    StateT ((Native × Platform) × Pool KemSK) ProbComp Value := fun before =>
  arrange <$> runState setup work before.1.1 before.1.2 before.2

/-- Pure source return leaves the packed native/platform/private state untouched. -/
theorem execute_pure (setup : Setup base KemSK) (value : Value) :
    execute setup (pure value : StateT Native (M KemSK Platform) Value) = pure value := by
  funext before
  simp only [execute, run_pure, map_pure]
  rfl

/-- Packed actual interpretation preserves every adaptive source continuation. -/
theorem execute_bind (setup : Setup base KemSK) (work : StateT Native (M KemSK Platform) Value)
    (next : Value → StateT Native (M KemSK Platform) Next) :
    execute setup (work >>= next) = (execute setup work >>= fun value => execute setup (next value)) := by
  funext before
  change arrange <$> runState setup (work >>= next) before.1.1 before.1.2 before.2 =
    ((execute setup work >>= fun value => execute setup (next value))).run before
  rw [run_bind, StateT.run_bind]
  simp only [execute, StateT.run, map_bind, bind_map_left, arrange]

/-- Every typed adaptive request tree has the same packed actual interpretation. -/
theorem execute_simulate {κ : Type} {spec : OracleSpec κ} (setup : Setup base KemSK)
    (implementation : QueryImpl spec (StateT Native (M KemSK Platform))) (work : OracleComp spec Value) :
    execute setup (simulateQ implementation work) = simulateQ (fun query => execute setup (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, execute_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, execute_bind, ih]

/-- Ordinary platform/source execution has its literal packed poststate and unchanged private pool. -/
theorem execute_lift (setup : Setup base KemSK) (work : StateT Native (StateT Platform ProbComp) Value)
    (before : Native) (previous : Platform) (pool : Pool KemSK) :
    (execute setup (lift work)).run ((before, previous), pool) =
      (fun result => (result.1.1, ((result.1.2, result.2), pool))) <$> ((work.run before).run previous) := by
  change arrange <$> runState setup (lift work) before previous pool = _
  rw [run_lift, Functor.map_map]
  rfl

/-- Actual indexed native execution retains the literal platform state and complete private source pool. -/
theorem execute_inject (setup : Setup base KemSK) (work : StateT Native (OracleComp (Spec KemSK)) Value)
    (before : Native) (previous : Platform) (pool : Pool KemSK) :
    (execute setup (inject work)).run ((before, previous), pool) =
      (fun result => (result.1.1, ((result.1.2, previous), result.2))) <$>
        RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem work before pool := by
  change arrange <$> runState setup (inject work) before previous pool = _
  rw [run_inject, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_lift' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_inject' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_inject

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.run_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_pure' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_simulate' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_lift' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_inject' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram.execute_inject
