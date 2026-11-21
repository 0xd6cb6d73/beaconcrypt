-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBackend
/-! The shared physical CTX interpreter threads one persistent platform state and one local source state. Public platform coins use their separate free branch and cannot inspect the private cache or journal. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner
open RegistrationNativePlatformCtxBackend (Spec)
variable {Local Platform A B : Type}
abbrev M (Local Platform : Type) := StateT Local (StateT Platform (OracleComp Spec))
abbrev Full (Local Platform : Type) := (Local × Platform) × RegistrationNativePlatformCtxBackend.State

noncomputable def interpret (work : M Local Platform A) : StateT (Full Local Platform) ProbComp A :=
  fun before => (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation ((work.run before.1.1).run before.1.2)).run before.2

def publicWork (work : StateT Platform ProbComp A) : M Local Platform A := fun current previous =>
  (fun result => ((result.1, current), result.2)) <$>
    simulateQ RegistrationNativePlatformCtxBackend.coin (work.run previous)

def privateWork (work : StateT Local (OracleComp Spec) A) : M Local Platform A :=
  fun current => StateT.lift (work.run current)

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let reply ← work before; next reply.1 reply.2) := rfl

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

theorem pure_run (value : A) :
    interpret (pure value : M Local Platform A) = pure value := by
  funext before
  simp only [interpret, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

theorem bind_run (work : M Local Platform A) (next : A → M Local Platform B) :
    interpret (work >>= next) = (interpret work >>= fun value => interpret (next value)) := by
  funext before
  simp only [interpret, StateT.run_bind, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

theorem simulate {I : Type} {spec : OracleSpec I} (handler : QueryImpl spec (M Local Platform))
    (work : OracleComp spec A) :
    interpret (simulateQ handler work) = simulateQ (fun query => interpret (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_run]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, bind_run, ih]

theorem public_run (work : StateT Platform ProbComp A) (before : Full Local Platform) :
    (interpret (publicWork work)).run before =
      (fun result => (result.1, ((before.1.1, result.2), before.2))) <$> work.run before.1.2 := by
  simp only [interpret, publicWork, StateT.run, simulateQ_map, RegistrationNativePlatformCtxBackend.coins,
    state_map_apply, state_lift_apply, bind_pure_comp, Functor.map_map]
  rfl

theorem private_run (work : StateT Local (OracleComp Spec) A) (before : Full Local Platform) :
    (interpret (privateWork work)).run before =
      (fun result => (result.1.1, ((result.1.2, before.1.2), result.2))) <$>
        (simulateQ RegistrationNativePlatformCtxBackend.implementation (work.run before.1.1)).run before.2 := by
  simp only [interpret, privateWork, StateT.run, state_lift_apply, bind_pure_comp,
    simulateQ_map, state_map_apply, Functor.map_map]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.pure_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.pure_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.bind_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.bind_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.public_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.public_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.private_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxRunner.private_run
