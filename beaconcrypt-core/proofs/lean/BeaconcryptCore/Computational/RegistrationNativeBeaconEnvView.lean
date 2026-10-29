-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationStateView
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend

/-! The concrete Beacon controller never reads its private record-request kind ledger. This file proves the actual state and trusted-query operations used to derive that property for its full lifecycle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView
open RegistrationNativeBeaconFrontend (M Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {KemSK Auxiliary Value Result : Type} {mlSource : RegistrationNativeMldsa.Source}

def erase (before : EnvState Auxiliary) : EnvState Auxiliary := { before with recordRequests := [] }

def project (before : RegistrationNativeBeaconFrontend.State mlSource × EnvState Auxiliary) :=
  (before.1, erase before.2)

def close (work : M n KemSK mlSource Auxiliary Value) :
    StateT (RegistrationNativeBeaconFrontend.State mlSource × EnvState Auxiliary)
      (OracleComp (Trusted n KemSK)) Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2

def Stable (work : M n KemSK mlSource Auxiliary Value) : Prop :=
  RegistrationStateView.Stable project (close work)

/-- The nested native owner/Env execution keeps its full actual result and owner state under Env projection. -/
theorem run_input (work : M n KemSK mlSource Auxiliary Value) (stable : Stable work)
    (owners : RegistrationNativeBeaconFrontend.State mlSource) (before : EnvState Auxiliary) :
    Prod.map id erase <$> (work.run owners).run before =
      Prod.map id erase <$> (work.run owners).run (erase before) := by
  have law := congrArg (fun distribution =>
    (fun result => ((result.1, result.2.1), result.2.2)) <$> distribution) (stable (owners, before))
  simp only [close, StateT.run, Functor.map_map, Prod.map, id_eq, project, Prod.mk.eta] at law ⊢
  exact law

private theorem close_pure (value : Value) :
    close (pure value : M n KemSK mlSource Auxiliary Value) = pure value := by
  funext before
  simp only [close, StateT.run_pure, map_pure]
  rfl

private theorem close_bind (work : M n KemSK mlSource Auxiliary Value)
    (next : Value → M n KemSK mlSource Auxiliary Result) :
    close (work >>= next) = (close work >>= fun value => close (next value)) := by
  funext before
  simp only [close, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]

/-- Pure controller replies retain the same owner roster and complete retained Env. -/
theorem pure_stable (value : Value) : Stable (pure value : M n KemSK mlSource Auxiliary Value) := by
  unfold Stable
  rw [close_pure]
  exact RegistrationStateView.pure_stable project (fun _ => rfl) value

/-- Concrete nested owner/Env continuations compose without exposing the erased analysis ledger. -/
theorem bind_stable (work : M n KemSK mlSource Auxiliary Value)
    (next : Value → M n KemSK mlSource Auxiliary Result)
    (first : Stable work) (rest : ∀ value, Stable (next value)) : Stable (work >>= next) := by
  unfold Stable at *
  rw [close_bind]
  exact RegistrationStateView.bind_stable project (close work) _ first rest

/-- Adaptive trusted controller programs preserve the same complete retained owner and Env state. -/
theorem program_stable {I : Type} {spec : OracleSpec I}
    (implementation : QueryImpl spec (M n KemSK mlSource Auxiliary))
    (step : ∀ query, Stable (implementation query)) (work : OracleComp spec Value) :
    Stable (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_stable value
  | query_bind query next ih =>
      simpa only [simulateQ_bind, simulateQ_spec_query] using
        bind_stable (implementation query) (fun reply => simulateQ implementation (next reply)) (step query) ih

/-- Owner lookup reads the actual unchanged roster. -/
theorem get_stable : Stable (get : M n KemSK mlSource Auxiliary (RegistrationNativeBeaconFrontend.State mlSource)) := by
  intro before
  change Prod.map id project <$> (pure (before.1, before) : OracleComp (Trusted n KemSK) _) =
    Prod.map id project <$> pure (before.1, project before)
  simp only [map_pure, Prod.map, id_eq, project, erase]

/-- Owner updates retain the complete Env and touch no erased input. -/
theorem modify_stable (change : RegistrationNativeBeaconFrontend.State mlSource → RegistrationNativeBeaconFrontend.State mlSource) :
    Stable (modify change : M n KemSK mlSource Auxiliary Unit) := by
  intro before
  change Prod.map id project <$> (pure ((), (change before.1, before.2)) : OracleComp (Trusted n KemSK) _) =
    Prod.map id project <$> pure ((), (change before.1, erase before.2))
  simp only [map_pure, Prod.map, id_eq, project, erase]

/-- Owner replacement has the same exact public and private owner state. -/
theorem set_stable (owners : RegistrationNativeBeaconFrontend.State mlSource) :
    Stable (set owners : M n KemSK mlSource Auxiliary Unit) := by
  intro before
  change Prod.map id project <$> (pure ((), (owners, before.2)) : OracleComp (Trusted n KemSK) _) =
    Prod.map id project <$> pure ((), (owners, erase before.2))
  simp only [map_pure, Prod.map, id_eq, project, erase]

/-- Actual external trusted queries do not inspect the controller's local analysis ledger. -/
theorem lift_stable (work : OracleComp (Trusted n KemSK) Value) :
    Stable (StateT.lift (StateT.lift work) : M n KemSK mlSource Auxiliary Value) := by
  intro before
  simp only [StateT.run, close, StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure, bind_pure_comp, Functor.map_map, Prod.map, id_eq, project, erase]

/-- An actual Env update is allowed exactly when its retained output ignores the omitted input. -/
theorem update_stable (change : EnvState Auxiliary → EnvState Auxiliary)
    (commutes : ∀ before, erase (change before) = erase (change (erase before))) :
    Stable (RegistrationNativeBeaconFrontend.updateEnv change : M n KemSK mlSource Auxiliary Unit) := by
  intro before
  change Prod.map id project <$> (pure ((), (before.1, change before.2)) : OracleComp (Trusted n KemSK) _) =
    Prod.map id project <$> pure ((), (before.1, change (erase before.2)))
  simp only [map_pure, Prod.map, id_eq, project]
  rw [commutes before.2]

end BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.run_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.run_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.pure_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.pure_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.bind_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.bind_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.program_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.get_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.get_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.modify_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.modify_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.set_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.set_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.lift_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.lift_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.update_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconEnvView.update_stable
