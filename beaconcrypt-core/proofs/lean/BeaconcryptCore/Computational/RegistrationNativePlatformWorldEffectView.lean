-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler
import BeaconcryptCore.Computational.RegistrationNativeWorldViewEffects
/-! The restricted source client may project the named native/Envcoin instrumentation after each effect. This interpreter is derived from the same original private World execution, retains true uniforms and every operational coordinate, and exposes no private World field to the public client. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectView
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationNativeWorldView (project)
variable {n : Nat} {Public A : Type}

noncomputable def implementation : QueryImpl (Spec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun query => fun before => Prod.map id project <$>
    (RegistrationNativePlatformWorldEffectClosure.implementation query).run before

private theorem lift_apply {S V : Type} (work : ProbComp V) (before : S) :
    (StateT.lift work : StateT S ProbComp V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem query (request : (Spec n).Domain) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (RegistrationNativePlatformWorldEffectClosure.implementation request).run before =
      (implementation request).run (project before) := by
  cases request with
  | inl effect => exact RegistrationNativeWorldViewEffects.effects_input effect before
  | inr coin =>
    simp only [RegistrationNativePlatformWorldEffectClosure.implementation, implementation,
      StateT.run, lift_apply, Functor.map_map, Prod.map, id_eq,
      RegistrationNativeWorldView.project_idempotent]

/-- Projection after the complete original effect program is exactly the interpreter that projects at each reached query, without omitting any actual random draw or failed effect. -/
theorem program (work : OracleComp (Spec n) A) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (simulateQ RegistrationNativePlatformWorldEffectClosure.implementation work).run before =
      (simulateQ implementation work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project query work before

noncomputable def close (work : StateT Public (OracleComp (Spec n)) A) :
    StateT (PqxdhRecordLiftWorld.State n) (StateT Public ProbComp) A := fun current previous =>
  (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ implementation (work.run previous)).run current

/-- One public state is threaded beside the same private World; only the explicitly named World instrumentation is projected. -/
theorem source (work : StateT Public (OracleComp (Spec n)) A)
    (before : PqxdhRecordLiftWorld.State n) (previous : Public) :
    (fun result => ((result.1.1, project result.1.2), result.2)) <$>
      ((RegistrationNativePlatformWorldEffectClosure.close work).run before).run previous =
      ((close work).run (project before)).run previous := by
  have same := congrArg (fun action => (fun result => ((result.1.1, result.2), result.1.2)) <$> action)
    (program (work.run previous) before)
  simpa only [close, RegistrationNativePlatformWorldEffectClosure.close, StateT.run,
    Functor.map_map, Prod.map, id_eq] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectView.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectView.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectView.source
