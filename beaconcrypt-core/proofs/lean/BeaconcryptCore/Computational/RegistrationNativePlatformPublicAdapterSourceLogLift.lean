-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
/-! Operations without signing or first-record stages retain the actual source outcome and every backend coordinate while carrying the existing observation log. Callback markers observe that same execution, including its terminal failure state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceRuntime (M Objects run join)
open RegistrationNativePlatformPublicAdapterSourceEvents (Log State Outcome)
open RegistrationNativePlatformSdkReification (Backend)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {KemSK R P A :Type}

noncomputable def lift (operation :M n KemSK R P A) :M n KemSK R (P×Log n KemSK R P) A :=
  fun objects=>⟨fun before=>(fun result=>(result.1,(result.2.1,(result.2.2,before.2.2)))) <$>
    (operation.run objects).run.run (before.1,before.2.1)⟩

theorem run_lift (operation :M n KemSK R P A) (before :State n KemSK R P) :
    run (lift operation) before=
      (fun result=>(result.1,(result.2.1,(result.2.2,before.backend.2.2)))) <$>
        run operation (RegistrationNativePlatformPublicAdapterSourceEvents.store before) :=rfl

theorem lift_erase (operation :M n KemSK R P A) (before :State n KemSK R P) :
    RegistrationNativePlatformPublicAdapterSourceEvents.outcome <$>run (lift operation) before=
      run operation (RegistrationNativePlatformPublicAdapterSourceEvents.store before) :=by
  rw [run_lift,Functor.map_map]
  exact LawfulFunctor.id_map _

noncomputable def ofOutcome (operation :State n KemSK R P→ProbComp (Outcome n KemSK R P A)) :
    M n KemSK R (P×Log n KemSK R P) A :=
  fun objects=>⟨fun backend=>operation (join objects backend)⟩

theorem run_outcome (operation :State n KemSK R P→ProbComp (Outcome n KemSK R P A))
    (before :State n KemSK R P) :run (ofOutcome operation) before=operation before :=rfl

noncomputable def callback (query :RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Domain)
    (operation :M n KemSK R (P×Log n KemSK R P) (RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Range query)) :
    M n KemSK R (P×Log n KemSK R P) (RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Range query) :=
  fun objects=>⟨fun backend=>RegistrationNativePlatformPublicAdapterSourceEvents.callback query (run operation) (join objects backend)⟩

theorem run_callback (query :RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Domain)
    (operation :M n KemSK R (P×Log n KemSK R P) (RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Range query))
    (before :State n KemSK R P) :
    run (callback query operation) before=
      RegistrationNativePlatformPublicAdapterSourceEvents.callback query (run operation) before :=by
  change RegistrationNativePlatformPublicAdapterSourceEvents.callback query (run operation)
    (join (RegistrationNativePlatformPublicAdapterSourceRuntime.objects before) before.backend)=_
  rw [RegistrationNativePlatformPublicAdapterSourceRuntime.join_objects]

theorem callback_erase (query :RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Domain)
    (operation :M n KemSK R (P×Log n KemSK R P) (RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Range query))
    (plain :M n KemSK R P (RegistrationNativePlatformPublicAdapterSourceEvents.Spec.Range query))
    (law :∀before,RegistrationNativePlatformPublicAdapterSourceEvents.outcome <$>run operation before=
      run plain (RegistrationNativePlatformPublicAdapterSourceEvents.store before))
    (before :State n KemSK R P) :
    RegistrationNativePlatformPublicAdapterSourceEvents.outcome <$>run (callback query operation) before=
      run plain (RegistrationNativePlatformPublicAdapterSourceEvents.store before) :=by
  rw [run_callback]
  exact RegistrationNativePlatformPublicAdapterSourceEvents.callback_erase query (run operation) (run plain) law before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.run_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.run_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.lift_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.lift_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.run_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.run_callback
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.callback_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift.callback_erase
