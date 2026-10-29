-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceCompletion

/-! Local ordinary-owner materialization changes only prepare queries. All actual native trusted callbacks, returned-reference demands, openings, installs and terminal lifecycle effects are forwarded unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationBeaconReferenceCompiler (Spec SelectedOwner effect)
open RegistrationNativePublicOwners (ordinary)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Value Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- The actual trusted interface contains no prepare query. -/
theorem trusted_program (setup : Setup base KemSK) (scalar : ScalarBytes)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    simulateQ (ordinary setup scalar) (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work) =
      simulateQ RegistrationBeaconReferenceCompiler.trustedLift work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  cases query <;> simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceCompiler.trustedLift,
    RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
    simulateQ_spec_query, ordinary]

/-- Native lifecycle and record effects are literally forwarded after preparation. -/
theorem effects_program (setup : Setup base KemSK) (scalar : ScalarBytes)
    (work : OracleComp (EnvEffects n) Value) :
    simulateQ (ordinary setup scalar) (simulateQ (effect (KemSK := KemSK)) work) =
      simulateQ effect work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- Material demand keeps the translated reference actually returned by the earlier source preparation. -/
theorem service_program (setup : Setup base KemSK) (scalar : ScalarBytes)
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    simulateQ (ordinary setup scalar) (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK)) work) =
      simulateQ RegistrationBeaconReferenceFinish.service work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- The actual no-prepare settling branch, including every abort, is unchanged by local materialization. -/
theorem after_program (setup : Setup base KemSK) (scalar : ScalarBytes)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (result : RustM RegistrationNativePairedBeaconService.Result) :
    simulateQ (ordinary setup scalar)
      (((RegistrationBeaconReferenceCompletion.after effect owner result :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) =
      (((RegistrationBeaconReferenceCompletion.after effect owner result :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) := by
  cases result with
  | fail error | div =>
      simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
        seqRight_eq_bind, StateT.run_map, StateT.run_lift, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, effect, ordinary]
  | ok result => cases result with
    | Err error =>
        simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
          seqRight_eq_bind, StateT.run_map, StateT.run_lift, bind_pure_comp, simulateQ_map,
          simulateQ_spec_query, effect, ordinary]
    | Ok completed =>
        simp only [RegistrationBeaconReferenceCompletion.after, StateT.run_bind,
          StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]

/-- Complete post-root execution contains only material, raw and lifecycle operations; ordinary preparation adds no later query or state change. -/
theorem complete_program (setup : Setup base KemSK) (scalar : ScalarBytes)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (ready : RegistrationBeaconReferenceRoot.Ready) :
    simulateQ (ordinary setup scalar)
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) =
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) := by
  have settle : RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary)
      setup.source owner ready = (do
        let completed ← StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceFinish.service
          (RegistrationNativePairedBeaconService.admitted setup.source owner.worldOwner owner.pin.binding.identity_key_id
            ready.descriptor ready.reference)))
        RegistrationBeaconReferenceCompletion.after effect owner completed) := by
    unfold RegistrationBeaconReferenceFinish.complete
    apply bind_congr
    intro result
    cases result with
    | fail error | div => rfl
    | ok result => cases result <;> rfl
  rw [settle]
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, simulateQ_bind, bind_map_left]
  rw [service_program]
  apply bind_congr
  intro completed
  exact after_program setup scalar owner current env completed

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.trusted_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.effects_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.effects_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.service_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.service_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.after_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.after_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.complete_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper.complete_program
