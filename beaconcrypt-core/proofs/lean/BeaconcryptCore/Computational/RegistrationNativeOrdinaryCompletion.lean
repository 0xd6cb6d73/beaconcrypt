-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource

/-! Ordinary-owner translation acts only on root preparation. The actual terminal completion contains only paired material/publication and World effects, so its full original local AST and chronology are unchanged. Its retained Ready has already been translated by the successful preparation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryCompletion
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem public_program (setup : Setup base KemSK) (localScalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
        (simulateQ RegistrationBeaconReferenceFinish.service work) =
      simulateQ RegistrationBeaconReferenceFinish.service work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativePublicOwners.ordinary setup localScalar ∘ₛ RegistrationBeaconReferenceFinish.service =
      RegistrationBeaconReferenceFinish.service (n := n) (KemSK := KemSK) := by
    funext query
    simp only [QueryImpl.compose, RegistrationBeaconReferenceFinish.service, simulateQ_spec_query,
      RegistrationNativePublicOwners.ordinary]
  rw [same]

private theorem effect (setup : Setup base KemSK) (localScalar : PqxdhJointGapDh.ScalarBytes)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
      (RegistrationBeaconReferenceCompiler.effect query) =
      RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK) query := by
  simp only [RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query, RegistrationNativePublicOwners.ordinary]

/-- The complete original terminal completion is unchanged by ordinary-owner translation, including every failure and World phase transition. -/
theorem complete (setup : Setup base KemSK) (localScalar : PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
        (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) setup.source owner ready).run current).run env) =
      (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) setup.source owner ready).run current).run env) := by
  rw [RegistrationNativeSelectiveBeaconCompletionSource.complete_source, simulateQ_bind, public_program]
  apply bind_congr
  intro completed
  cases completed with
  | fail error | div =>
      simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
        StateT.run_lift, StateT.run_map, seqRight_eq_bind, bind_pure_comp, Functor.map_map,
        simulateQ_map, effect]
  | ok completed => cases completed with
    | Err previous =>
        simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
          StateT.run_lift, StateT.run_map, seqRight_eq_bind, bind_pure_comp, Functor.map_map,
          simulateQ_map, effect]
    | Ok published =>
        simp only [RegistrationBeaconReferenceCompletion.after, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryCompletion.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryCompletion.complete
