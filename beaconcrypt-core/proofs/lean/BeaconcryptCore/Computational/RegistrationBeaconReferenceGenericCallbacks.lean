-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks

/-! Private selected-role restoration commutes with the concrete ordinary interpreter. The same algebraic callback law applies to selected and locally materialized owners and retains the entire caller environment/private state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceGenericStage (Local lower native)
open RegistrationBeaconReferenceNativeCallbacks (source)
variable {n : Nat} {ι KemSK Auxiliary Private Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem lower_run (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value)
    (before : Local Auxiliary Private) :
    (lower setup trusted work).run before = (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ trusted (work.run before.1)).run before.2 := rfl

/-- The selected DH callback and its actual visit marker lower to the same native continuation. -/
theorem lower_query (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (scalar : PqxdhJointGapDh.ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    lower (Auxiliary := Auxiliary) setup trusted (source setup scalar owner oneTime query) =
      native setup trusted scalar owner oneTime query := by
  cases query with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | root request => rfl
  | dh request =>
      cases role : request.secret_role with
      | LocalIdentity | ServerEphemeral | BeaconOneTime =>
          simp only [RegistrationBeaconRootInterpreter.sourceImpl, source, native, role]
      | BeaconPrekey =>
          apply StateT.ext
          intro before
          simp only [source, native, RegistrationBeaconRootInterpreter.sourceImpl, role, StateT.run_bind]
          rw [lower_run, lower_run]
          simp only [RegistrationBeaconReferenceSource.visit, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, pure_bind, map_pure]

/-- Whole actual native agreement programs use the same concrete ordinary interpreter on every adaptive branch. -/
theorem lower_program (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (scalar : PqxdhJointGapDh.ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    lower (Auxiliary := Auxiliary) setup trusted (simulateQ (source setup scalar owner oneTime) work) =
      simulateQ (native setup trusted scalar owner oneTime) work := by
  rw [RegistrationBeaconReferenceGenericStage.lower_program]
  congr 1
  funext query
  exact lower_query setup trusted scalar owner oneTime query

end BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks.lower_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks.lower_query
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericCallbacks.lower_program
