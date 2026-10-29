-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage

/-! The private source lens restores only the selected prekey role. The actual native owner-list controller and the scalar-free ordinary prefix use exactly the same external effects and full reached owner/environment state; selected DH restoration occurs solely in the native interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceCompiler (SelectedOwner restoreOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeStage (Local lower native)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem lower_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : StateT (EnvState RegistrationServerRoleBackend.State)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value)
    (before : Local n KemSK mlSource) :
    (lower setup checks representation created work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (work.run before.1)).run before.2 := rfl

noncomputable def source (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec
      (StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK))) :=
  RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
    (RegistrationBeaconReferenceSource.backend setup owner oneTime) RegistrationBeaconReferenceSource.visit

/-- Every actual native callback leaves the owner list unchanged in this phase while retaining its actual external state. -/
theorem owned_query (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup (restoreOwner scalar owner) oneTime query =
      StateT.lift (source setup scalar owner oneTime query) := by
  rw [RegistrationBeaconReferenceSource.agreement_native]
  cases query with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | root request => rfl
  | dh request =>
      cases role : request.secret_role with
      | LocalIdentity | ServerEphemeral | BeaconOneTime =>
          simp only [RegistrationBeaconRootInterpreter.sourceImpl, source, role]
      | BeaconPrekey =>
          simp only [RegistrationBeaconRootInterpreter.sourceImpl, source, role, bind_pure_comp]
          apply StateT.ext
          intro owners
          simp only [StateT.run_map, StateT.run_lift, Functor.map_map, bind_pure_comp]

/-- Complete actual agreement execution retains every owner and environment field, including all optional failures. -/
theorem owned_program (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    simulateQ (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup (restoreOwner scalar owner) oneTime) work =
      StateT.lift (simulateQ (source setup scalar owner oneTime) work) := by
  have same : RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup (restoreOwner scalar owner) oneTime =
      (source (n := n) (Auxiliary := Auxiliary) setup scalar owner oneTime).liftTarget
        (RegistrationNativeBeaconFrontend.M n KemSK mlSource Auxiliary) :=
    by
      funext query
      rw [QueryImpl.liftTarget_apply]
      exact owned_query (n := n) (Auxiliary := Auxiliary) setup scalar owner oneTime query
  rw [same, simulateQ_liftTarget]
  rfl

/-- Lowering the private selected-role restoration uses the actual global native primitive interpretation. -/
theorem lower_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    lower (n := n) setup checks representation created (source setup scalar owner oneTime query) =
      native setup checks representation created scalar owner oneTime query := by
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

/-- Arbitrary reached native agreement programs share the concrete global source state. -/
theorem lower_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    lower setup checks representation created (simulateQ (source (n := n) setup scalar owner oneTime) work) =
      simulateQ (native setup checks representation created scalar owner oneTime) work := by
  rw [RegistrationBeaconReferenceNativeStage.lower_program]
  congr 1
  funext query
  exact lower_query setup checks representation created scalar owner oneTime query

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.owned_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.owned_query

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.owned_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.owned_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.lower_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.lower_query

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks.lower_program
