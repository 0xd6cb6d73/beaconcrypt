-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks

/-! This private source interpretation restores only the selected prekey DH calls and the actual native root callback. The executable ordinary prefix remains scalar-free and uses its generated indexed KEM handle. Every request is logged at its original native position, with all nested owner/environment and external source state retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationBeaconReferenceCompiler
open RegistrationBeaconReferenceCallbacks
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

/-- The literal private root request occurs only in this source interpreter, after the public collection prefix. -/
noncomputable def backend (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) : QueryImpl RegistrationAgreementExecutor.Spec
      (StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)))
  | .root request => do
      modify fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded (.root request) }
      pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))
  | query => trustedBackend setup owner oneTime query

def visit (point : PqxdhBeaconPhase2Preparation.Word32) :
    StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Unit :=
  modify fun env => { env with requests := env.requests ++ [.dh ⟨.BeaconPrekey, point⟩] }

/-- The exact actual native callback is recovered with no pin condition or assumed callback simulation. -/
theorem agreement_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) :
    RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup (restoreOwner scalar owner) oneTime =
      RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
        (fun query => StateT.lift (backend setup owner oneTime query))
        (fun point => StateT.lift (visit point)) := by
  funext query
  cases query with
  | convertPublic key => exact RegistrationBeaconReferenceCallbacks.agreement_native setup scalar owner oneTime (.convertPublic key) trivial
  | convertSecret role => exact RegistrationBeaconReferenceCallbacks.agreement_native setup scalar owner oneTime (.convertSecret role) trivial
  | generate role => exact RegistrationBeaconReferenceCallbacks.agreement_native setup scalar owner oneTime (.generate role) trivial
  | encapsulate key => exact RegistrationBeaconReferenceCallbacks.agreement_native setup scalar owner oneTime (.encapsulate key) trivial
  | decapsulate ciphertext => exact RegistrationBeaconReferenceCallbacks.agreement_native setup scalar owner oneTime (.decapsulate ciphertext) trivial
  | root request => rfl
  | dh request =>
      cases role : request.secret_role with
      | BeaconPrekey =>
          simp only [RegistrationNativeBeaconFrontend.agreement, RegistrationNativeBeaconFrontend.agreementCore,
            RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
            RegistrationNativeKemInterface.other, simulateQ_spec_query, restoreOwner,
            RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive,
            RegistrationBeaconRoleBackend.native, role, StateT.run,
            RegistrationNativeBeaconFrontend.sample,
            RegistrationBeaconRootInterpreter.sourceImpl, visit, RegistrationNativeBeaconFrontend.updateEnv]
          simp only [StateT.monad_pure_def, StateT.pure, map_pure, simulateQ_pure]
          cases request
          cases role
          rfl
      | LocalIdentity | ServerEphemeral | BeaconOneTime =>
          simpa only [RegistrationBeaconRootInterpreter.sourceImpl, role, backend] using
            RegistrationBeaconReferenceCallbacks.agreement_native setup scalar owner oneTime (.dh request)
              (by simp [OrdinaryAgreement, role])

/-- Any actual native continuation, including optional failures and the final root request, retains exactly the same full source state. -/
theorem program_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    simulateQ (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup
      (restoreOwner scalar owner) oneTime) work =
    simulateQ (RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
      (fun query => StateT.lift (backend setup owner oneTime query))
      (fun point => StateT.lift (visit point))) work := by
  rw [agreement_native]

end BeaconcryptCore.Computational.RegistrationBeaconReferenceSource

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceSource.agreement_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceSource.agreement_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceSource.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceSource.program_native
