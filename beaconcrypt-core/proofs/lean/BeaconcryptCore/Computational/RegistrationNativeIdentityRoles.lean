-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend

/-! Source receipts for the generated credential's public fields and converted-static-DH callback. The executable role uses the private indexed service rather than an Ed25519 seed or converted secret. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityRoles
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity
open RegistrationNativeIdentityFrontend
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- Outgoing source fields use the public identity from this same generated credential. -/
theorem inputs_source (setup : Setup base KemSK) (owner : Owner source) (seed : IdentitySeed)
    (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed) :
    inputs owner = RegistrationNativeBeaconFrontend.inputs setup (restore seed owner) := by
  simp only [inputs, RegistrationNativeBeaconFrontend.inputs, restore, publicKey]

/-- Native local-static-DH operands are forwarded unchanged to the generated identity handle. -/
theorem local_dh (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (peer : PqxdhBeaconPhase2Preparation.Word32) :
    primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime (.dh ⟨.LocalIdentity, peer⟩) =
      StateT.lift (StateT.lift (RegistrationNativeIdentityCallbacks.dh (Ambient n KemSK) owner.identity peer)) := rfl

/-- Interpreting the actual native local-static-DH callback recovers its optional source value and retains the whole public owner/environment plus unrelated auxiliary state. -/
theorem local_dh_source {Other : Type} (setup : Setup base KemSK)
    (ordinary : QueryImpl (Ambient n KemSK) (StateT Other ProbComp))
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (peer : PqxdhBeaconPhase2Preparation.Word32) (seed : IdentitySeed)
    (owners : State source) (env : EnvState Auxiliary)
    (before : RegistrationNativeIdentityInterface.State Other)
    (owned : RegistrationNativeIdentityCallbacks.Owns setup.joint before.2 owner.identity seed) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (RegistrationNativeIdentityInterface.source (Ambient n KemSK) ordinary setup.joint)
        (((primitive (Auxiliary := Auxiliary) setup owner oneTime (.dh ⟨.LocalIdentity, peer⟩)).run owners).run env)).run before =
      pure (((RegistrationAgreementRoot.nativeOption
        ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer peer)).map PqxdhRootTableInitialization.rootArray), owners), env), before.1) := by
  rw [local_dh]
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map,
    simulateQ_map]
  have actual := congrArg (fun work => (fun answer => (((answer.1, owners), env), answer.2)) <$> work)
    (RegistrationNativeIdentityCallbacks.dh_source ordinary setup.joint owner.identity seed peer before owned)
  simpa only [RegistrationAgreementShared.PrimitiveSpec, RegistrationAgreementShared.PrimitiveRequest.toRequest,
    RegistrationAgreementExecutor.Spec, OracleSpec.Range, Functor.map_map, map_pure, Prod.map_def, id_eq] using actual

end BeaconcryptCore.Computational.RegistrationNativeIdentityRoles

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRoles.inputs_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRoles.inputs_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRoles.local_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRoles.local_dh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRoles.local_dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRoles.local_dh_source
