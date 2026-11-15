-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial

/-! Every actual response-authentication callback uses the same mandatory verifier and shared World hash program as the scalar-free finishing controller. Owner and local environment state remain unchanged by this finite authentication component, including rejection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

/-- Callback operands, optional replies and the shared hash request are those of the actual native controller. -/
theorem query (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (request : RegistrationAuthenticationExecutor.Request) :
    RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup mlSource request =
      StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify request))) := by
  cases request with
  | hash request =>
      apply StateT.ext
      intro owners
      apply StateT.ext
      intro env
      simp only [RegistrationNativeBeaconFrontend.authentication, RegistrationNativeBeaconFrontend.hash,
        RegistrationNativeBeaconFrontend.effect, RegistrationAuthenticationCompiler.callbacks,
        simulateQ_map, simulateQ_spec_query,
        RegistrationBeaconReferenceNativeRecord.environment,
        StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]
      rfl
  | mldsa request | ed25519 request => rfl

/-- The entire actual verifier execution retains every reached World effect and all optional failures before root preparation. -/
theorem program (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    simulateQ (RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup mlSource) work =
      StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify) work))) := by
  have restriction : RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup mlSource =
      (RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) ∘ₛ
        RegistrationAuthenticationCompiler.callbacks (n := n) setup.source.crypto mlSource.verify).liftTarget
          (RegistrationNativeBeaconFrontend.M n KemSK mlSource Auxiliary) := by
    funext request
    rw [QueryImpl.liftTarget_apply, QueryImpl.apply_compose]
    exact query setup mlSource request
  rw [restriction, simulateQ_liftTarget, QueryImpl.simulateQ_compose]
  rfl

/-- Actual response authentication is interpreted on the existing complete native World and private KEM pool. -/
theorem native_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (mlSource : RegistrationNativeMldsa.Source)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.authentication (n := n) setup mlSource) work) =
      simulateQ (RegistrationBeaconReferenceNativeEffects.native setup checks representation created)
        (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify) work) := by
  rw [program, RegistrationBeaconReferenceNativeEffects.beacon_program]

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication.query
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication.program
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication.native_program
