-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEnvironment

/-! The actual corrected full raw compiler closes through its selective opaque-material backend with the original ledger and persistent platform state. This exact query-tree law is independent of the later primitive hybrid and event comparisons. Allocator coins use the explicitly counted comparison embedding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open BeaconcryptCore.Refinement
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK ProviderState Platform E Value : Type} {base : OracleSpec ι}

open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def handler : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (State n KemSK ProviderState Platform source) (OracleComp (PqxdhRecordLiftInterface.WorldSpec n))) :=
  ((RegistrationNativePlatformSelectiveEntropyBackend.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider).mapStateTBase
    (RegistrationNativePlatformPublicFrontend.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)).flattenStateT

noncomputable def run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK ProviderState Platform source) :=
  (simulateQ (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)).run before

/-- The complete original full ledger and all reached public/opaque/P states follow from the actual callback compiler, without a whole-program relationship premise. -/
theorem run_source (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK ProviderState Platform source) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
        (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          serverKeyId bounds mode work before.1)).run before.2 =
      run setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before := by
  have whole := simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativePlatformSelectiveEntropyBackend.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
    (RegistrationNativePlatformPublicFrontend.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)
    before.1 before.2
  have mapped := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> action) whole
  simpa only [RegistrationNativePlatformPublicFrontend.run, run, handler, Functor.map_map,
    Function.comp_def, Prod.mk.eta, id_map'] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution.run_source
