-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative
/-! The actual corrected raw frontend closes over its literal selective World backend. Registration callbacks retain their restricted source effects; ordinary routes keep their actual post-send allocator and full shared platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


local notation "actualTyped" => RegistrationNativePlatformSelectiveEntropyExecution.handler (n := n) setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actualRaw" => RegistrationNativePlatformSelectiveEntropyNative.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- The full corrected raw callback closes exactly the original raw adapter over the actual typed stateful callback. -/
theorem handler_source (query : RegistrationNativeInterface.Spec.Domain) :
    actualRaw query = simulateQ actualTyped
      (RegistrationNativeRawAdapter.adapter (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) query) := by
  unfold RegistrationNativePlatformSelectiveEntropyNative.handler RegistrationNativePlatformPublicFrontendCaps.raw QueryImpl.compose
  rw [RegistrationNativePlatformSelectiveEntropyEffects.close_program]
  rfl

/-- Arbitrary raw programs retain the complete typed source state under exact adapter compilation. -/
theorem raw_source (work : OracleComp RegistrationNativeInterface.Spec Value) :
    simulateQ actualRaw work = simulateQ actualTyped
      (RegistrationNativeRawAdapter.compile (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) work) := by
  unfold RegistrationNativeRawAdapter.compile
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact handler_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query

/-- Every original observation mode preserves the complete ledger and actual source/private/P poststate. -/
theorem run_source (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Platform source) :
    RegistrationNativePlatformSelectiveEntropyExecution.run setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before =
      (simulateQ actualRaw
        (RegistrationNativeLedger.wrap setup.source.crypto
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
          serverKeyId bounds (RegistrationNativeInterface.asModeO mode work))).run before := by
  unfold RegistrationNativePlatformSelectiveEntropyExecution.run RegistrationNativeFullCompiler.compile
  rw [← raw_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer]
end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution.raw_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution.run_source
