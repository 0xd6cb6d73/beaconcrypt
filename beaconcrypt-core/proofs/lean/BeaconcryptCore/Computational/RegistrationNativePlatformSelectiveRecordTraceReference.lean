-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto
/-! Chronology erasure reaches the literal gated native reference program in each record interpretation. Source and reference execute their own identical reached cache, slot map, platform and failure histories; no real and ideal reply supports are identified. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReference
open PqxdhServerAuthExperiment (Setup Checks Codec)
open BeaconcryptCore.Refinement
variable {Value : Type}
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

variable (providerState : ProviderState) (previous : Platform)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

open RegistrationNativeRecordPackage (View)
open RegistrationNativePlatformSelectiveRecordTraceStartup (Extra program forget)
open RegistrationNativePlatformInstallKernelStorage (Selected)

variable (route : RawCtxServerRouting.SenderDecoder)
local notation "job" => program setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary
local notation "plain" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous (RegistrationNativeHiddenInterpreter.initial providerState,known) bounds mode adversary
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)


/-- The actual source trace erases to its literal gated native reference in every record interpretation, retaining its same complete result and physical map. -/
theorem ctx_erase (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode) :
    RegistrationNativePlatformSelectiveRecordTraceView.erase <$> RegistrationNativeRecordPackage.ctx modes setup codec route job =
      RegistrationNativeRecordPackage.ctx modes setup codec route plain := by
  rw [RegistrationNativePlatformSelectiveRecordTraceView.ctx_erase setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary route modes,
    RegistrationNativeRecordPackage.ctx_source,RegistrationNativeRecordPackage.ctx_source]
  rw [RegistrationNativePlatformSelectiveEntropyStartup.program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous
    (RegistrationNativeHiddenInterpreter.initial providerState,known) bounds mode adversary
    (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec) codec route PqxdhRecordLiftIdeal.CtxPrivate.initial]

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReference
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReference.ctx_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReference.ctx_erase
