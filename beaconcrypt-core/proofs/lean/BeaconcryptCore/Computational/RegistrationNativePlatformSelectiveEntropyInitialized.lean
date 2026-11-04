-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The actual corrected raw frontend closes over its literal selective World backend. Registration callbacks retain their restricted source effects; ordinary routes keep their actual post-send allocator and full shared platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyInitialized
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


open RegistrationNativeHiddenEnvironmentWorld (lower)

/-- Genuine source startup discharges physical allocation for the complete adaptive source-to-gated-environment law. -/
theorem initialized_source
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (secret : Secret) (started : RegistrationNativeHiddenStartup.Started source)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (after : Secret)
    (supported : (((some started,shell),control),after) ∈ support
      (CborRawRecordOriginFlatten.interpret service codec route
        (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret))
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState Platform source)))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    let initial : RegistrationNativePlatformHiddenAllocationCore.State n Platform
      (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret source :=
      (((((started.native.frontend,previous),privateBefore),shell),control),after)
    (lower service codec route (simulateQ
      (RegistrationNativePlatformSelectiveEntropyExecution.handler (n := n) setup checks wire source started.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        serverKeyId bounds mode work))).run initial =
      (lower service codec route (simulateQ
        (RegistrationNativePlatformSelectiveEntropyQuery.reference (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source started.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup)
        (RegistrationNativeLedger.wrap setup.source.crypto
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds
          (RegistrationNativeInterface.asModeO mode work)))).run initial := by
  let initial : RegistrationNativePlatformHiddenAllocationCore.State n Platform
      (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret source :=
    (((((started.native.frontend,previous),privateBefore),shell),control),after)
  have reached := RegistrationNativePlatformHiddenAllocationStartup.initialized setup ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed) privateBefore.1.provider previous privateBefore.2 service codec route secret started shell control after supported
  have valid : RegistrationNativePlatformHiddenAllocationCore.Holds initial := ⟨reached.length,reached.indexed,reached.cursor⟩
  exact RegistrationNativePlatformSelectiveEntropyAdaptive.full_source setup checks wire source started.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route
    startup serverKeyId bounds mode work initial valid
end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyInitialized.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyInitialized.initialized_source
