-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReached
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto
/-! The same source trace retains its physical hidden-slot receipts and erases to the literal reference view at any reached private record state. Sampling prefixes keep their actual cache and accounting coordinates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView
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



/-- Source-derived hidden-slot receipts use the same supported trace and reached private state. -/
theorem hidden (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (lowerCodec : Codec Reader Response) (initialSecret : Secret)
    (result : RegistrationNativePlatformSelectiveRecordTraceHidden.Result n KemSK ProviderState Platform Secret Value source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service lowerCodec route job
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret))
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) :
    RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup seed scalar candidate
      (RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) produced) := by
  have invariant := RegistrationNativePlatformSelectiveRecordTraceHidden.initialized setup checks wire seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary
    service lowerCodec route initialSecret result supported
  intro finished present
  cases outcome : result.1.1.1 with
  | none => simp [RegistrationNativeRecordPackage.nativeView,outcome] at present
  | some born =>
    have same : born = finished := by simpa only [RegistrationNativeRecordPackage.nativeView,outcome,Option.mem_some_iff] using present
    subst finished
    simpa only [RegistrationNativePlatformSelectiveRecordTraceHidden.Holds,outcome,RegistrationNativeRecordPackage.nativeView] using invariant

/-- The full original record view is recovered without changing the reached cache or accounting prefix. -/
theorem erase (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (lowerCodec : Codec Reader Response) (initialSecret : Secret)
    (produced : Secret → List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) :
    (fun result => RegistrationNativePlatformSelectiveRecordTraceView.erase
      (RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) (produced result.2))) <$>
      CborRawRecordOriginFlatten.interpret service lowerCodec route job
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret =
    (fun result => RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) (produced result.2)) <$>
      CborRawRecordOriginFlatten.interpret service lowerCodec route plain
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret := by
  have sourceLaw := congrArg (Functor.map (fun result : ((RegistrationNativeEntropyRun.Outcome
    (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source) Value × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret =>
      RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) (produced result.2)))
    (RegistrationNativePlatformSelectiveRecordTraceReached.interpret_erase setup checks wire seed scalar candidate provider selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary
      route service lowerCodec initialSecret)
  simpa only [Functor.map_map,RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativeRecordPackage.nativeView] using sourceLaw

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView.hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView.erase
