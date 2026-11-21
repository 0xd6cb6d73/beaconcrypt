-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceHidden
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView
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

def erase (view : View n (Extra n KemSK ProviderState Platform source) Value) :
    View n (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source) Value :=
  ⟨forget view.result,view.produced,view.raw,view.slots⟩

def Hidden (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (view : View n (Extra n KemSK ProviderState Platform source) Value) : Prop :=
  ∀ finished ∈ view.result,RegistrationNativeInstallOrdinals.Hidden finished.2.2.2.events finished.2.1.2.transcript
    view.slots (Selected setup seed scalar candidate)

variable (route : RawCtxServerRouting.SenderDecoder)
local notation "job" => program setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary
local notation "plain" => RegistrationNativePlatformSelectiveEntropyStartup.program setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous (RegistrationNativeHiddenInterpreter.initial providerState,known) bounds mode adversary
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)

/-- The real record view retains same-result hidden-slot receipts derived from the actual startup and corrected source callbacks. -/
theorem real_hidden (observed : View n (Extra n KemSK ProviderState Platform source) Value)
    (supported : observed ∈ support (RegistrationNativeRecordViewCrypto.real setup codec route job)) :
    Hidden setup seed scalar candidate observed := by
  rw [RegistrationNativeRecordViewCrypto.real_source,support_map] at supported
  obtain ⟨result,reached,rfl⟩ := supported
  have invariant := RegistrationNativePlatformSelectiveRecordTraceHidden.initialized setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary _ _ route _ result reached
  intro finished present
  cases outcome : result.1.1.1 with
  | none => simp [RegistrationNativeRecordPackage.nativeView,outcome] at present
  | some born =>
    have same : born = finished := by simpa only [RegistrationNativeRecordPackage.nativeView,outcome,Option.mem_some_iff] using present
    subst finished
    simpa only [RegistrationNativePlatformSelectiveRecordTraceHidden.Holds,outcome,RegistrationNativeRecordPackage.nativeView] using invariant

/-- The same structural receipts hold under every actual ideal record interpretation, retaining its own physical slots. -/
theorem ctx_hidden (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (observed : View n (Extra n KemSK ProviderState Platform source) Value)
    (supported : observed ∈ support (RegistrationNativeRecordPackage.ctx modes setup codec route job)) :
    Hidden setup seed scalar candidate observed := by
  rw [RegistrationNativeRecordPackage.ctx_source,support_map] at supported
  obtain ⟨result,reached,rfl⟩ := supported
  have invariant := RegistrationNativePlatformSelectiveRecordTraceHidden.initialized setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary _ _ route _ result reached
  intro finished present
  cases outcome : result.1.1.1 with
  | none => simp [RegistrationNativeRecordPackage.nativeView,outcome] at present
  | some born =>
    have same : born = finished := by simpa only [RegistrationNativeRecordPackage.nativeView,outcome,Option.mem_some_iff] using present
    subst finished
    simpa only [RegistrationNativePlatformSelectiveRecordTraceHidden.Holds,outcome,RegistrationNativeRecordPackage.nativeView] using invariant

/-- Erasing chronology alone preserves every original real ledger, platform, produced and raw field. -/
theorem real_erase :
    erase <$> RegistrationNativeRecordViewCrypto.real setup codec route (job : OracleComp _ (RegistrationNativePlatformSelectiveRecordTraceStartup.Outcome n KemSK ProviderState Platform Value source)) =
      RegistrationNativeRecordViewCrypto.real setup codec route plain := by
  rw [← RegistrationNativePlatformSelectiveRecordTraceStartup.erase setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary]
  rw [RegistrationNativeRecordViewCrypto.real_source,RegistrationNativeRecordViewCrypto.real_source,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  simp only [Functor.map_map,erase,RegistrationNativeRecordPackage.nativeView]

/-- The ideal erasure keeps its literal private origin map and the complete original platform result. -/
theorem ctx_erase (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode) :
    erase <$> RegistrationNativeRecordPackage.ctx modes setup codec route job =
      RegistrationNativeRecordPackage.ctx modes setup codec route plain := by
  rw [← RegistrationNativePlatformSelectiveRecordTraceStartup.erase setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary]
  rw [RegistrationNativeRecordPackage.ctx_source,RegistrationNativeRecordPackage.ctx_source,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  simp only [Functor.map_map,erase,RegistrationNativeRecordPackage.nativeView]

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.real_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.real_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.ctx_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.ctx_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.real_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.real_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.ctx_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView.ctx_erase
