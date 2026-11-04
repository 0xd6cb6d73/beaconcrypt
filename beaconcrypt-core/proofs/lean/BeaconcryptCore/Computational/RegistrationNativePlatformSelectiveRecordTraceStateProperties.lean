-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceState
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties
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

variable (previous : Platform)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

open RegistrationNativeRecordPackage (View)
open RegistrationNativePlatformSelectiveRecordTraceStartup (Extra forget)
open RegistrationNativePlatformSelectiveRecordTraceState (program after)
open RegistrationNativePlatformInstallKernelStorage (Selected)

variable (route : RawCtxServerRouting.SenderDecoder)
local notation "job" => program setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous privateBefore ensureInit identityIndex serverKeyId bounds mode adversary
local notation "plain" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)



/-- The initialized physical allocation and Protocol invariants do not inspect the selective material cache. -/
theorem initialized
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (lowerCodec : Codec Reader Response) (initialSecret : Secret)
    (result : RegistrationNativePlatformSelectiveRecordTraceHidden.Result n KemSK ProviderState Platform Secret Value source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service lowerCodec route job
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret)) :
    RegistrationNativePlatformSelectiveRecordTraceHidden.Holds setup seed scalar candidate result := by
  unfold program at supported
  rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
  obtain ⟨initialized,startupSupport,continued⟩ := supported
  rcases initialized with ⟨⟨⟨initialized,shell⟩,control⟩,reached⟩
  cases initialized with
  | none =>
    rw [CborRawRecordOriginFlatten.interpret_pure,mem_support_pure_iff] at continued
    subst result
    trivial
  | some born =>
    simp only [after,RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at continued
    obtain ⟨observed,observedSupport,rfl⟩ := continued
    let before : RegistrationNativePlatformSelectiveInstallKernel.State n KemSK ProviderState Platform Secret source :=
      (RegistrationNativeG2Trace.initial,(((((born.native.frontend,previous),privateBefore),shell),control),reached))
    have original := RegistrationNativePlatformInstallKernelInitial.initialized setup ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
      privateBefore.1.provider service lowerCodec route initialSecret born previous privateBefore.2 shell control reached startupSupport
    have valid : RegistrationNativePlatformInstallKernelStorage.Valid before :=
      ⟨⟨original.1.length,original.1.indexed,original.1.cursor⟩,original.2⟩
    have invariant := RegistrationNativePlatformInstallKernelTraceInvariant.run setup checks wire born.native.credential
      seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service lowerCodec route
      serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
      before valid rfl observed observedSupport
    exact invariant.2.2

/-- The same physical hidden handles are attached to the supported view with its own completed material cache. -/
theorem hidden
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (lowerCodec : Codec Reader Response) (initialSecret : Secret)
    (result : RegistrationNativePlatformSelectiveRecordTraceHidden.Result n KemSK ProviderState Platform Secret Value source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service lowerCodec route job
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret))
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) :
    RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup seed scalar candidate
      (RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) produced) := by
  have invariant := initialized setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous privateBefore ensureInit identityIndex serverKeyId bounds mode adversary route service lowerCodec initialSecret result supported
  intro finished present
  cases outcome : result.1.1.1 with
  | none => simp [RegistrationNativeRecordPackage.nativeView,outcome] at present
  | some born =>
    have same : born = finished := by simpa only [RegistrationNativeRecordPackage.nativeView,outcome,Option.mem_some_iff] using present
    subst finished
    simpa only [RegistrationNativePlatformSelectiveRecordTraceHidden.Holds,outcome,RegistrationNativeRecordPackage.nativeView] using invariant

/-- Erasing chronology retains the same completed material table and reached private record state. -/
theorem interpret_erase (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (lowerCodec : Codec Reader Response) (initialSecret : Secret) :
    (fun result => (((forget result.1.1.1,result.1.1.2),result.1.2),result.2)) <$>
      CborRawRecordOriginFlatten.interpret service lowerCodec route job
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret =
    CborRawRecordOriginFlatten.interpret service lowerCodec route plain
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret := by
  have traceLaw := congrArg (fun work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n)
    (RegistrationNativeEntropyRun.Outcome (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source) Value) => CborRawRecordOriginFlatten.interpret service lowerCodec route work
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret)
    (RegistrationNativePlatformSelectiveRecordTraceState.erase (n := n) (source := source) setup checks wire seed scalar candidate provider selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous privateBefore ensureInit identityIndex serverKeyId bounds mode adversary)
  rw [RegistrationNativeHiddenEnvironmentWorld.interpret_map] at traceLaw
  exact traceLaw.trans (RegistrationNativePlatformSelectiveEntropyStartup.program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous
    privateBefore bounds mode adversary service lowerCodec route initialSecret)

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties.hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties.interpret_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties.interpret_erase
