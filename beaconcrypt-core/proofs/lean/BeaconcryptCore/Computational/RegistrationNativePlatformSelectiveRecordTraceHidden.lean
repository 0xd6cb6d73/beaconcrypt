-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceInvariant
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceHidden
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

open RegistrationNativePlatformSelectiveRecordTraceStartup (Outcome Extra program after)
open RegistrationNativePlatformInstallKernelStorage (Selected)

abbrev Result (n : Nat) (KemSK ProviderState Platform Secret Value : Type) (source : RegistrationNativeMldsa.Source) :=
  ((Outcome n KemSK ProviderState Platform Value source × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret

def Holds (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (result : Result n KemSK ProviderState Platform Secret Value source) : Prop :=
  match result.1.1.1 with
  | none => True
  | some finished => RegistrationNativeInstallOrdinals.Hidden finished.2.2.2.events finished.2.1.2.transcript
      (PqxdhRecordLiftIdeal.handleSlot result.1.2) (Selected setup seed scalar candidate)

/-- The complete actual startup and corrected callback program derive same-trace selected hidden slots in their same reached physical state. -/
theorem initialized
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (secret : Secret)
    (result : Result n KemSK ProviderState Platform Secret Value source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (program setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret)) :
    Holds setup seed scalar candidate result := by
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
    have valid := RegistrationNativePlatformInstallKernelInitial.initialized setup ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
      providerState service codec route secret born previous known shell control reached startupSupport
    have invariant := RegistrationNativePlatformInstallKernelTraceInvariant.run setup checks wire born.native.credential
      seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route
      serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
      (RegistrationNativePlatformInstallKernelInitial.initial born providerState previous known shell control reached) valid
      (RegistrationNativePlatformInstallKernelInitial.empty born providerState previous known shell control reached) observed observedSupport
    exact invariant.2.2

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceHidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceHidden.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceHidden.initialized
