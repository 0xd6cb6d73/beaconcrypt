-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage

/-! The actual traced selective kernel preserves its physical allocation invariant, Protocol safety, and every previously installed hidden handle. Its selected-message predicate reads the same full-byte material evaluator and complete candidate, with no plaintext-state replacement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
open RegistrationNativePlatformSelectiveInstallKernel (State typed)
variable {n : Nat} {ι KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Valid (before : State n KemSK ProviderState Platform Secret source) : Prop :=
  RegistrationNativePlatformHiddenAllocationCore.Holds before.2 ∧ PqxdhRecordLiftProtocolHistory.Safe before.2.1.2

def events (before : State n KemSK ProviderState Platform Secret source) : List RegistrationNativeG2Trace.Event := before.1.events

def slots (before : State n KemSK ProviderState Platform Secret source) :
    PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n) :=
  PqxdhRecordLiftIdeal.handleSlot before.2.1.2

def Selected (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : RegistrationNativeRelatedFamily.Message) : Prop :=
  ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
    RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true

/-- The actual typed kernel preserves allocation, safety and forward physical hidden-slot storage for the same callback result. -/
theorem typed_storage [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (prior : Valid before) (supported : result ∈ support
      ((typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before)) :
    RegistrationNativeInstallLedger.Storage slots Valid before result.2 := by
  have ownerAllocation := RegistrationNativePlatformSelectiveInstallKernel.typed_holds setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query before result prior.1 supported
  have stored := RegistrationNativePlatformSelectiveInstallKernel.typed_storage setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query before result prior.2 supported
  refine ⟨⟨ownerAllocation, stored.1⟩, ?_⟩
  intro handle present
  obtain ⟨slot, installed⟩ := Option.isSome_iff_exists.mp present
  exact Option.isSome_iff_exists.mpr ⟨slot, stored.2 handle slot installed⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage.typed_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage.typed_storage
