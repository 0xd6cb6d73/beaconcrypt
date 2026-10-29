-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage

/-! The actual traced selective kernel preserves its physical allocation invariant, Protocol safety, and every previously installed hidden handle. Its selected-message predicate reads the same full-byte material evaluator and complete candidate, with no plaintext-state replacement. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
open RegistrationNativeSelectiveInstallKernel (State typed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Valid (before : State n KemSK ProviderState Secret source) : Prop :=
  RegistrationNativeSelectiveAllocationJoint.Holds before.2 ∧ PqxdhRecordLiftProtocolHistory.Safe before.2.1.2

def events (before : State n KemSK ProviderState Secret source) : List RegistrationNativeG2Trace.Event := before.1.events

def slots (before : State n KemSK ProviderState Secret source) :
    PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n) :=
  PqxdhRecordLiftIdeal.handleSlot before.2.1.2

def Selected (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : RegistrationNativeRelatedFamily.Message) : Prop :=
  ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
    RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true

/-- The actual typed kernel preserves allocation, safety and forward physical hidden-slot storage for the same callback result. -/
theorem typed_storage (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK ProviderState Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Secret source)
    (prior : Valid before) (supported : result ∈ support
      ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before)) :
    RegistrationNativeInstallLedger.Storage slots Valid before result.2 := by
  have allocation := RegistrationNativeSelectiveInstallKernel.typed_holds setup checks wire sign seed scalar candidate provider service codec route
    selectedOwner selectedAccept query before result prior.1 supported
  have stored := RegistrationNativeSelectiveInstallKernel.typed_storage setup checks wire sign seed scalar candidate provider service codec route
    selectedOwner selectedAccept query before result prior.2 supported
  refine ⟨⟨allocation, stored.1⟩, ?_⟩
  intro handle present
  obtain ⟨slot, installed⟩ := Option.isSome_iff_exists.mp present
  exact Option.isSome_iff_exists.mpr ⟨slot, stored.2 handle slot installed⟩

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage.typed_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage.typed_storage
