-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconServiceSource
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution

/-! The original native Beacon paired callback installs the selected hidden origin in the same physical owner slot. Its signing frame is the actual private receipt frame, and no current environment is reset. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconOrigin
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSelectiveMaterialService (Local)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Reader Response Secret : Type} {base : OracleSpec ι}

/-- The literal successful paired Beacon callback installs its selected origin at the physical owner address. -/
theorem admitted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response)
    (owner : Nat) (sender : U64) (ready : RegistrationBeaconReferenceRoot.Ready)
    (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : (((RustM RegistrationNativePairedBeaconService.Result × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (RegistrationNativeSelectiveBeaconServiceSource.actual setup wire sign seed scalar candidate provider)
        (RegistrationNativePairedBeaconService.admitted setup.source owner sender ready.descriptor ready.reference)).run
          (RegistrationNativeSelectiveBeaconServiceSource.restore before)) shell world secret))
    (completed : RegistrationBeaconSeed.PublicCompleted) (successful : result.1.1.1.1 = .ok (.Ok completed))
    (realizedBytes : Pqxdh.Bytes)
    (realized : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some slot := by
  rw [RegistrationNativeSelectiveBeaconServiceSource.program_source,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at supported
  obtain ⟨native, called, returned⟩ := supported
  cases returned
  exact RegistrationNativeSelectiveMaterialAdmitted.beacon setup wire route sign seed scalar candidate provider service codec
    ready.reference realizedBytes realized selected owner sender ready.descriptor completed before shell world secret native called successful

end BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconOrigin.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconOrigin.admitted
