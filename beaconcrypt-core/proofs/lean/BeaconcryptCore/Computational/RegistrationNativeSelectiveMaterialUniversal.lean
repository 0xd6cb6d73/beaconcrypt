-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted
import BeaconcryptCore.Computational.RegistrationNativeSelectiveDemandRealized

/-! Successful original material controllers discharge input realization themselves. Universal selection on every realized input is sufficient; invalid-input vacuity cannot create an installed handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialUniversal
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (Control)
open RegistrationNativeSelectiveMaterialService (Local handler)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Encoded Reader Response Secret : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response)
  (message : RegistrationNativeRelatedFamily.Message)
  (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
    RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)

private theorem demand_realized (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : Control n) (secret : Secret)
    (middle : (((Option (RegistrationNativePairedChoice.Choice n) × Local n Auxiliary KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : middle ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((handler setup wire sign seed scalar candidate provider (.inl message)).run before) shell world secret))
    (choice : RegistrationNativePairedChoice.Choice n) (chosen : middle.1.1.1.1 = some choice) :
    ∃ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes := by
  have original := RegistrationNativeRecordHandleSlots.open_support service codec route _ shell world secret middle supported
  simp only [handler, RegistrationNativeSelectiveMaterialService.onKeys, StateT.run, support_map] at original
  obtain ⟨result, called, returned⟩ := original
  have reply : result.1 = some choice := (congrArg Prod.fst returned).trans chosen
  rcases result with ⟨value, after⟩
  dsimp only at reply
  subst value
  exact RegistrationNativeSelectiveDemandRealized.source setup wire sign seed scalar candidate provider message before.2 after choice called

include selected in
/-- Successful actual Server publication supplies its own input realization before selecting the installed hidden origin. -/
theorem server (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (peer : peer.PublishedPeer Encoded)
    (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell) (world : Control n) (secret : Secret)
    (result : (((RustM (RegistrationHiddenInstall.Result Encoded) × Local n Auxiliary KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (handler setup wire sign seed scalar candidate provider)
        (RegistrationNativePairedServerService.publicAdmitted encode control initial message)).run before) shell world secret))
    (successful : result.1.1.1.1 = .ok (.Ok peer)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer peer.key_id) = some slot := by
  have original := supported
  simp only [RegistrationNativePairedServerService.publicAdmitted, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, demanded, continued⟩ := supported
  cases chosen : middle.1.1.1.1 with
  | none =>
      simp only [chosen, simulateQ_pure, StateT.run_pure, CborRawRecordOriginFlatten.interpret_pure,
        mem_support_pure_iff] at continued
      subst result
      cases successful
  | some choice =>
      obtain ⟨bytes, realized⟩ := demand_realized setup wire route sign seed scalar candidate provider service codec message
        before shell world secret middle demanded choice chosen
      exact RegistrationNativeSelectiveMaterialAdmitted.server setup wire route sign seed scalar candidate provider service codec
        message bytes realized (selected bytes realized) encode control initial peer before shell world secret result original successful

include selected in
/-- Successful actual Beacon publication supplies its own input realization before selecting the installed hidden origin. -/
theorem beacon (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (completed : RegistrationBeaconSeed.PublicCompleted)
    (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell) (world : Control n) (secret : Secret)
    (result : (((RustM RegistrationNativePairedBeaconService.Result × Local n Auxiliary KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (handler setup wire sign seed scalar candidate provider)
        (RegistrationNativePairedBeaconService.admitted setup.source owner sender descriptor message)).run before) shell world secret))
    (successful : result.1.1.1.1 = .ok (.Ok completed)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some slot := by
  have original := supported
  simp only [RegistrationNativePairedBeaconService.admitted, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, demanded, continued⟩ := supported
  cases chosen : middle.1.1.1.1 with
  | none =>
      simp only [chosen, simulateQ_pure, StateT.run_pure, CborRawRecordOriginFlatten.interpret_pure,
        mem_support_pure_iff] at continued
      subst result
      cases successful
  | some choice =>
      obtain ⟨bytes, realized⟩ := demand_realized setup wire route sign seed scalar candidate provider service codec message
        before shell world secret middle demanded choice chosen
      exact RegistrationNativeSelectiveMaterialAdmitted.beacon setup wire route sign seed scalar candidate provider service codec
        message bytes realized (selected bytes realized) owner sender descriptor completed before shell world secret result original successful

end BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialUniversal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialUniversal.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialUniversal.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialUniversal.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialUniversal.beacon
