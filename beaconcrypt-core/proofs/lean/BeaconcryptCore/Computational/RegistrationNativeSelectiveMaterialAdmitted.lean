-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialService

/-! The same actual admitted material demand selects the hidden reference used by the subsequent native current-environment stage. Successful completion therefore supplies an actual hidden record handle, with no separate installation or game-equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftProtocol (Control)
open RegistrationNativeSelectiveMaterialService (Local handler)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Encoded Reader Response Secret : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : PqxdhServerAuthExperiment.Codec Reader Response)
  (message : RegistrationNativeRelatedFamily.Message) (bytes : Pqxdh.Bytes)
  (realized : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes)
  (selected : RegistrationNativeSelectiveHiddenService.selected
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)

include realized selected in
private theorem demand_hidden (before : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (secret : Secret)
    (middle : (((Option (RegistrationNativePairedChoice.Choice n) × Local n Auxiliary KemSK ProviderState) ×
      CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : middle ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((handler setup wire sign seed scalar candidate provider (.inl message)).run before) shell control secret))
    (choice : RegistrationNativePairedChoice.Choice n) (chosen : middle.1.1.1.1 = some choice) :
    ∃ reference, choice = .hidden reference := by
  have original := RegistrationNativeRecordHandleSlots.open_support service codec route _ shell control secret middle supported
  simp only [handler, RegistrationNativeSelectiveMaterialService.onKeys, StateT.run, support_map] at original
  obtain ⟨result, called, returned⟩ := original
  have reply : result.1 = some choice := (congrArg Prod.fst returned).trans chosen
  rcases result with ⟨value, after⟩
  dsimp only at reply
  subst value
  obtain ⟨reference, hidden, _slot, _material⟩ := RegistrationNativeSelectiveHiddenDemandWorld.source_demand setup wire sign seed scalar
    candidate provider message bytes before.2 after choice realized selected called
  exact ⟨reference, hidden⟩

include realized selected in
/-- The literal current-environment Server admitted controller installs a hidden origin for its own selected successful demand. -/
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
      obtain ⟨reference, hidden⟩ := demand_hidden setup wire route sign seed scalar candidate provider service codec message bytes realized selected
        before shell world secret middle demanded choice chosen
      subst choice
      simp only [chosen] at continued
      rw [RegistrationNativeSelectiveMaterialService.common_program,
        RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at continued
      obtain ⟨installed, called, returned⟩ := continued
      cases returned
      exact ⟨reference.slot, RegistrationNativeRecordHiddenStage.server service codec route setup.source wire.frameWrite sign
        encode control initial reference peer middle.1.1.1.2.1 middle.1.1.2 middle.1.2 middle.2 installed called successful⟩

include realized selected in
/-- The literal current-environment Beacon admitted controller installs a hidden origin for its own selected successful demand. -/
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
      obtain ⟨reference, hidden⟩ := demand_hidden setup wire route sign seed scalar candidate provider service codec message bytes realized selected
        before shell world secret middle demanded choice chosen
      subst choice
      simp only [chosen] at continued
      rw [RegistrationNativeSelectiveMaterialService.common_program,
        RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at continued
      obtain ⟨installed, called, returned⟩ := continued
      cases returned
      exact ⟨reference.slot, RegistrationNativeRecordHiddenStage.beacon service codec route setup.source wire.frameWrite sign
        owner sender descriptor reference completed middle.1.1.1.2.1 middle.1.1.2 middle.1.2 middle.2 installed called successful⟩

end BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialAdmitted.beacon
