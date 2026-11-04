-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
import BeaconcryptCore.Refinement.RegistrationSigningHistory
/-! Unsigned issuance in the actual source history selects an actual same-key signing request, including a missing signature reply. No key injectivity, successful publication or successful signing is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterSourceSigningHistory (receipt receipts history)

theorem receipt_member (log :List Stage) (selected :RegistrationSigningShared.Receipt)
    (present :selected∈receipts log) :
    ∃request payload digest signature,
      Stage.sign request payload digest signature∈log ∧
      selected=⟨⟨request.public_key,payload,RegistrationSigningTrace.replyBytes signature⟩,digest⟩ :=by
  obtain ⟨actual,member,same⟩:=List.mem_filterMap.mp present
  cases actual with
  | hash request digest | firstRecord initial reply | beaconFirstRecord initial reply=>cases same
  | sign request payload digest signature=>
    exact ⟨request,payload,digest,signature,member,(Option.some.inj same).symm⟩

theorem issued_sign (publicKey :Pqxdh.Bytes) (protectedKey :Bool) (log :List Stage)
    (candidate :MldsaTranscriptAuth.Payload) (signature :Pqxdh.Bytes)
    (issued :MldsaTranscriptAuth.Issued ⟨publicKey,protectedKey,history publicKey log,candidate,signature⟩) :
    ∃request digest reply, Stage.sign request candidate digest reply∈log ∧
      PqxdhRefinement.absBytes request.public_key=publicKey :=by
  obtain ⟨call,present,payload⟩:=issued
  obtain ⟨observation,observed,key,sameCall⟩:=
    (RegistrationSigningHistory.history_mem_iff publicKey ((receipts log).map RegistrationSigningShared.Receipt.observation) call).mp present
  obtain ⟨selected,recorded,sameObservation⟩:=List.mem_map.mp observed
  cases sameObservation
  obtain ⟨request,actual,digest,reply,member,same⟩:=receipt_member log selected recorded
  cases same
  have actualEq :actual=candidate:=(congrArg MldsaTranscriptAuth.SigningCall.payload sameCall).trans payload
  cases actualEq
  exact ⟨request,digest,reply,member,key⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin.receipt_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin.receipt_member

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin.issued_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin.issued_sign
