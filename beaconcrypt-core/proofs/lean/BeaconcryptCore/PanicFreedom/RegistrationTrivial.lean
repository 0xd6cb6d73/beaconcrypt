-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs

/-! Definitionally normal registration constructors, immutable views and field transfers, on arbitrary represented states. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.RegistrationTrivial

theorem AuthenticatedInit_into_parts_total (self : registration.AuthenticatedInit) :
    ∃ result, registration.AuthenticatedInit.into_parts self = ok result := ⟨_, rfl⟩

theorem AuthenticatedResponse_into_parts_total (self : registration.AuthenticatedResponse) :
    ∃ result, registration.AuthenticatedResponse.into_parts self = ok result := ⟨_, rfl⟩

theorem InitPacket_fields_total (self : registration.InitPacket) :
    ∃ result, registration.InitPacket.fields self = ok result := ⟨_, rfl⟩

theorem begin_server_pin_total (binding : pqxdh.ServerBinding) (public_key : Array Std.U8 1952#usize) :
    ∃ result, registration.begin_server_pin binding public_key = ok result := ⟨_, rfl⟩

theorem PinFingerprint_request_total (self : registration.PinFingerprint) :
    ∃ result, registration.PinFingerprint.request self = ok result := ⟨_, rfl⟩

theorem InitHash_request_total (self : registration.InitHash) :
    ∃ result, registration.InitHash.request self = ok result := ⟨_, rfl⟩

theorem InitMldsaVerification_request_total (self : registration.InitMldsaVerification) :
    ∃ result, registration.InitMldsaVerification.request self = ok result := ⟨_, rfl⟩

theorem InitServerFingerprint_request_total (self : registration.InitServerFingerprint) :
    ∃ result, registration.InitServerFingerprint.request self = ok result := ⟨_, rfl⟩

theorem InitBeaconFingerprint_request_total (self : registration.InitBeaconFingerprint) :
    ∃ result, registration.InitBeaconFingerprint.request self = ok result := ⟨_, rfl⟩

theorem BeaconPending_server_key_id_total (self : registration.BeaconPending) :
    ∃ result, registration.BeaconPending.server_key_id self = ok result := ⟨_, rfl⟩

theorem BeaconPending_aborted_state_total (self : registration.BeaconPending) :
    ∃ result, registration.BeaconPending.aborted_state self = ok result := ⟨_, rfl⟩

theorem BeaconPending_abort_total (self : registration.BeaconPending) :
    ∃ result, registration.BeaconPending.abort self = ok result := ⟨_, rfl⟩

theorem ResponseHash_request_total (self : registration.ResponseHash) :
    ∃ result, registration.ResponseHash.request self = ok result := ⟨_, rfl⟩

theorem ResponseMldsaVerification_request_total (self : registration.ResponseMldsaVerification) :
    ∃ result, registration.ResponseMldsaVerification.request self = ok result := ⟨_, rfl⟩

theorem BeaconInitState_fields_total (self : registration.BeaconInitState) :
    ∃ result, registration.BeaconInitState.fields self = ok result := ⟨_, rfl⟩

theorem BeaconFingerprint_request_total (self : registration.BeaconFingerprint) :
    ∃ result, registration.BeaconFingerprint.request self = ok result := ⟨_, rfl⟩

theorem BeaconInitHash_request_total (self : registration.BeaconInitHash) :
    ∃ result, registration.BeaconInitHash.request self = ok result := ⟨_, rfl⟩

theorem BeaconMldsaSigning_request_total (self : registration.BeaconMldsaSigning) :
    ∃ result, registration.BeaconMldsaSigning.request self = ok result := ⟨_, rfl⟩

theorem BeaconInitReady_message_total (self : registration.BeaconInitReady) :
    ∃ result, registration.BeaconInitReady.message self = ok result := ⟨_, rfl⟩

theorem PublishedBeaconInit_into_parts_total {Encoded : Type} (self : registration.PublishedBeaconInit Encoded) :
    ∃ result, registration.PublishedBeaconInit.into_parts (Encoded := Encoded) self = ok result := ⟨_, rfl⟩

theorem BeaconInitialKdf_request_total (self : registration.BeaconInitialKdf) :
    ∃ result, registration.BeaconInitialKdf.request self = ok result := ⟨_, rfl⟩

theorem CompletedBeacon_into_parts_total (self : registration.CompletedBeacon) :
    ∃ result, registration.CompletedBeacon.into_parts self = ok result := ⟨_, rfl⟩

theorem ServerInitialKdf_request_total (self : registration.ServerInitialKdf) :
    ∃ result, registration.ServerInitialKdf.request self = ok result := ⟨_, rfl⟩

theorem ServerInitialSeal_request_total (self : registration.ServerInitialSeal) :
    ∃ result, registration.ServerInitialSeal.request self = ok result := ⟨_, rfl⟩

theorem ServerResponseHash_request_total (self : registration.ServerResponseHash) :
    ∃ result, registration.ServerResponseHash.request self = ok result := ⟨_, rfl⟩

theorem ServerResponseSigning_request_total (self : registration.ServerResponseSigning) :
    ∃ result, registration.ServerResponseSigning.request self = ok result := ⟨_, rfl⟩

theorem ServerResponseReady_message_total (self : registration.ServerResponseReady) :
    ∃ result, registration.ServerResponseReady.message self = ok result := ⟨_, rfl⟩

theorem PublishedServerResponse_into_parts_total {Encoded : Type} (self : registration.PublishedServerResponse Encoded) :
    ∃ result, registration.PublishedServerResponse.into_parts (Encoded := Encoded) self = ok result := ⟨_, rfl⟩

theorem PinFingerprint_resume_total (self : registration.PinFingerprint)
  (fingerprint : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.PinFingerprint.resume self fingerprint = ok result := by
  cases fingerprint
  all_goals exact ⟨_, rfl⟩

theorem InitServerFingerprint_resume_total (self : registration.InitServerFingerprint)
  (fingerprint : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.InitServerFingerprint.resume self fingerprint = ok result := by
  cases fingerprint
  all_goals exact ⟨_, rfl⟩

theorem ResponseMldsaVerification_resume_total (self : registration.ResponseMldsaVerification) (verified : Bool) :
    ∃ result, registration.ResponseMldsaVerification.resume self verified = ok result := by
  cases verified
  all_goals exact ⟨_, rfl⟩

theorem BeaconInitReady_publish_total {Encoded : Type} (self : registration.BeaconInitReady)
  (encoded : core.option.Option Encoded) :
    ∃ result, registration.BeaconInitReady.publish (Encoded := Encoded) self encoded = ok result := by
  cases encoded
  all_goals exact ⟨_, rfl⟩

theorem ServerResponseReady_publish_total {Encoded : Type} (self : registration.ServerResponseReady)
  (encoded : core.option.Option Encoded) :
    ∃ result, registration.ServerResponseReady.publish (Encoded := Encoded) self encoded = ok result := by
  cases encoded
  all_goals exact ⟨_, rfl⟩

end BeaconcryptCore.PanicFreedom.RegistrationTrivial

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.AuthenticatedInit_into_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.AuthenticatedInit_into_parts_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.AuthenticatedResponse_into_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.AuthenticatedResponse_into_parts_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitPacket_fields_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitPacket_fields_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.begin_server_pin_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.begin_server_pin_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.PinFingerprint_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.PinFingerprint_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitHash_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitHash_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitMldsaVerification_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitMldsaVerification_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitServerFingerprint_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitServerFingerprint_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitBeaconFingerprint_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitBeaconFingerprint_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconPending_server_key_id_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconPending_server_key_id_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconPending_aborted_state_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconPending_aborted_state_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconPending_abort_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconPending_abort_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ResponseHash_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ResponseHash_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ResponseMldsaVerification_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ResponseMldsaVerification_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitState_fields_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitState_fields_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconFingerprint_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconFingerprint_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitHash_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitHash_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconMldsaSigning_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconMldsaSigning_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_message_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_message_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.PublishedBeaconInit_into_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.PublishedBeaconInit_into_parts_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitialKdf_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitialKdf_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.CompletedBeacon_into_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.CompletedBeacon_into_parts_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialKdf_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialKdf_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialSeal_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialSeal_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseHash_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseHash_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseSigning_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseSigning_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseReady_message_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseReady_message_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.PublishedServerResponse_into_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.PublishedServerResponse_into_parts_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.PinFingerprint_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.PinFingerprint_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitServerFingerprint_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.InitServerFingerprint_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ResponseMldsaVerification_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ResponseMldsaVerification_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_publish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_publish_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseReady_publish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerResponseReady_publish_total
