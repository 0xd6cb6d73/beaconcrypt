-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInbound
import BeaconcryptCore.PanicFreedom.RegistrationTrivial

/-! Unconditional normal returns for registration admission and authentication, including rejected malformed inputs. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.Registration

theorem InitPacket_from_slices_total (identity_key : Slice Std.U8) (pre_key : Slice Std.U8)
  (one_time_key : Slice Std.U8) (pq_key : Slice Std.U8)
  (mldsa_public_key : Slice Std.U8) (signature : Slice Std.U8) :
    ∃ result, registration.InitPacket.from_slices identity_key pre_key one_time_key pq_key mldsa_public_key signature = ok result :=
  (BeaconcryptCore.Refinement.RegistrationInputs.init_packet_exact identity_key pre_key one_time_key pq_key mldsa_public_key signature).imp (fun _ h => h.1)

theorem ResponsePacket_from_slices_total (identity_key : Slice Std.U8) (ephemeral_key : Slice Std.U8)
  (kem_cipher_text : Slice Std.U8) (key_id : Std.U64)
  (application : Slice Std.U8) (signature : Slice Std.U8) :
    ∃ result, registration.ResponsePacket.from_slices identity_key ephemeral_key kem_cipher_text key_id application signature = ok result :=
  (BeaconcryptCore.Refinement.RegistrationInputs.response_packet_exact identity_key ephemeral_key kem_cipher_text key_id application signature).imp (fun _ h => h.1)

theorem AuthenticatedInit_registration_id_total (self : registration.AuthenticatedInit) :
    ∃ result, registration.AuthenticatedInit.registration_id self = ok result :=
  BeaconcryptCore.PanicFreedom.registration_id_ok self.registration

theorem begin_init_authentication_total (server_pin : session.ServerAuthenticationPin)
  (packet : registration.InitPacket) :
    ∃ result, registration.begin_init_authentication server_pin packet = ok result :=
  (BeaconcryptCore.Refinement.RegistrationAuthentication.begin_init_exact server_pin packet).elim
    (fun _next facts => ⟨_, facts.1⟩)

theorem InitHash_resume_total (self : registration.InitHash)
  (hash : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.InitHash.resume self hash = ok result :=
  match hash with
  | .None => ⟨_, BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_failure self⟩
  | .Some digest =>
      (BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_success self digest).elim
        (fun _next facts => ⟨_, facts.1⟩)

theorem InitMldsaVerification_resume_total (self : registration.InitMldsaVerification) (verified : Bool) :
    ∃ result, registration.InitMldsaVerification.resume self verified = ok result :=
  (BeaconcryptCore.Refinement.RegistrationAuthentication.init_mldsa_exact self verified).imp
    (fun _ facts => facts.1)

theorem InitEd25519Verification_request_total (self : registration.InitEd25519Verification) :
    ∃ result, registration.InitEd25519Verification.request self = ok result :=
  (BeaconcryptCore.Refinement.RegistrationAuthentication.init_ed_request_exact self).imp
    (fun _ facts => facts.1)

theorem InitEd25519Verification_resume_total (self : registration.InitEd25519Verification)
  (opened : core.option.Option (Slice Std.U8)) :
    ∃ result, registration.InitEd25519Verification.resume self opened = ok result :=
  (BeaconcryptCore.Refinement.RegistrationInbound.init_ed_resume_refines self opened).imp
    (fun _ facts => facts.1)

theorem InitBeaconFingerprint_resume_total (self : registration.InitBeaconFingerprint)
  (fingerprint : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.InitBeaconFingerprint.resume self fingerprint = ok result :=
  match fingerprint with
  | .None => ⟨_, rfl⟩
  | .Some fingerprint =>
      (BeaconcryptCore.Refinement.RegistrationInbound.init_beacon_fingerprint_exact self fingerprint).elim
        (fun _accepted facts => ⟨_, facts.1⟩)

end BeaconcryptCore.PanicFreedom.Registration

/-- info: 'BeaconcryptCore.PanicFreedom.Registration.InitPacket_from_slices_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.InitPacket_from_slices_total
/-- info: 'BeaconcryptCore.PanicFreedom.Registration.ResponsePacket_from_slices_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.ResponsePacket_from_slices_total
/-- info: 'BeaconcryptCore.PanicFreedom.Registration.AuthenticatedInit_registration_id_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.AuthenticatedInit_registration_id_total
/-- info: 'BeaconcryptCore.PanicFreedom.Registration.begin_init_authentication_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.begin_init_authentication_total
/-- info: 'BeaconcryptCore.PanicFreedom.Registration.InitHash_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.InitHash_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.Registration.InitMldsaVerification_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.InitMldsaVerification_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.Registration.InitEd25519Verification_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.InitEd25519Verification_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.Registration.InitEd25519Verification_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.InitEd25519Verification_resume_total
/-- info: 'BeaconcryptCore.PanicFreedom.Registration.InitBeaconFingerprint_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Registration.InitBeaconFingerprint_resume_total
