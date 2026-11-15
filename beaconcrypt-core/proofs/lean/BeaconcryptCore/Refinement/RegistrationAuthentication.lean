-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Refinement.SessionBinding
import BeaconcryptCore.Refinement.TranscriptAuth

/-!
The current Init controller owns the four complete decoded field buffers and the selected Server pin. Its hash and Ed25519 phases retain exact primitive inputs and failure behavior; it has no Beacon ML credential or fingerprint stage. Cryptographic correctness remains an interpreter obligation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationAuthentication

def ownedFields (packet : registration.InitPacket) : authentication.OwnedInitFields :=
  ⟨packet.identity_key, packet.pre_key, packet.one_time_key, packet.pq_key⟩

def initFields (packet : registration.InitPacket) : Pqxdh.TranscriptAuth.InitFields where
  identityKey := absBytes packet.identity_key
  preKey := absBytes packet.pre_key
  oneTimeKey := absBytes packet.one_time_key
  pqKey := absBytes packet.pq_key

def initPreimage (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Pqxdh.Bytes :=
  Pqxdh.TranscriptAuth.initTranscript (initFields packet)
    (UInt64.ofNat pin.binding.identity_key_id.val) (absBytes pin.binding.identity_public_key)
    (absBytes pin.public_key)

/-- Authentication hashes the complete retained request under both configured server pins. -/
theorem begin_init_exact (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    ∃ next : registration.InitHash,
      registration.begin_init_authentication pin packet = ok (.HashRequested next) ∧
      next.fields = ownedFields packet ∧ next.server_pin = pin ∧ absBytes next.input = initPreimage pin packet := by
  obtain ⟨input, inputRun, inputBytes⟩ := TranscriptAuthRefinement.build_init_transcript_abs
    ⟨packet.identity_key, packet.pre_key, packet.one_time_key, packet.pq_key⟩
    pin.binding.identity_key_id pin.binding.identity_public_key pin.public_key
  refine ⟨⟨ownedFields packet, pin, input⟩, ?_, rfl, rfl, ?_⟩
  · simp [registration.begin_init_authentication, registration.InitPacket.fields,
      authentication.OwnedInitFields.new, ownedFields,
      session.ServerAuthenticationPin.impl.binding, session.ServerAuthenticationPin.impl.public_key,
      inputRun]
  · simpa [initPreimage, initFields, TranscriptAuthRefinement.absInit,
      TranscriptAuthRefinement.absId] using inputBytes

theorem init_hash_request (before : registration.InitHash) :
    ∃ request, before.request = ok request ∧ hashBytes request = absBytes before.input :=
  ⟨_, rfl, rfl⟩

theorem init_hash_failure (before : registration.InitHash) :
    before.resume .None = ok .Rejected := rfl

/-- A present digest advances only to verification under the complete tagged classical identity. -/
def initHashOutcome (before : registration.InitHash) (digest : Std.Array Std.U8 64#usize) :
    registration.InitAuthentication → Prop
  | .Rejected => before.fields.identity_key.val[0]! ≠ pqxdh.SIGN_TYPE_ED25519
  | .Ed25519VerificationRequested next =>
      before.fields.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519 ∧
      next.state.fields = before.fields ∧ next.state.server_pin = before.server_pin ∧
      next.state.init_hash = digest ∧ next.stage = .PqKey ∧
      next.public_key.val = (List.range (32#usize).val).map
        (fun index => before.fields.identity_key.val[index + 1]!)
  | _ => False

theorem init_hash_resume_refines (before : registration.InitHash) (digest : Std.Array Std.U8 64#usize) :
    ∃ result, before.resume (.Some digest) = ok result ∧ initHashOutcome before digest result := by
  obtain ⟨publicKey, publicRun, publicBytes⟩ :=
    TranscriptAuthInputsRefinement.identity_public_key_exact before.fields
  by_cases tag : before.fields.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519
  all_goals simp_all [registration.InitHash.resume, initHashOutcome,
    authentication.OwnedInitFields.fields, UScalar.eq_equiv,
    index_usize_eq before.fields.identity_key 0#usize (by scalar_tac)]

def edSignedBytes (before : registration.InitEd25519Verification) : List Std.U8 :=
  match before.stage with
  | .PreKey => before.state.fields.pre_key.val
  | .OneTimeKey => before.state.fields.one_time_key.val
  | .PqKey => before.state.fields.pq_key.val

/-- Every Ed verification requests the selected attached field under the same retained identity key. -/
theorem init_ed_request_exact (before : registration.InitEd25519Verification) :
    ∃ request : registration.Ed25519VerificationRequest,
      before.request = ok request ∧ request.public_key = before.public_key ∧
      request.signed.val = edSignedBytes before ∧ 64 ≤ request.signed.val.length := by
  cases stage : before.stage
  all_goals simp [registration.InitEd25519Verification.request, authentication.OwnedInitFields.fields, edSignedBytes, stage,
    lift, Bind.bind, Aeneas.Std.bind, Array.to_slice, Array.length_eq, Std.UScalar.ofNatCore_val_eq]

end BeaconcryptCore.Refinement.RegistrationAuthentication


/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.begin_init_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.begin_init_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_request

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_failure

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_resume_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_resume_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_ed_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_ed_request_exact
