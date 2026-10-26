-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Refinement.SessionBinding

/-!
The extracted authentication phases retain one decoded packet and its selected server pin. Behavioral laws describe their exact primitive requests, rejection gates and accepted fields. Cryptographic correctness remains a property of the chosen interpreter.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationAuthentication

def initFields (packet : registration.InitPacket) : Pqxdh.TranscriptAuth.InitFields where
  identityKey := absBytes packet.identity_key
  preKey := absBytes packet.pre_key
  oneTimeKey := absBytes packet.one_time_key
  pqKey := absBytes packet.pq_key
  mldsaPublicKey := absBytes packet.mldsa_public_key

def initPreimage (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Pqxdh.Bytes :=
  Pqxdh.TranscriptAuth.initTranscript (initFields packet)
    (UInt64.ofNat pin.binding.identity_key_id.val) (absBytes pin.binding.identity_public_key)
    (absBytes pin.public_key)

private theorem identity_tail_byte (identity : Std.Array Std.U8 33#usize) (index : Std.Usize)
    (inside : index.val < 32) :
    registration.InitMldsaVerification.resume.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      identity index = ok (identity.val[index.val + 1]!, identity) := by
  obtain ⟨next, nextRun, nextValue⟩ := usize_add_val index 1#usize
    (lt_numBits _ (by simp; omega))
  simp [registration.InitMldsaVerification.resume.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    nextRun, index_usize_eq identity next (by simp at nextValue ⊢; omega), nextValue]

/-- The Ed25519 verification key is the complete 32-byte suffix after the identity tag. -/
theorem identity_tail_exact (identity : Std.Array Std.U8 33#usize) :
    ∃ publicKey : Std.Array Std.U8 32#usize, core.array.from_fn 32#usize
        registration.InitMldsaVerification.resume.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        identity = ok publicKey ∧
      publicKey.val = (List.range (32#usize).val).map (fun index => identity.val[index + 1]!) := by
  apply from_fn_pure 32#usize
    registration.InitMldsaVerification.resume.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    identity (fun index => identity.val[index + 1]!)
  intro index inside
  have indexValue := usize_mk_val index (by scalar_tac)
  simpa only [indexValue] using identity_tail_byte identity ⟨BitVec.ofNat _ index⟩
    (by simpa only [indexValue, usize_val_32] using inside)

def initMldsaOutcome (before : registration.InitMldsaVerification) (verified : Bool) :
    registration.InitAuthentication → Prop
  | .Rejected => verified = false ∨ before.state.packet.identity_key.val[0]! ≠ pqxdh.SIGN_TYPE_ED25519
  | .Ed25519VerificationRequested next =>
      verified = true ∧ before.state.packet.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519 ∧
        next.state = before.state ∧ next.stage = .PqKey ∧
        next.public_key.val = (List.range (32#usize).val).map
          (fun index => before.state.packet.identity_key.val[index + 1]!)
  | _ => False

/-- Ed25519 admission starts at PQ only after ML success and the exact Ed25519 identity tag. -/
theorem init_mldsa_exact (before : registration.InitMldsaVerification) (verified : Bool) :
    ∃ result, before.resume verified = ok result ∧ initMldsaOutcome before verified result := by
  obtain ⟨publicKey, publicRun, publicBytes⟩ := identity_tail_exact before.state.packet.identity_key
  cases verified
  · simp [registration.InitMldsaVerification.resume, initMldsaOutcome]
  · by_cases tag : before.state.packet.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519
    all_goals simp_all [registration.InitMldsaVerification.resume, initMldsaOutcome, UScalar.eq_equiv,
      index_usize_eq before.state.packet.identity_key 0#usize (by scalar_tac)]

/-- Authentication hashes the complete retained unsigned request under both configured server pins. -/
theorem begin_init_exact (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    ∃ next : registration.InitHash,
      registration.begin_init_authentication pin packet = ok (.HashRequested next) ∧
      next.packet = packet ∧ next.server_pin = pin ∧ absBytes next.input = initPreimage pin packet := by
  obtain ⟨input, inputRun, inputBytes⟩ := TranscriptAuthRefinement.build_init_transcript_abs
    ⟨packet.identity_key, packet.pre_key, packet.one_time_key, packet.pq_key, packet.mldsa_public_key⟩
    pin.binding.identity_key_id pin.binding.identity_public_key pin.public_key
  refine ⟨⟨packet, pin, input⟩, ?_, rfl, rfl, ?_⟩
  · simp [registration.begin_init_authentication, registration.InitPacket.fields,
      session.ServerAuthenticationPin.impl.binding, session.ServerAuthenticationPin.impl.public_key,
      inputRun]
  · simpa [initPreimage, initFields, TranscriptAuthRefinement.absInit,
      TranscriptAuthRefinement.absId] using inputBytes

theorem init_hash_request (before : registration.InitHash) :
    ∃ request, before.request = ok request ∧ hashBytes request = absBytes before.input :=
  ⟨_, rfl, rfl⟩

theorem init_hash_failure (before : registration.InitHash) :
    before.resume .None = ok .Rejected := rfl

theorem init_mldsa_request (before : registration.InitMldsaVerification) :
    before.request = ok {
      public_key := before.state.packet.mldsa_public_key,
      input := before.input,
      context := authentication.SIGNING_CONTEXT,
      signature := before.state.packet.signature
    } := rfl

/-- A successful request hash feeds the exact Beacon-role ML message and the same packet/pins forward. -/
theorem init_hash_success (before : registration.InitHash) (digest : Std.Array Std.U8 64#usize) :
    ∃ next : registration.InitMldsaVerification,
      before.resume (.Some digest) = ok (.MldsaVerificationRequested next) ∧
      next.state.packet = before.packet ∧ next.state.server_pin = before.server_pin ∧
      next.state.init_hash = digest ∧
      absBytes next.input = Pqxdh.TranscriptAuth.signatureInput .beacon (absBytes digest) := by
  obtain ⟨input, inputRun, inputBytes⟩ :=
    TranscriptAuthInputsRefinement.build_signature_input_abs .Beacon digest
  refine ⟨⟨⟨before.packet, before.server_pin, digest⟩, input⟩, ?_, rfl, rfl, rfl, ?_⟩
  · simp [registration.InitHash.resume, inputRun]
  · exact inputBytes

def edSignedBytes (before : registration.InitEd25519Verification) : List Std.U8 :=
  match before.stage with
  | .PreKey => before.state.packet.pre_key.val
  | .OneTimeKey => before.state.packet.one_time_key.val
  | .PqKey => before.state.packet.pq_key.val

/-- Every Ed verification requests the selected attached field under the same retained identity key. -/
theorem init_ed_request_exact (before : registration.InitEd25519Verification) :
    ∃ request : registration.Ed25519VerificationRequest,
      before.request = ok request ∧ request.public_key = before.public_key ∧
      request.signed.val = edSignedBytes before ∧ 64 ≤ request.signed.val.length := by
  cases stage : before.stage
  all_goals simp [registration.InitEd25519Verification.request, edSignedBytes, stage,
    lift, Bind.bind, Aeneas.Std.bind, Array.to_slice, Array.length_eq, Std.UScalar.ofNatCore_val_eq]

end BeaconcryptCore.Refinement.RegistrationAuthentication

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.identity_tail_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.identity_tail_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_mldsa_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_mldsa_exact
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
/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_mldsa_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_mldsa_request
/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_hash_success
/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthentication.init_ed_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthentication.init_ed_request_exact
