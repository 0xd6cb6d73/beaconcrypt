-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldServerPublication
import BeaconcryptCore.Computational.RegistrationNativeWire

/-! Actual Server response encoding retains the KEM ciphertext of its owned candidate through digest and ML signature admission, including every failed optional reply. These source publication receipts apply independently of the record kernel or KEM provider. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext
open RegistrationWorldServerPublication (ready signing program continueWith continueResult)
open RegistrationSigningShared (Spec)
variable {Encoded : Type}

def EncodedFrom (encode : registration.SignedResponseView → core.option.Option Encoded)
    (ciphertext : Std.Array U8 1088#usize) (bytes : Encoded) : Prop :=
  ∃ view, encode view = .Some bytes ∧ view.kem_cipher_text = ciphertext

/-- Actual publication encodes the exact KEM ciphertext retained by the ready native capability. -/
theorem ready_ciphertext (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (ready encode pending)) :
    EncodedFrom encode pending.candidate.kem_ciphertext published.encoded := by
  let view : registration.SignedResponseView := ⟨pending.candidate.server_identity_public_key,
    pending.candidate.ephemeral_public_key, pending.candidate.kem_ciphertext, pending.candidate.key_id,
    pending.ciphertext, pending.signature⟩
  have message : pending.message = .ok view := rfl
  simp only [ready, message, continueWith, support_pure, Set.mem_singleton_iff] at supported
  rw [BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines] at supported
  cases encoded : encode view with
  | none => simp only [encoded] at supported; cases supported
  | some bytes =>
      simp only [encoded, RustM.ok.injEq, core.result.Result.Ok.injEq] at supported
      cases supported
      exact ⟨view, encoded, rfl⟩

/-- The actual signature gate never changes the candidate KEM ciphertext before encoding. -/
theorem signing_ciphertext (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (signing encode payload digest pending)) :
    EncodedFrom encode pending.candidate.kem_ciphertext published.encoded := by
  have request : pending.request = .ok ⟨pending.binding.server_pin.public_key, .Server,
      pending.input, authentication.SIGNING_CONTEXT⟩ := rfl
  simp only [signing, request, continueWith, mem_support_bind_iff] at supported
  obtain ⟨signature, _signed, continued⟩ := supported
  cases signature with
  | none => simp only [registration.ServerResponseSigning.resume, continueResult] at continued; cases continued
  | some signature =>
      obtain ⟨reply, admitted, retained⟩ := BeaconcryptCore.Refinement.RegistrationPublication.server_signature_admission_refines pending signature
      rw [admitted] at continued
      cases reply with
      | Err previous => simp only [continueResult, support_pure, Set.mem_singleton_iff] at continued; cases continued
      | Ok current =>
          have receipt := ready_ciphertext encode current published continued
          rw [retained.1] at receipt
          exact receipt

set_option maxRecDepth 2048 in
/-- The complete actual response hash/sign/publication tree encodes only its retained candidate KEM ciphertext. -/
theorem program_ciphertext (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (program encode pending)) :
    EncodedFrom encode pending.candidate.kem_ciphertext published.encoded := by
  obtain ⟨request, requested, _bytes⟩ := BeaconcryptCore.Refinement.RegistrationPublication.server_hash_request_refines pending
  simp only [program, requested, continueWith, mem_support_bind_iff] at supported
  obtain ⟨digest, _hashed, continued⟩ := supported
  obtain ⟨current, resumed, candidate, _binding, _kernel, _ciphertext, _input, _request⟩ :=
    BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed] at continued
  have receipt := signing_ciphertext encode _ digest current published continued
  rw [candidate] at receipt
  exact receipt

/-- Native response readback recovers the actual encoded candidate KEM ciphertext used by original public designation. -/
theorem readback_ciphertext (wire : RegistrationNativeWire.Wire) (readback : RegistrationNativeWire.ResponseReadBack wire)
    (ciphertext : Std.Array U8 1088#usize) (bytes : Pqxdh.Bytes) (encoded : EncodedFrom wire.encodeResponse ciphertext bytes) :
    ((RegistrationNativeWire.ledgerCodec wire).read2 bytes).bind (RegistrationNativeWire.ledgerCodec wire).ciphertext = some ciphertext := by
  obtain ⟨view, written, same⟩ := encoded
  simp only [RegistrationNativeWire.ledgerCodec, readback view bytes written, Option.bind_some,
    RegistrationNativeWire.responsePacket, same]


end BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.ready_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.ready_ciphertext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.signing_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.signing_ciphertext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.program_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.program_ciphertext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.readback_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext.readback_ciphertext
