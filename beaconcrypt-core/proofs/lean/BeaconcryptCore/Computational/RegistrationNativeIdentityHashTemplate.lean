-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition
import BeaconcryptCore.Computational.RegistrationNativeInitStageContents

/-! The original attached-signature Init hash request has one exact64-byte one-time signature window. Its leading bytes use the source fixed width98 and all remaining retained fields; no signature-byte-dependent length is exposed. The actual canonical-builder receipt supplies the request, rather than a caller hash-template equation. Actual Ed-copy receipts separately establish the attached-field witness. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate
open BeaconcryptCore.Refinement
open RegistrationSigningContinuations (retainedFields)
open PqxdhEd25519EufCma (Ed25519PublicKey Ed25519Signature)

def leading (state : registration.BeaconInitState) : Pqxdh.Bytes :=
  Pqxdh.TranscriptAuth.initDomain ++ Pqxdh.LE64 (TranscriptAuthRefinement.absId state.server_pin.binding.identity_key_id).toNat ++
    absBytes state.server_pin.binding.identity_public_key ++ absBytes state.server_pin.public_key ++
    Pqxdh.TranscriptAuth.hashField (absBytes state.started.message.identity_key) ++
    Pqxdh.TranscriptAuth.hashField (absBytes state.pre_key) ++ Pqxdh.LE64 98

def trailing (state : registration.BeaconInitState) (message : Pqxdh.Bytes) : Pqxdh.Bytes :=
  message ++ Pqxdh.TranscriptAuth.hashField (absBytes state.pq_key)

private theorem template (state : registration.BeaconInitState) (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (attached : absBytes state.one_time_key = signature.toList ++ message) :
    Pqxdh.TranscriptAuth.initTranscript (TranscriptAuthRefinement.absInit (retainedFields state))
      (TranscriptAuthRefinement.absId state.server_pin.binding.identity_key_id)
      (absBytes state.server_pin.binding.identity_public_key) (absBytes state.server_pin.public_key) =
      leading state ++ signature.toList ++ trailing state message := by
  have framed : Pqxdh.TranscriptAuth.hashField (absBytes state.one_time_key) =
      Pqxdh.LE64 98 ++ signature.toList ++ message := by
    simp only [Pqxdh.TranscriptAuth.hashField, absBytes_length]
    rw [attached]
    rfl
  simp only [Pqxdh.TranscriptAuth.initTranscript, TranscriptAuthRefinement.absInit, retainedFields, framed,
    leading, trailing, List.append_assoc]

/-- The actual canonical request-hash input contains this precise Ed signature window. -/
theorem source (pending : registration.BeaconInitHash)
    (canonical : RegistrationNativeInitStageContents.Canonical pending)
    (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (attached : absBytes pending.state.one_time_key = signature.toList ++ message) :
    ∃ request, pending.request = .ok request ∧
      RegistrationInputs.hashBytes request = leading pending.state ++ signature.toList ++ trailing pending.state message := by
  refine ⟨.Single pending.input.to_slice, rfl, ?_⟩
  exact canonical.trans (template pending.state signature message attached)

/-- Recognition finds a valid target Ed signature in the actual reached request, without canonical-signature uniqueness. -/
theorem recognized (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (target : Pqxdh.Bytes)
    (pending : registration.BeaconInitHash) (canonical : RegistrationNativeInitStageContents.Canonical pending)
    (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (attached : absBytes pending.state.one_time_key = signature.toList ++ message)
    (valid : verify publicKey target signature = true) :
    ∃ request, pending.request = .ok request ∧
      (RegistrationNativeIdentityRecognition.recognize verify publicKey target (RegistrationInputs.hashBytes request)).isSome = true := by
  obtain ⟨request, requested, bytes⟩ := source pending canonical signature message attached
  exact ⟨request, requested, bytes ▸
    RegistrationNativeIdentityRecognition.template_recognized verify publicKey target (leading pending.state)
      (trailing pending.state message) signature valid⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate.recognized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate.recognized
