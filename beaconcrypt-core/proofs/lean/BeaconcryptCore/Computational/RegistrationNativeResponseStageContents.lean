-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerContents

/-! A reached native Server record path gives the canonical unsigned response fields before hashing or signing. Matching that source-stage payload with a Beacon trial determines its actual ciphertext, assigned identifier and public agreement inputs. This is a contents bridge, not a premise or claim of completed partner installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseStageContents
open BeaconcryptCore.Refinement.RegistrationPublication
open BeaconcryptCore.Refinement.RegistrationResponse
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command)

/-- Even before response signing, the actual last raw-writer continuation fixes the complete unsigned response to its own retained candidate and ciphertext. -/
theorem path_payload (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (path : RegistrationServerRecordExecutor.Path initial hashed) :
    Command.payload (.server hashed) = MldsaTranscriptAuth.responsePayload (absBytes hashed.binding.init_hash)
      (TranscriptAuthRefinement.absResponse (serverResponseFields hashed.candidate hashed.ciphertext)) := by
  cases path with
  | mk initialReply ratchetPhase initialResume ratchetReply aead ratchetResume aeadReply commitmentPhase
      aeadResume hashReply writePhase commitmentResume writeReply writeResume =>
    obtain ⟨result, resumed, retained⟩ := server_seal_preimage_refines writePhase writeReply
    have same : result = .Ok hashed := by simpa using resumed.symm.trans writeResume
    rw [same] at retained
    obtain ⟨candidate, binding, _kernel, _ciphertext, request, requested, bytes⟩ := retained
    obtain ⟨actualRequest, actualRequested, actualBytes⟩ := server_hash_request_refines hashed
    have requestEq : request = actualRequest := RustM.ok.inj (requested.symm.trans actualRequested)
    have transcript : absBytes hashed.prefix ++ TranscriptAuthParts.absSlice hashed.ciphertext ++ absBytes hashed.assigned_id =
        Pqxdh.TranscriptAuth.responseTranscript (absBytes hashed.binding.init_hash)
          (TranscriptAuthRefinement.absResponse (serverResponseFields hashed.candidate hashed.ciphertext)) := by
      rw [requestEq, actualBytes] at bytes
      simpa only [candidate, binding] using bytes
    exact congrArg (MldsaTranscriptAuth.Payload.mk .server) transcript

private theorem response_valid (fields : authentication.ResponseFields) :
    (TranscriptAuthRefinement.absResponse fields).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [TranscriptAuthRefinement.absResponse, absBytes]
  · simp [TranscriptAuthRefinement.absResponse, absBytes]
  · simp [TranscriptAuthRefinement.absResponse, absBytes]
  · change (fields.app_cipher_text.val.map absByte).length < 2 ^ 64
    rw [List.length_map]
    have bound := fields.app_cipher_text.property
    have limit : Usize.max < 2 ^ 64 := by
      cases System.Platform.numBits_eq with
      | inl bits => simp [Usize.max, Usize.numBits, UScalarTy.numBits, bits]
      | inr bits => simp [Usize.max, Usize.numBits, UScalarTy.numBits, bits]
    exact lt_of_le_of_lt bound limit

/-- Matching the source-stage unsigned payload determines the full response contents and original Init digest. -/
theorem response_fields (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (path : RegistrationServerRecordExecutor.Path initial hashed)
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (payloadSame : Command.payload (.server hashed) = RegistrationResponseExecutor.payload pending packet) :
    TranscriptAuthRefinement.absResponse (serverResponseFields hashed.candidate hashed.ciphertext) =
        TranscriptAuthRefinement.absResponse (responseFields packet) ∧
      hashed.binding.init_hash = pending.binding.init_hash := by
  have same := congrArg MldsaTranscriptAuth.Payload.transcript ((path_payload initial hashed path).symm.trans payloadSame)
  change Pqxdh.TranscriptAuth.responseTranscript (absBytes hashed.binding.init_hash)
      (TranscriptAuthRefinement.absResponse (serverResponseFields hashed.candidate hashed.ciphertext)) =
    Pqxdh.TranscriptAuth.responseTranscript (absBytes pending.binding.init_hash)
      (TranscriptAuthRefinement.absResponse (responseFields packet)) at same
  obtain ⟨fields, hashes⟩ := Pqxdh.TranscriptAuth.responseTranscript_inj
    (response_valid _) (response_valid _) (by simp [absBytes]) same
  exact ⟨fields, Subtype.ext ((absBytes_inj_iff _ _).mp hashes)⟩

/-- The typed native response field abstraction is injective, including raw ciphertext slices and identifiers. -/
theorem response_injective {left right : authentication.ResponseFields}
    (same : TranscriptAuthRefinement.absResponse left = TranscriptAuthRefinement.absResponse right) : left = right := by
  have identityEq : left.identity_key = right.identity_key :=
    Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.ResponseFields.identityKey same))
  have ephemeralEq : left.ephemeral_key = right.ephemeral_key :=
    Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.ResponseFields.ephemeralKey same))
  have kemEq : left.kem_cipher_text = right.kem_cipher_text :=
    Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.ResponseFields.kemCipherText same))
  have applicationEq : left.app_cipher_text = right.app_cipher_text := by
    apply Subtype.ext
    exact List.map_injective_iff.mpr absByte_injective (congrArg Pqxdh.TranscriptAuth.ResponseFields.appCipherText same)
  have idEq : left.key_id = right.key_id := by
    apply UScalar.eq_of_val_eq
    have ids := congrArg (fun fields : Pqxdh.TranscriptAuth.ResponseFields => fields.keyId.toNat) same
    simpa only [TranscriptAuthRefinement.absResponse, TranscriptAuthRefinement.absId_toNat] using ids
  cases left
  cases right
  simp_all only

/-- Source payload origin fixes the exact raw ciphertext, assigned identifier and all three native public agreement fields; no ML signature-byte equality is inferred. -/
theorem native_fields (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (path : RegistrationServerRecordExecutor.Path initial hashed)
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (payloadSame : Command.payload (.server hashed) = RegistrationResponseExecutor.payload pending packet) :
    hashed.candidate.server_identity_public_key = packet.public.identity_key ∧
      hashed.candidate.ephemeral_public_key = packet.public.ephemeral_key ∧
      hashed.candidate.kem_ciphertext = packet.public.kem_cipher_text ∧
      hashed.ciphertext = packet.application ∧ hashed.candidate.key_id = packet.public.key_id ∧
      hashed.binding.init_hash = pending.binding.init_hash := by
  obtain ⟨fields, hashes⟩ := response_fields initial hashed path pending packet payloadSame
  have exactFields := response_injective fields
  exact ⟨congrArg authentication.ResponseFields.identity_key exactFields,
    congrArg authentication.ResponseFields.ephemeral_key exactFields,
    congrArg authentication.ResponseFields.kem_cipher_text exactFields,
    congrArg authentication.ResponseFields.app_cipher_text exactFields,
    congrArg authentication.ResponseFields.key_id exactFields, hashes⟩

end BeaconcryptCore.Computational.RegistrationNativeResponseStageContents
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.path_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.path_payload

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.response_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.response_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.response_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.response_injective

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.native_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseStageContents.native_fields
