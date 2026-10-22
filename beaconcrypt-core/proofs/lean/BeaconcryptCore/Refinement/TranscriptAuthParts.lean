-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AuthenticationExtraction.Funs
import BeaconcryptCore.Refinement.PqxdhCommitment
import BeaconcryptCore.Model.Pqxdh.TranscriptAuth

/-!
The extracted response wrapper returns its fixed prefix, the same borrowed body whose length was checked, and its assigned-ID suffix in that order. These pure byte facts assume no hash/signature security or SDK streaming implementation. Historical refinement imports supply only checked generic byte/LE64 helpers.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM PqxdhRefinement beaconcrypt_authentication_core

set_option autoImplicit false

namespace TranscriptAuthParts

def absSlice (slice : Aeneas.Std.Slice Std.U8) : Pqxdh.Bytes := slice.val.map absByte

def absParts (parts : Std.Array (Aeneas.Std.Slice Std.U8) 3#usize) : Pqxdh.Bytes :=
  (parts.val.map absSlice).flatten

private theorem usize_to_u64 (value : Std.Usize) :
    core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from value =
      ok (core.result.Result.Ok (UScalar.cast .U64 value)) := by
  simp only [core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from,
    lift, bind_tc_ok]
  simp only [core.num.U64.MAX, core.num.U64.MIN]
  cases System.Platform.numBits_eq <;> simp [*, UScalar.lt_equiv, UScalar.cast_val_eq]
  all_goals norm_num [U64.rMax]
  all_goals have bounds := value.hBounds
  all_goals simp [UScalarTy.numBits, *] at bounds
  all_goals omega

private theorem usize_to_u64_value (value : Std.Usize) :
    (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]

/-- The actual extracted method returns prefix/body/assigned-ID slices in order. -/
theorem ordered_parts (response : authentication.ResponseTranscript) :
    ∃ parts, authentication.ResponseTranscript.parts response = ok parts ∧
      absParts parts = absBytes response.prefix ++ absSlice response.application ++
        absBytes response.assigned_id := by
  refine ⟨_, rfl, ?_⟩
  change absBytes response.prefix ++
    (absSlice response.application ++ (absBytes response.assigned_id ++ [])) = _
  simp only [List.append_nil, List.append_assoc]

theorem build_response_transcript_parts
    (initHash : Std.Array Std.U8 64#usize) (fields : authentication.ResponseFields)
    (prefixBytes : Pqxdh.Bytes)
    (prefixRefines : ∀ length : Std.U64,
      length.val = fields.app_cipher_text.val.length →
      ∃ buffer, authentication.build_response_prefix initHash fields.identity_key
        fields.ephemeral_key fields.kem_cipher_text length = ok buffer ∧
        absBytes buffer = prefixBytes) :
    ∃ response parts,
      authentication.build_response_transcript initHash fields = ok (.Some response) ∧
      authentication.ResponseTranscript.parts response = ok parts ∧
      absParts parts = prefixBytes ++ absSlice fields.app_cipher_text ++
        Pqxdh.LE64 fields.key_id.val := by
  unfold authentication.build_response_transcript
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  simp only [usize_to_u64, bind_tc_ok]
  obtain ⟨buffer, built, sameBytes⟩ := prefixRefines
    (UScalar.cast .U64 fields.app_cipher_text.len)
    ((usize_to_u64_value _).trans (Aeneas.Std.Slice.len_val _))
  obtain ⟨assigned, builtId, idBytes⟩ := (show ∃ bytes,
      authentication.encode_u64_le fields.key_id = ok bytes ∧
        absBytes bytes = Pqxdh.LE64 fields.key_id.val from
      commitment_encode_u64_le_abs fields.key_id)
  obtain ⟨parts, builtParts, partsBytes⟩ := ordered_parts
    (⟨buffer, fields.app_cipher_text, assigned⟩ : authentication.ResponseTranscript)
  refine ⟨⟨buffer, fields.app_cipher_text, assigned⟩, parts, ?_, builtParts, ?_⟩
  · simp only [built, builtId, bind_tc_ok]
  · simpa only [sameBytes, idBytes] using partsBytes

/-- info: 'TranscriptAuthParts.ordered_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ordered_parts

/-- info: 'TranscriptAuthParts.build_response_transcript_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms build_response_transcript_parts

end TranscriptAuthParts
