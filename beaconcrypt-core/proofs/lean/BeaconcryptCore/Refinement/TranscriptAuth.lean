-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.Refinement.PqxdhCommitment
import BeaconcryptCore.Refinement.TranscriptAuthInputs
import BeaconcryptCore.Refinement.TranscriptAuthParts
import BeaconcryptCore.Model.Pqxdh.TranscriptAuth

/-!
The complete production extraction's authentication builders refine the exact unsigned byte transcripts. Hashing and ML-DSA remain external primitives.

The same current extraction supplies the generic byte/scalar lemmas, LE64 helper and AD281/CTX357 refinements. The separately generated authentication cohort remains a reproducibility check.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM PqxdhRefinement beaconcrypt_core Pqxdh

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TranscriptAuthRefinement

def absId (value : Std.U64) : UInt64 := UInt64.ofNat value.val

@[simp] theorem absId_toNat (value : Std.U64) : (absId value).toNat = value.val := by
  simp [absId]

def absInit (fields : authentication.InitFields) : TranscriptAuth.InitFields where
  identityKey := absBytes fields.identity_key
  preKey := absBytes fields.pre_key
  oneTimeKey := absBytes fields.one_time_key
  pqKey := absBytes fields.pq_key
  mldsaPublicKey := absBytes fields.mldsa_public_key

def absResponse (fields : authentication.ResponseFields) : TranscriptAuth.ResponseFields where
  identityKey := absBytes fields.identity_key
  ephemeralKey := absBytes fields.ephemeral_key
  kemCipherText := absBytes fields.kem_cipher_text
  appCipherText := fields.app_cipher_text.val.map absByte
  keyId := absId fields.key_id

/-- The selected extraction uses the same fully checked LE64 operations. -/
theorem encode_u64_le_abs (value : Std.U64) :
    ∃ bytes, authentication.encode_u64_le value = ok bytes ∧
      absBytes bytes = Pqxdh.LE64 value.val := by
  exact commitment_encode_u64_le_abs value

private theorem index_sub_eq {Output : Type} {n : Std.Usize} (bytes : Std.Array Std.U8 n)
    (index offset : Std.Usize) (lower : offset.val ≤ index.val)
    (upper : index.val - offset.val < n.val) (fits : index.val < 2 ^ 32)
    (next : Std.U8 → RustM Output) :
    (do let adjusted ← index - offset; let byte ← Std.Array.index_usize bytes adjusted; next byte) =
      next bytes.val[index.val - offset.val]! := by
  rw [usize_sub_eq index offset lower]
  simp only [bind_tc_ok]
  have value := usize_mk_val (index.val - offset.val) (by omega)
  rw [index_usize_eq bytes _ (by omega), value]
  simp only [bind_tc_ok]

private theorem from_fn_list {Closure : Type} (size : Std.Usize)
    (inst : core.ops.function.FnMut Closure Std.Usize Std.U8) (closure : Closure)
    (bytes : List Std.U8) (width : bytes.length = size.val)
    (each : ∀ index, index < size.val →
      inst.call_mut closure ⟨BitVec.ofNat _ index⟩ = ok (bytes[index]!, closure)) :
    ∃ output, core.array.from_fn size inst closure = ok output ∧ output.val = bytes := by
  simpa only [← width, map_range_getElem!] using
    from_fn_pure size inst closure (fun index => bytes[index]!) each

private theorem getByte_append (left right : List Std.U8) (index : Nat) :
    (left ++ right)[index]! =
      if index < left.length then left[index]! else right[index - left.length]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
  split_ifs <;> rfl

private theorem init_closure_list (fields : authentication.InitFields)
    (serverId : Std.Array Std.U8 8#usize) (serverEd : Std.Array Std.U8 32#usize)
    (serverMldsa : Std.Array Std.U8 1952#usize)
    (identityLength signedLength pqLength : Std.Array Std.U8 8#usize)
    (index : Nat) (bound : index < 5495) :
    let closure : authentication.build_init_transcript.closure :=
      (serverId, serverEd, fields.identity_key, fields.pre_key, fields.one_time_key,
        fields.pq_key, fields.mldsa_public_key, serverMldsa, identityLength, signedLength, pqLength)
    authentication.build_init_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        closure ⟨BitVec.ofNat _ index⟩ =
      ok ((authentication.INIT_DOMAIN.val ++ serverId.val ++ serverEd.val ++
        fields.mldsa_public_key.val ++ serverMldsa.val ++ identityLength.val ++
        fields.identity_key.val ++ signedLength.val ++ fields.pre_key.val ++ signedLength.val ++
        fields.one_time_key.val ++ pqLength.val ++ fields.pq_key.val)[index]!, closure) := by
  have value := usize_mk_val index (by omega)
  simp only [authentication.build_init_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    Std.UScalar.lt_equiv, value, getByte_append, List.length_append, Std.Array.length_eq]
  dsimp! only [authentication.build_init_transcript.closure]
  dsimp only [Std.UScalarTy.numBits] at value
  norm_num only [Std.UScalar.ofNatCore_val_eq]
  rcases (show index < 41 ∨ (41 ≤ index ∧ index < 49) ∨ (49 ≤ index ∧ index < 81) ∨
      (81 ≤ index ∧ index < 2033) ∨ (2033 ≤ index ∧ index < 3985) ∨
      (3985 ≤ index ∧ index < 3993) ∨ (3993 ≤ index ∧ index < 4026) ∨
      (4026 ≤ index ∧ index < 4034) ∨ (4034 ≤ index ∧ index < 4132) ∨
      (4132 ≤ index ∧ index < 4140) ∨ (4140 ≤ index ∧ index < 4238) ∨
      (4238 ≤ index ∧ index < 4246) ∨ 4246 ≤ index by omega) with
    region | region | region | region | region | region | region | region | region |
      region | region | region | region
  all_goals repeat' first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]
  all_goals try erw [index_sub_eq]
  all_goals norm_num only [value, Std.UScalar.ofNatCore_val_eq]
  all_goals try omega
  erw [index_usize_eq authentication.INIT_DOMAIN ⟨BitVec.ofNat _ index⟩
    (by simpa only [usize_mk_val index (by omega), Std.UScalar.ofNatCore_val_eq] using region)]
  simp only [bind_tc_ok, usize_mk_val index (by omega)]

/-- The actual extracted request builder emits exactly the unsigned model transcript. -/
theorem build_init_transcript_abs (fields : authentication.InitFields) (serverId : Std.U64)
    (serverEd : Std.Array Std.U8 32#usize) (serverMldsa : Std.Array Std.U8 1952#usize) :
    ∃ output, authentication.build_init_transcript fields serverId serverEd serverMldsa = ok output ∧
      absBytes output = TranscriptAuth.initTranscript (absInit fields) (absId serverId)
        (absBytes serverEd) (absBytes serverMldsa) := by
  unfold authentication.build_init_transcript
  obtain ⟨serverBytes, serverSuccess, serverAbs⟩ := encode_u64_le_abs serverId
  obtain ⟨identityLength, identitySuccess, identityAbs⟩ := encode_u64_le_abs 33#u64
  obtain ⟨signedLength, signedSuccess, signedAbs⟩ := encode_u64_le_abs 98#u64
  obtain ⟨pqLength, pqSuccess, pqAbs⟩ := encode_u64_le_abs 1249#u64
  let bytes := authentication.INIT_DOMAIN.val ++ serverBytes.val ++ serverEd.val ++
    fields.mldsa_public_key.val ++ serverMldsa.val ++ identityLength.val ++
    fields.identity_key.val ++ signedLength.val ++ fields.pre_key.val ++ signedLength.val ++
    fields.one_time_key.val ++ pqLength.val ++ fields.pq_key.val
  have width : bytes.length = (5495#usize).val := by
    norm_num only [bytes, List.length_append, Std.Array.length_eq, Std.UScalar.ofNatCore_val_eq]
  obtain ⟨output, success, contents⟩ := from_fn_list 5495#usize
    authentication.build_init_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    (serverBytes, serverEd, fields.identity_key, fields.pre_key, fields.one_time_key,
      fields.pq_key, fields.mldsa_public_key, serverMldsa, identityLength, signedLength, pqLength)
    bytes width (fun index bound => init_closure_list fields serverBytes serverEd serverMldsa
      identityLength signedLength pqLength index
      (by simpa only [Std.UScalar.ofNatCore_val_eq] using bound))
  refine ⟨output, by simpa only [serverSuccess, identitySuccess, signedSuccess, pqSuccess, bind_tc_ok]
    using success, ?_⟩
  simp only [absBytes, contents, bytes, List.map_append]
  simp only [absBytes] at serverAbs identityAbs signedAbs pqAbs
  simp only [show authentication.INIT_DOMAIN.val.map absByte = TranscriptAuth.initDomain from
      TranscriptAuthInputsRefinement.init_domain_abs,
    serverAbs, identityAbs, signedAbs, pqAbs, TranscriptAuth.initTranscript, absInit,
    TranscriptAuth.hashField, absBytes, List.length_map, Std.Array.length_eq,
    absId_toNat, Std.UScalar.ofNatCore_val_eq, List.append_assoc]

private theorem response_closure_list (initHash : Std.Array Std.U8 64#usize)
    (identity ephemeral : Std.Array Std.U8 32#usize) (kem : Std.Array Std.U8 1088#usize)
    (publicLength kemLength appLength : Std.Array Std.U8 8#usize)
    (index : Nat) (bound : index < 1293) :
    let closure : authentication.build_response_prefix.closure :=
      (initHash, publicLength, identity, ephemeral, kemLength, kem, appLength)
    authentication.build_response_prefix.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        closure ⟨BitVec.ofNat _ index⟩ =
      ok ((authentication.RESPONSE_DOMAIN.val ++ initHash.val ++ publicLength.val ++ identity.val ++
        publicLength.val ++ ephemeral.val ++ kemLength.val ++ kem.val ++ appLength.val)[index]!, closure) := by
  have value := usize_mk_val index (by omega)
  simp only [authentication.build_response_prefix.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    Std.UScalar.lt_equiv, value, getByte_append, List.length_append, Std.Array.length_eq]
  dsimp! only [authentication.build_response_prefix.closure, Std.UScalarTy.numBits] at value ⊢
  norm_num only [Std.UScalar.ofNatCore_val_eq]
  rcases (show index < 45 ∨ (45 ≤ index ∧ index < 109) ∨ (109 ≤ index ∧ index < 117) ∨
      (117 ≤ index ∧ index < 149) ∨ (149 ≤ index ∧ index < 157) ∨
      (157 ≤ index ∧ index < 189) ∨ (189 ≤ index ∧ index < 197) ∨
      (197 ≤ index ∧ index < 1285) ∨ 1285 ≤ index by omega) with
    region | region | region | region | region | region | region | region | region
  all_goals repeat' first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]
  all_goals try erw [index_sub_eq]
  all_goals norm_num only [value, Std.UScalar.ofNatCore_val_eq]
  all_goals try omega
  erw [index_usize_eq authentication.RESPONSE_DOMAIN ⟨BitVec.ofNat _ index⟩
    (by simpa only [usize_mk_val index (by omega), Std.UScalar.ofNatCore_val_eq] using region)]
  simp only [bind_tc_ok, usize_mk_val index (by omega)]

/-- The streamed prefix ends with the checked length of the same application body. -/
def responsePrefix (initHash : Std.Array Std.U8 64#usize)
    (identity ephemeral : Std.Array Std.U8 32#usize) (kem : Std.Array Std.U8 1088#usize)
    (appLength : Nat) : Pqxdh.Bytes :=
  TranscriptAuth.responseDomain ++ absBytes initHash ++ TranscriptAuth.hashField (absBytes identity) ++
    TranscriptAuth.hashField (absBytes ephemeral) ++ TranscriptAuth.hashField (absBytes kem) ++
    Pqxdh.LE64 appLength

/-- The actual extracted fixed prefix is exactly the response model through its body length. -/
theorem build_response_prefix_abs (initHash : Std.Array Std.U8 64#usize)
    (identity ephemeral : Std.Array Std.U8 32#usize) (kem : Std.Array Std.U8 1088#usize)
    (appLength : Std.U64) :
    ∃ output, authentication.build_response_prefix initHash identity ephemeral kem appLength = ok output ∧
      absBytes output = responsePrefix initHash identity ephemeral kem appLength.val := by
  obtain ⟨publicLength, publicSuccess, publicAbs⟩ := encode_u64_le_abs 32#u64
  obtain ⟨kemLength, kemSuccess, kemAbs⟩ := encode_u64_le_abs 1088#u64
  obtain ⟨appBytes, appSuccess, appAbs⟩ := encode_u64_le_abs appLength
  obtain ⟨output, success, contents⟩ := from_fn_list 1293#usize
    authentication.build_response_prefix.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    (initHash, publicLength, identity, ephemeral, kemLength, kem, appBytes)
    (authentication.RESPONSE_DOMAIN.val ++ initHash.val ++ publicLength.val ++ identity.val ++
      publicLength.val ++ ephemeral.val ++ kemLength.val ++ kem.val ++ appBytes.val)
    (by norm_num only [List.length_append, Std.Array.length_eq, Std.UScalar.ofNatCore_val_eq])
    (fun index bound => response_closure_list initHash identity ephemeral kem publicLength kemLength
      appBytes index (by simpa only [Std.UScalar.ofNatCore_val_eq] using bound))
  refine ⟨output, by simpa only [authentication.build_response_prefix, publicSuccess, kemSuccess,
    appSuccess, bind_tc_ok] using success, ?_⟩
  simp only [absBytes] at publicAbs kemAbs appAbs
  simp only [absBytes, contents, List.map_append,
    show authentication.RESPONSE_DOMAIN.val.map absByte = TranscriptAuth.responseDomain from
      TranscriptAuthInputsRefinement.response_domain_abs,
    publicAbs, kemAbs, appAbs, responsePrefix, TranscriptAuth.hashField,
    List.length_map, Std.Array.length_eq, Std.UScalar.ofNatCore_val_eq, List.append_assoc]

/-- Concatenating the actual returned slices yields the complete unsigned response transcript. -/
theorem build_response_transcript_abs (initHash : Std.Array Std.U8 64#usize)
    (fields : authentication.ResponseFields) :
    ∃ response parts,
      authentication.build_response_transcript initHash fields = ok (.Some response) ∧
      authentication.ResponseTranscript.parts response = ok parts ∧
      TranscriptAuthParts.absParts parts =
        TranscriptAuth.responseTranscript (absBytes initHash) (absResponse fields) := by
  have prefixRefines : ∀ length : Std.U64, length.val = fields.app_cipher_text.val.length →
      ∃ output, authentication.build_response_prefix initHash fields.identity_key
          fields.ephemeral_key fields.kem_cipher_text length = ok output ∧
        absBytes output = responsePrefix initHash fields.identity_key fields.ephemeral_key
          fields.kem_cipher_text fields.app_cipher_text.val.length := by
    intro length sameLength
    simpa only [sameLength] using build_response_prefix_abs initHash fields.identity_key
      fields.ephemeral_key fields.kem_cipher_text length
  simpa only [responsePrefix, absResponse, TranscriptAuth.responseTranscript, TranscriptAuth.hashField,
    TranscriptAuthParts.absSlice, List.length_map, absId_toNat, List.append_assoc] using
    TranscriptAuthParts.build_response_transcript_parts initHash fields
      (responsePrefix initHash fields.identity_key fields.ephemeral_key fields.kem_cipher_text
        fields.app_cipher_text.val.length) prefixRefines

/-- info: 'TranscriptAuthRefinement.absId_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms absId_toNat

/-- info: 'TranscriptAuthRefinement.encode_u64_le_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encode_u64_le_abs

/-- info: 'TranscriptAuthRefinement.build_init_transcript_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms build_init_transcript_abs

/-- info: 'TranscriptAuthRefinement.build_response_prefix_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms build_response_prefix_abs

/-- info: 'TranscriptAuthRefinement.build_response_transcript_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms build_response_transcript_abs

end TranscriptAuthRefinement
