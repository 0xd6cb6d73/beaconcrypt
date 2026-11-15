-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.TranscriptAuthInputs
import BeaconcryptCore.Refinement.TranscriptAuth
import BeaconcryptCore.Model.Pqxdh.SessionTranscript

/-!
Current registration version 3 exact-byte connection. The generated allocation-free encoder retains the complete attached-signature request buffers and the fixed authenticated response fields before sealing. Hashing remains external; this establishes framing and normal return, without an injective-hash assumption.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement Pqxdh

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace SessionTranscriptRefinement

def absInit (fields : authentication.InitFields) : SessionTranscript.InitFields where
  identityKey := absBytes fields.identity_key
  preKey := absBytes fields.pre_key
  oneTimeKey := absBytes fields.one_time_key
  pqKey := absBytes fields.pq_key

def absResponse (fields : authentication.AdResponseFields) : SessionTranscript.ResponseFields where
  identityKey := absBytes fields.identity_key
  ephemeralKey := absBytes fields.ephemeral_key
  kemCipherText := absBytes fields.kem_cipher_text
  keyId := TranscriptAuthRefinement.absId fields.key_id

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

private theorem transcript_closure_list (init : authentication.InitFields)
    (response : authentication.AdResponseFields) (id : Std.Array Std.U8 8#usize)
    (index : Nat) (bound : index < 2638) :
    let closure : authentication.build_record_ad_transcript.closure :=
      (init.identity_key, init.pre_key, init.one_time_key, init.pq_key,
        response.identity_key, response.ephemeral_key, response.kem_cipher_text, id)
    authentication.build_record_ad_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        closure ⟨BitVec.ofNat _ index⟩ =
      ok ((init.identity_key.val ++ init.pre_key.val ++ init.one_time_key.val ++ init.pq_key.val ++
        response.identity_key.val ++ response.ephemeral_key.val ++ response.kem_cipher_text.val ++ id.val)[index]!, closure) := by
  have value := usize_mk_val index (by omega)
  simp only [authentication.build_record_ad_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut,
    Std.UScalar.lt_equiv, value, getByte_append, List.length_append, Std.Array.length_eq]
  dsimp! only [authentication.build_record_ad_transcript.closure]
  norm_num only [Std.UScalar.ofNatCore_val_eq]
  rcases (show index < 33 ∨ (33 ≤ index ∧ index < 131) ∨ (131 ≤ index ∧ index < 229) ∨
      (229 ≤ index ∧ index < 1478) ∨ (1478 ≤ index ∧ index < 1510) ∨
      (1510 ≤ index ∧ index < 1542) ∨ (1542 ≤ index ∧ index < 2630) ∨ 2630 ≤ index by omega) with
    region | region | region | region | region | region | region | region
  all_goals repeat' first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]
  all_goals try erw [index_sub_eq]
  all_goals dsimp only [Std.UScalarTy.numBits] at value
  all_goals norm_num only [value, Std.UScalar.ofNatCore_val_eq]
  all_goals try omega
  erw [index_usize_eq]
  all_goals simp only [bind_tc_ok, value, Std.UScalar.ofNatCore_val_eq]
  all_goals omega

/-- Actual pure-core bytes are exactly the model's fixed 2638-byte field encoding. -/
theorem build_record_ad_transcript_abs (init : authentication.InitFields)
    (response : authentication.AdResponseFields) :
    ∃ output, authentication.build_record_ad_transcript init response = ok output ∧
      absBytes output = SessionTranscript.encode (absInit init) (absResponse response) := by
  unfold authentication.build_record_ad_transcript
  obtain ⟨id, idRun, idAbs⟩ := TranscriptAuthRefinement.encode_u64_le_abs response.key_id
  let bytes := init.identity_key.val ++ init.pre_key.val ++ init.one_time_key.val ++ init.pq_key.val ++
    response.identity_key.val ++ response.ephemeral_key.val ++ response.kem_cipher_text.val ++ id.val
  obtain ⟨output, run, contents⟩ := from_fn_list 2638#usize
    authentication.build_record_ad_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
    (init.identity_key, init.pre_key, init.one_time_key, init.pq_key,
      response.identity_key, response.ephemeral_key, response.kem_cipher_text, id)
    bytes (by simp [bytes, Std.Array.length_eq])
    (fun index bound => transcript_closure_list init response id index bound)
  refine ⟨output, by simpa only [idRun, bind_tc_ok] using run, ?_⟩
  simp only [absBytes, contents, bytes, List.map_append]
  simp only [absBytes] at idAbs
  simp only [SessionTranscript.encode, SessionTranscript.initBlock, absInit, absResponse,
    absBytes, TranscriptAuthRefinement.absId_toNat, idAbs, List.append_assoc]

/-- The current encoder always has a normal return for represented exact-width inputs. -/
theorem build_record_ad_transcript_total (init : authentication.InitFields)
    (response : authentication.AdResponseFields) :
    ∃ output, authentication.build_record_ad_transcript init response = ok output :=
  (build_record_ad_transcript_abs init response).imp fun _ result => result.1

end SessionTranscriptRefinement

/-- info: 'SessionTranscriptRefinement.build_record_ad_transcript_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SessionTranscriptRefinement.build_record_ad_transcript_abs

/-- info: 'SessionTranscriptRefinement.build_record_ad_transcript_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SessionTranscriptRefinement.build_record_ad_transcript_total
