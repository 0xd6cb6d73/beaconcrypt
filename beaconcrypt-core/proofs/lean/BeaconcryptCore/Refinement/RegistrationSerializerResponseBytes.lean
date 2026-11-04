-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSerializerInitBytes
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual public Response serialization for the complete current schema, arbitrary application bytes including empty, and every U64 identifier. Exact source field/counter/writeback composition and the actual array rotation derive the whole prefix, untouched suffix, slice length and nonwrapping returned cursor. Actual complete-size admission is linked to the source sizing operation, and oversized requests return zero without changing the output. No codec-law premise is supplied; decoding and native-instance composition remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical RegistrationSerializerFields
open RegistrationSerializerReachableSource RegistrationSerializerStages
open RegistrationSerializerInitBytes

def ResponseShape (value : transport.kexresponse) : Prop :=
  value.identity_key.length = 32 ∧ value.ephemeral_key.length = 32 ∧
    value.kem_cipher_text.length = 1088 ∧ value.signature.length = 3309

def applicationLength (value : transport.kexresponse) : Nat :=
  (writtenCount (UScalar.cast .U64 value.app_cipher_text.len)).val + value.app_cipher_text.length

def keyLength (value : transport.kexresponse) : Nat := (writtenCount value.key_id).val

def bodyLength (value : transport.kexresponse) : Nat := 4473 + applicationLength value + keyLength value

def totalLength (value : transport.kexresponse) : Nat := bodyLength value + 1

def afterApplication (value : transport.kexresponse) : Usize :=
  Usize.wrapping_add 1161#usize (byteCount value.app_cipher_text)

def afterKey (value : transport.kexresponse) : Usize :=
  Usize.wrapping_add (afterApplication value) (writtenCount value.key_id)

def beforeArray (value : transport.kexresponse) : Usize :=
  Usize.wrapping_add (afterKey value) 3312#usize

def finalCursor (value : transport.kexresponse) : Usize :=
  Usize.wrapping_add (beforeArray value) 1#usize

def payload (value : transport.kexresponse) : List U8 :=
  [2#u8, 1#u8] ++ fieldBytes value.identity_key ++ fieldBytes value.ephemeral_key ++
    fieldBytes value.kem_cipher_text ++ fieldBytes value.app_cipher_text ++
    encodedBytes cbor_major_type_uint64 value.key_id ++ fieldBytes value.signature

theorem add_value (out : Slice U8) (left right : Usize) (fit : left.val + right.val ≤ out.length) :
    (Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Usize.wrapping_add_val_eq, UScalar.size_def]
  apply Nat.mod_eq_of_lt
  have bounded := out.len.hBounds
  rw [Slice.len_val] at bounded
  omega

theorem offsets (value : transport.kexresponse) (out : Slice U8)
    (fit : totalLength value ≤ out.length) :
    (byteCount value.app_cipher_text).val = applicationLength value ∧
      (afterApplication value).val = 1161 + applicationLength value ∧
      (afterKey value).val = 1161 + applicationLength value + keyLength value ∧
      (beforeArray value).val = bodyLength value ∧
      (finalCursor value).val = totalLength value := by
  have expanded : 4473 + applicationLength value + keyLength value + 1 ≤ out.length := fit
  have bytes := byte_count_value out value.app_cipher_text (by
    change applicationLength value ≤ out.length
    omega)
  change (byteCount value.app_cipher_text).val = applicationLength value at bytes
  have application : (afterApplication value).val = 1161 + applicationLength value := by
    unfold afterApplication
    rw [add_value out _ _ (by rw [bytes]; change (1161#usize).val + applicationLength value ≤ out.length; scalar_tac), bytes]
    congr 1
  have key : (afterKey value).val = 1161 + applicationLength value + keyLength value := by
    unfold afterKey
    rw [add_value out _ _ (by rw [application]; change 1161 + applicationLength value + keyLength value ≤ out.length; omega), application]
    rfl
  have body : (beforeArray value).val = bodyLength value := by
    unfold beforeArray
    rw [add_value out _ _ (by rw [key]; change 1161 + applicationLength value + keyLength value + (3312#usize).val ≤ out.length; scalar_tac), key]
    have constant : (3312#usize).val = 3312 := by scalar_tac
    rw [constant]
    unfold bodyLength
    omega
  have complete : (finalCursor value).val = totalLength value := by
    unfold finalCursor
    have constant : (1#usize).val = 1 := by scalar_tac
    rw [add_value out _ _ (by rw [body, constant]; exact fit), body, constant]
    rfl
  exact ⟨bytes, application, key, body, complete⟩

structure ResponseStages (other : OtherBranches) (value : transport.kexresponse) (out : Slice U8) where
  first : UIntStage other out 0#usize 2#u64
  second : UIntStage other first.stage.after 1#usize 1#u64
  identity : Stage (@transport.serialize_bstr (operations other) value.identity_key) second.stage.after
    2#usize 34#usize (fieldBytes value.identity_key)
  ephemeral : Stage (@transport.serialize_bstr (operations other) value.ephemeral_key) identity.after
    36#usize 34#usize (fieldBytes value.ephemeral_key)
  kem : Stage (@transport.serialize_bstr (operations other) value.kem_cipher_text) ephemeral.after
    70#usize 1091#usize (fieldBytes value.kem_cipher_text)
  application : Stage (@transport.serialize_bstr (operations other) value.app_cipher_text) kem.after
    1161#usize (byteCount value.app_cipher_text) (fieldBytes value.app_cipher_text)
  key : Stage (@transport.serialize_uint (operations other) value.key_id) application.after
    (afterApplication value) (writtenCount value.key_id) (encodedBytes cbor_major_type_uint64 value.key_id)
  signature : Stage (@transport.serialize_bstr (operations other) value.signature) key.after
    (afterKey value) 3312#usize (fieldBytes value.signature)

theorem response_stages (other : OtherBranches) (value : transport.kexresponse) (out : Slice U8)
    (shape : ResponseShape value) (room : totalLength value ≤ out.length) :
    Nonempty (ResponseStages other value out) := by
  rcases shape with ⟨identityLength, ephemeralLength, kemLength, signatureLength⟩
  have full : 4473 + applicationLength value + keyLength value + 1 ≤ out.length := room
  have expanded := full
  unfold applicationLength keyLength at expanded
  obtain ⟨appCount, appOffset, keyOffset, bodyOffset, outputOffset⟩ := offsets value out room
  obtain ⟨first⟩ := source_uint_stage other out 0#usize 2#u64 (by
    change (0#usize).val + 1 ≤ out.length
    scalar_tac)
  have firstLength : first.stage.after.length = out.length := first.stage.sameLength
  obtain ⟨second⟩ := source_uint_stage other first.stage.after 1#usize 1#u64 (by
    rw [firstLength]
    change (1#usize).val + 1 ≤ out.length
    scalar_tac)
  have secondLength : second.stage.after.length = out.length := second.stage.sameLength.trans firstLength
  have header0 : (writtenCount (UScalar.cast .U64 value.identity_key.len)).val = 2 := by
    have cast := usize_cast value.identity_key.len
    have len : value.identity_key.len.val = 32 := by rw [Slice.len_val]; exact identityLength
    simp only [writtenCount, cast, len]
    rfl
  have count0 : byteCount value.identity_key = 34#usize := by
    apply constant_field value.identity_key 32#usize 2#usize 34#usize
    · simpa only [show (32#usize).val = 32 by scalar_tac] using identityLength
    · simp only [writtenCount, usize_cast, show (32#usize).val = 32 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨identity⟩ := bytes_stage other second.stage.after value.identity_key 2#usize (by
    rw [secondLength, header0, identityLength]
    scalar_tac)
  rw [count0] at identity
  have identitySame : identity.after.length = out.length := identity.sameLength.trans secondLength
  have header1 : (writtenCount (UScalar.cast .U64 value.ephemeral_key.len)).val = 2 := by
    have cast := usize_cast value.ephemeral_key.len
    have len : value.ephemeral_key.len.val = 32 := by rw [Slice.len_val]; exact ephemeralLength
    simp only [writtenCount, cast, len]
    rfl
  have count1 : byteCount value.ephemeral_key = 34#usize := by
    apply constant_field value.ephemeral_key 32#usize 2#usize 34#usize
    · simpa only [show (32#usize).val = 32 by scalar_tac] using ephemeralLength
    · simp only [writtenCount, usize_cast, show (32#usize).val = 32 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨ephemeral⟩ := bytes_stage other identity.after value.ephemeral_key 36#usize (by
    rw [identitySame, header1, ephemeralLength]
    scalar_tac)
  rw [count1] at ephemeral
  have ephemeralSame : ephemeral.after.length = out.length := ephemeral.sameLength.trans identitySame
  have header2 : (writtenCount (UScalar.cast .U64 value.kem_cipher_text.len)).val = 3 := by
    have cast := usize_cast value.kem_cipher_text.len
    have len : value.kem_cipher_text.len.val = 1088 := by rw [Slice.len_val]; exact kemLength
    simp only [writtenCount, cast, len]
    rfl
  have count2 : byteCount value.kem_cipher_text = 1091#usize := by
    apply constant_field value.kem_cipher_text 1088#usize 3#usize 1091#usize
    · simpa only [show (1088#usize).val = 1088 by scalar_tac] using kemLength
    · simp only [writtenCount, usize_cast, show (1088#usize).val = 1088 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨kem⟩ := bytes_stage other ephemeral.after value.kem_cipher_text 70#usize (by
    rw [ephemeralSame, header2, kemLength]
    scalar_tac)
  rw [count2] at kem
  have kemSame : kem.after.length = out.length := kem.sameLength.trans ephemeralSame
  obtain ⟨application⟩ := bytes_stage other kem.after value.app_cipher_text 1161#usize (by
    rw [kemSame]
    have constant : (1161#usize).val = 1161 := by scalar_tac
    rw [constant]
    omega)
  have applicationSame : application.after.length = out.length := application.sameLength.trans kemSame
  obtain ⟨key⟩ := uint_stage other application.after (afterApplication value) value.key_id (by
    rw [applicationSame, appOffset]
    change 1161 + applicationLength value + keyLength value ≤ out.length
    omega)
  have keySame : key.after.length = out.length := key.sameLength.trans applicationSame
  have headerSignature : (writtenCount (UScalar.cast .U64 value.signature.len)).val = 3 := by
    have cast := usize_cast value.signature.len
    have len : value.signature.len.val = 3309 := by rw [Slice.len_val]; exact signatureLength
    simp only [writtenCount, cast, len]
    rfl
  have countSignature : byteCount value.signature = 3312#usize := by
    apply constant_field value.signature 3309#usize 3#usize 3312#usize
    · simpa only [show (3309#usize).val = 3309 by scalar_tac] using signatureLength
    · simp only [writtenCount, usize_cast, show (3309#usize).val = 3309 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨signature⟩ := bytes_stage other key.after value.signature (afterKey value) (by
    rw [keySame, keyOffset, headerSignature, signatureLength]
    omega)
  rw [countSignature] at signature
  exact ⟨⟨first, second, identity, ephemeral, kem, application, key, signature⟩⟩

theorem encoded_one : encodedBytes cbor_major_type_uint64 1#u64 = [1#u8] := by
  have cast : UScalar.cast .U8 1#u64 = 1#u8 := by
    apply UScalar.eq_of_val_eq
    rw [cast_value .U8 1#u64 (by scalar_tac)]
    rfl
  simp only [encodedBytes, show (1#u64).val < 24 by scalar_tac, ↓reduceIte,
    cast, cbor_major_type_uint64]
  rfl

theorem stages_framed (other : OtherBranches) (value : transport.kexresponse) (out : Slice U8)
    (stages : ResponseStages other value out) (shape : ResponseShape value)
    (room : totalLength value ≤ out.length) :
    stages.signature.after.val = payload value ++ out.val.drop (bodyLength value) ∧
      (payload value).length = bodyLength value ∧ stages.signature.after.length = out.length := by
  rcases shape with ⟨identityLength, ephemeralLength, kemLength, signatureLength⟩
  obtain ⟨appCount, appOffset, keyOffset, bodyOffset, outputOffset⟩ := offsets value out room
  have val0 : (0#usize).val = 0 := by scalar_tac
  have val1 : (1#usize).val = 1 := by scalar_tac
  have val2 : (2#usize).val = 2 := by scalar_tac
  have val34 : (34#usize).val = 34 := by scalar_tac
  have val36 : (36#usize).val = 36 := by scalar_tac
  have val70 : (70#usize).val = 70 := by scalar_tac
  have val1091 : (1091#usize).val = 1091 := by scalar_tac
  have val1161 : (1161#usize).val = 1161 := by scalar_tac
  have val3312 : (3312#usize).val = 3312 := by scalar_tac
  have bytes0 : (fieldBytes value.identity_key).length = 34 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, identityLength]
    rfl
  have bytes1 : (fieldBytes value.ephemeral_key).length = 34 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, ephemeralLength]
    rfl
  have bytes2 : (fieldBytes value.kem_cipher_text).length = 1091 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, kemLength]
    rfl
  have bytes3 : (fieldBytes value.signature).length = 3312 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, signatureLength]
    rfl
  have appBytes : (fieldBytes value.app_cipher_text).length = applicationLength value := by
    simp only [fieldBytes, List.length_append, encoded_length]
    rfl
  have keyBytes : (encodedBytes cbor_major_type_uint64 value.key_id).length = keyLength value :=
    encoded_length _ _
  have first := stage_append stages.first.stage out.val [] (by simp) (by simp)
  have firstBytes : stages.first.stage.after.val = [2#u8] ++ out.val.drop 1 := by
    simpa only [encoded_two, show (writtenCount 2#u64).val = 1 from rfl,
      val0, List.nil_append, Nat.zero_add] using first
  have second := stage_append stages.second.stage out.val [2#u8] firstBytes (by simp only [List.length_cons, List.length_nil, val1])
  let part0 : List U8 := [2#u8, 1#u8]
  have prior0 : stages.second.stage.after.val = part0 ++ out.val.drop 2 := by
    change stages.second.stage.after.val = [2#u8, 1#u8] ++ out.val.drop 2
    simpa only [encoded_one, show (writtenCount 1#u64).val = 1 from rfl,
      val1, List.cons_append, List.nil_append] using second
  let part1 := part0 ++ fieldBytes value.identity_key
  have length0 : part0.length = (2#usize).val := by
    simp only [part0, List.length_cons,
      List.length_nil, val2]
  have next0 := stage_append stages.identity out.val part0 prior0 length0
  have prior1 : stages.identity.after.val = part1 ++ out.val.drop 36 := by
    simpa only [val2, val34] using next0
  let part2 := part1 ++ fieldBytes value.ephemeral_key
  have length1 : part1.length = (36#usize).val := by
    simp only [part0, part1, List.length_append, List.length_cons,
      List.length_nil, bytes0, val36]
  have next1 := stage_append stages.ephemeral out.val part1 prior1 length1
  have prior2 : stages.ephemeral.after.val = part2 ++ out.val.drop 70 := by
    simpa only [val36, val34] using next1
  let part3 := part2 ++ fieldBytes value.kem_cipher_text
  have length2 : part2.length = (70#usize).val := by
    simp only [part0, part1, part2, List.length_append, List.length_cons,
      List.length_nil, bytes0, bytes1, val70]
  have next2 := stage_append stages.kem out.val part2 prior2 length2
  have prior3 : stages.kem.after.val = part3 ++ out.val.drop 1161 := by
    simpa only [val70, val1091] using next2
  let part4 := part3 ++ fieldBytes value.app_cipher_text
  have length3 : part3.length = (1161#usize).val := by
    simp only [part3, part2, part1, part0, List.length_append, List.length_cons,
      List.length_nil, bytes0, bytes1, bytes2, val1161]
  have next3 := stage_append stages.application out.val part3 prior3 length3
  have prior4 : stages.application.after.val = part4 ++ out.val.drop (afterApplication value).val := by
    simpa only [val1161, appCount, appOffset] using next3
  let part5 := part4 ++ encodedBytes cbor_major_type_uint64 value.key_id
  have length4 : part4.length = (afterApplication value).val := by
    simp only [part4, List.length_append, length3, val1161, appBytes, appOffset]
  have next4 := stage_append stages.key out.val part4 prior4 length4
  have prior5 : stages.key.after.val = part5 ++ out.val.drop (afterKey value).val := by
    simpa only [appOffset, keyOffset, keyLength] using next4
  let part6 := part5 ++ fieldBytes value.signature
  have length5 : part5.length = (afterKey value).val := by
    simp only [part5, List.length_append, length4, appOffset, keyBytes, keyOffset]
  have next5 := stage_append stages.signature out.val part5 prior5 length5
  have endOffset : (afterKey value).val + (3312#usize).val = bodyLength value := by
    rw [keyOffset, val3312]
    unfold bodyLength
    omega
  have prior6 : stages.signature.after.val = part6 ++ out.val.drop (bodyLength value) := by
    simpa only [endOffset] using next5
  have total : part6.length = bodyLength value := by
    simp only [part6, List.length_append, length5, keyOffset, bytes3]
    unfold bodyLength
    omega
  have original : part6 = payload value := by
    simp only [part6, part5, part4, part3, part2, part1, part0, payload, List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rwa [original] at prior6
  · rwa [original] at total
  · exact stages.signature.sameLength.trans (stages.key.sameLength.trans
      (stages.application.sameLength.trans (stages.kem.sameLength.trans
        (stages.ephemeral.sameLength.trans (stages.identity.sameLength.trans
          (stages.second.stage.sameLength.trans stages.first.stage.sameLength))))))

theorem add_source (left right : Usize) :
    core.num.Usize.wrapping_add left right = .ok (Usize.wrapping_add left right) := rfl

attribute [local irreducible] cbordetver.cbor_det_serialize cbordetver.cbor_det_mk_int64
  transport.serialize_bstr transport.serialize_uint core.slice.Slice.split_at_mut
  transport.extraction_serialize_kexresponse_size_0 transport.extraction_serialize_kexresponse_size_1
  transport.extraction_serialize_kexresponse_size_2 transport.extraction_serialize_kexresponse_size_3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem controller_to_array (other : OtherBranches) (value : transport.kexresponse) (out : Slice U8)
    (stages : ResponseStages other value out) (shape : ResponseShape value)
    (room : totalLength value ≤ out.length) :
    @transport.extraction_serialize_kexresponse (operations other) value out =
      extraction_array_entry 8#u64 stages.signature.after (beforeArray value) := by
  let _ : RegistrationSerializerPrimitive.Operations := operations other
  rcases shape with ⟨identityLength, ephemeralLength, kemLength, signatureLength⟩
  obtain ⟨appCount, appOffset, keyOffset, bodyOffset, outputOffset⟩ := offsets value out room
  have bound0 : 0#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound1 : 1#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound2 : 2#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound3 : 3#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound4 : 4#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound5 : 5#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound6 : 6#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound7 : 7#u64 < 18446744073709551615#u64 := by scalar_tac
  have nonzero1 : ¬(1#usize = 0#usize) := by scalar_tac
  have nonzero34 : ¬(34#usize = 0#usize) := by scalar_tac
  have nonzero1091 : ¬(1091#usize = 0#usize) := by scalar_tac
  have nonzero3312 : ¬(3312#usize = 0#usize) := by scalar_tac
  have nonzeroApplication : ¬(byteCount value.app_cipher_text = 0#usize) := by
    have positive := header_positive (UScalar.cast .U64 value.app_cipher_text.len)
    unfold applicationLength at appCount
    scalar_tac
  have nonzeroKey : ¬(writtenCount value.key_id = 0#usize) := by
    have positive := header_positive value.key_id
    scalar_tac
  have low0 : u64_lte_sizet 32#u64 value.identity_key.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, identityLength]
    rfl
  have high0 : sizet_lte_u64 value.identity_key.len 32#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, identityLength]
    rfl
  have low1 : u64_lte_sizet 32#u64 value.ephemeral_key.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, ephemeralLength]
    rfl
  have high1 : sizet_lte_u64 value.ephemeral_key.len 32#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, ephemeralLength]
    rfl
  have low2 : u64_lte_sizet 1088#u64 value.kem_cipher_text.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, kemLength]
    rfl
  have high2 : sizet_lte_u64 value.kem_cipher_text.len 1088#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, kemLength]
    rfl
  have low3 : u64_lte_sizet 3309#u64 value.signature.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, signatureLength]
    rfl
  have high3 : sizet_lte_u64 value.signature.len 3309#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, signatureLength]
    rfl
  have split0 := stages.first.stage.splitSource
  have split1 := stages.second.stage.splitSource
  dsimp only [Stage.after] at split1
  have split2 := stages.identity.splitSource
  dsimp only [Stage.after] at split2
  have split3 := stages.ephemeral.splitSource
  dsimp only [Stage.after] at split3
  have split4 := stages.kem.splitSource
  dsimp only [Stage.after] at split4
  have split5 := stages.application.splitSource
  dsimp only [Stage.after] at split5
  have split6 := stages.key.splitSource
  dsimp only [Stage.after, afterApplication] at split6
  have split7 := stages.signature.splitSource
  dsimp only [Stage.after, afterApplication, afterKey] at split7
  unfold transport.extraction_serialize_kexresponse
  simp only [transport.kexresponse_left, index_singleton, bind_tc_ok, uncurry]
  simp only [bind_tc_ok, uncurry, index_singleton, update_singleton, index_mut_singleton, bound0, ↓reduceIte]
  rw [split0]
  simp only [bind_tc_ok, uncurry]
  rw [stages.first.factory]
  simp only [bind_tc_ok]
  rw [stages.first.actualSerialize]
  simp only [show writtenCount 2#u64 = 1#usize from rfl, bind_tc_ok]
  simp only [bind_tc_ok, uncurry, nonzero1, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 0#u64 1#u64 = .ok 1#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 0#usize 1#usize 1#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound1, ↓reduceIte]
  rw [split1]
  simp only [bind_tc_ok, uncurry]
  rw [stages.second.factory]
  simp only [bind_tc_ok]
  rw [stages.second.actualSerialize]
  simp only [show writtenCount 1#u64 = 1#usize from rfl, bind_tc_ok]
  simp only [bind_tc_ok, uncurry, nonzero1, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 1#u64 1#u64 = .ok 2#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 1#usize 1#usize 2#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound2, ↓reduceIte]
  rw [split2]
  simp only [bind_tc_ok, uncurry]
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  rw [low0, high0]
  simp only [bind_tc_ok, kexresponse_field_0]
  rw [stages.identity.runSource]
  simp only [bind_tc_ok, uncurry, nonzero34, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 2#u64 1#u64 = .ok 3#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 2#usize 34#usize 36#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound3, ↓reduceIte]
  rw [split3]
  simp only [bind_tc_ok, uncurry]
  rw [low1, high1]
  simp only [bind_tc_ok, kexresponse_field_1]
  rw [stages.ephemeral.runSource]
  simp only [bind_tc_ok, uncurry, nonzero34, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 3#u64 1#u64 = .ok 4#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 36#usize 34#usize 70#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound4, ↓reduceIte]
  rw [split4]
  simp only [bind_tc_ok, uncurry]
  rw [low2, high2]
  simp only [bind_tc_ok, kexresponse_field_2]
  rw [stages.kem.runSource]
  simp only [bind_tc_ok, uncurry, nonzero1091, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 4#u64 1#u64 = .ok 5#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 70#usize 1091#usize 1161#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound5, ↓reduceIte]
  rw [split5]
  simp only [bind_tc_ok, uncurry]
  rw [stages.application.runSource]
  simp only [bind_tc_ok, uncurry, nonzeroApplication, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 5#u64 1#u64 = .ok 6#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_source]
  simp only [bind_tc_ok, bound6, ↓reduceIte]
  rw [split6]
  simp only [bind_tc_ok, uncurry]
  rw [stages.key.runSource]
  simp only [bind_tc_ok, uncurry, nonzeroKey, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 6#u64 1#u64 = .ok 7#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_source]
  simp only [bind_tc_ok, bound7, ↓reduceIte]
  rw [split7]
  simp only [bind_tc_ok, uncurry]
  rw [low3, high3]
  simp only [bind_tc_ok, kexresponse_field_3]
  rw [stages.signature.runSource]
  simp only [bind_tc_ok, uncurry, nonzero3312, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 7#u64 1#u64 = .ok 8#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_source]
  simp only [bind_tc_ok]
  rfl

theorem controller_bytes (other : OtherBranches) (value : transport.kexresponse) (out : Slice U8)
    (shape : ResponseShape value) (room : totalLength value ≤ out.length) :
    ∃ after, @transport.extraction_serialize_kexresponse (operations other) value out = .ok (finalCursor value, after) ∧
      after.length = out.length ∧
      after.val = (136#u8 :: payload value) ++ out.val.drop (totalLength value) ∧
      (finalCursor value).val = totalLength value := by
  obtain ⟨stages⟩ := response_stages other value out shape room
  obtain ⟨framed, bytesLength, sameLength⟩ := stages_framed other value out stages shape room
  obtain ⟨appCount, appOffset, keyOffset, bodyOffset, outputOffset⟩ := offsets value out room
  have available : (beforeArray value).val < stages.signature.after.length := by
    rw [bodyOffset, sameLength]
    have fitting : bodyLength value + 1 ≤ out.length := room
    omega
  obtain ⟨after, actual, afterLength, afterBytes⟩ :=
    RegistrationArraySourceBytes.entry8 stages.signature.after (beforeArray value) available
  have cursor : RegistrationArraySerialize.cursor (beforeArray value) = finalCursor value := rfl
  refine ⟨after, ?_, afterLength.trans sameLength, ?_, outputOffset⟩
  · rw [controller_to_array other value out stages shape room, actual, cursor]
  · have head : stages.signature.after.val.take (bodyLength value) = payload value := by
      rw [framed]
      exact List.take_left' bytesLength
    have tail : stages.signature.after.val.drop (bodyLength value + 1) = out.val.drop (totalLength value) := by
      rw [framed, List.drop_append, bytesLength, Nat.add_sub_cancel_left]
      have empty : (payload value).drop (bodyLength value + 1) = [] := by
        rw [← List.drop_drop (i := 1) (j := bodyLength value), ← bytesLength, List.drop_length]
        exact List.drop_nil
      rw [empty, List.nil_append, List.drop_drop]
      rfl
    simpa only [bodyOffset, head, tail] using afterBytes

theorem argument_width (value : U64) :
    (writtenCount value).val = BeaconcryptCore.Computational.CborSizing.argumentLen value.val := by
  unfold writtenCount BeaconcryptCore.Computational.CborSizing.argumentLen
  split_ifs <;> scalar_tac

theorem total_sizing (value : transport.kexresponse) :
    totalLength value = BeaconcryptCore.Computational.CborSizing.responseLen
      value.app_cipher_text.length value.key_id.val := by
  unfold totalLength bodyLength applicationLength keyLength
  rw [argument_width, argument_width, usize_cast, Slice.len_val]
  change 4473 + (BeaconcryptCore.Computational.CborSizing.argumentLen value.app_cipher_text.length +
    value.app_cipher_text.length) + BeaconcryptCore.Computational.CborSizing.argumentLen value.key_id.val + 1 =
    1162 + (BeaconcryptCore.Computational.CborSizing.argumentLen value.app_cipher_text.length +
    value.app_cipher_text.length) + BeaconcryptCore.Computational.CborSizing.argumentLen value.key_id.val + 3312
  omega

theorem source_capacity (value : transport.kexresponse) (shape : ResponseShape value) :
    ∃ reply, beaconcrypt_core.transport.encoded_response_len
        (Array.make 5#usize [value.identity_key.len, value.ephemeral_key.len, value.kem_cipher_text.len,
          value.app_cipher_text.len, value.signature.len]) value.key_id = .ok reply ∧
      BeaconcryptCore.Refinement.Transport.absLength reply =
        BeaconcryptCore.Refinement.Transport.messageCap (totalLength value) := by
  rcases shape with ⟨identityLength, ephemeralLength, kemLength, signatureLength⟩
  have length0 : value.identity_key.len = 32#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, identityLength]
    scalar_tac
  have length1 : value.ephemeral_key.len = 32#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, ephemeralLength]
    scalar_tac
  have length2 : value.kem_cipher_text.len = 1088#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, kemLength]
    scalar_tac
  have length3 : value.signature.len = 3309#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, signatureLength]
    scalar_tac
  obtain ⟨reply, actual, represented⟩ :=
    BeaconcryptCore.Computational.TransportSizingBridge.encoded_current_response_len_exact value.app_cipher_text.len value.key_id
  refine ⟨reply, ?_, ?_⟩
  · simpa only [length0, length1, length2, length3, beaconcrypt_core.pqxdh.SIGN_PUBLIC_KEY_SIZE,
      beaconcrypt_core.pqxdh.X25519_PUBLIC_KEY_SIZE, beaconcrypt_core.pqxdh.MLKEM768_CIPHERTEXT_SIZE,
      beaconcrypt_core.authentication.MLDSA_SIGNATURE_LEN] using actual
  · rwa [Slice.len_val, ← total_sizing value] at represented

theorem public_bytes (other : OtherBranches) (value : transport.kexresponse) (out : Slice U8)
    (shape : ResponseShape value) (room : totalLength value ≤ out.length)
    (admitted : totalLength value ≤ BeaconcryptCore.Computational.CborSizing.maxMessageSize) :
    ∃ after, @extraction_encode_response (operations other) value out = .ok (finalCursor value, after) ∧
      after.length = out.length ∧
      after.val = (136#u8 :: payload value) ++ out.val.drop (totalLength value) ∧
      (finalCursor value).val = totalLength value := by
  obtain ⟨after, actual, sameLength, bytes, cursor⟩ := controller_bytes other value out shape room
  obtain ⟨reply, capacity, represented⟩ := source_capacity value shape
  refine ⟨after, ?_, sameLength, bytes, cursor⟩
  unfold extraction_encode_response
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  rw [capacity]
  simp only [bind_tc_ok]
  change totalLength value ≤ 33554432 at admitted
  rw [BeaconcryptCore.Refinement.Transport.messageCap, ite_eq_left admitted] at represented
  cases reply with
  | none => simp only [BeaconcryptCore.Refinement.Transport.absLength, reduceCtorEq] at represented
  | some capacity =>
    simp only [core.option.Option.is_none]
    exact actual

theorem public_rejected (other : OtherBranches) (value : transport.kexresponse) (out : Slice U8)
    (shape : ResponseShape value)
    (rejected : BeaconcryptCore.Computational.CborSizing.maxMessageSize < totalLength value) :
    @extraction_encode_response (operations other) value out = .ok (0#usize, out) := by
  obtain ⟨reply, capacity, represented⟩ := source_capacity value shape
  unfold extraction_encode_response
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  rw [capacity]
  simp only [bind_tc_ok]
  have inadmissible : ¬totalLength value ≤ 33554432 := by
    change 33554432 < totalLength value at rejected
    omega
  rw [BeaconcryptCore.Refinement.Transport.messageCap, ite_eq_right inadmissible] at represented
  cases reply with
  | none => simp only [core.option.Option.is_none]; rfl
  | some capacity => simp only [BeaconcryptCore.Refinement.Transport.absLength, reduceCtorEq] at represented

theorem public_success_admitted (other : OtherBranches) (value : transport.kexresponse) (out after : Slice U8)
    (shape : ResponseShape value) (cursor : Usize)
    (actual : @extraction_encode_response (operations other) value out = .ok (cursor, after))
    (positive : cursor ≠ 0#usize) :
    totalLength value ≤ BeaconcryptCore.Computational.CborSizing.maxMessageSize := by
  by_contra outside
  have rejected := public_rejected other value out shape (Nat.lt_of_not_ge outside)
  have equal : (cursor, after) = (0#usize, out) := RustM.ok.inj (actual.symm.trans rejected)
  exact positive (congrArg Prod.fst equal)

end BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.add_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.add_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.offsets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.offsets

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.response_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.response_stages

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.encoded_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.encoded_one

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.stages_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.stages_framed

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.add_source' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.add_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.controller_to_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.controller_to_array

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.controller_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.controller_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.argument_width' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.argument_width

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.total_sizing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.total_sizing

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.source_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.source_capacity

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.public_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.public_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.public_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.public_rejected

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.public_success_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes.public_success_admitted
