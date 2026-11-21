-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSerializerStages
import BeaconcryptCore.Computational.TransportSizingBridge
import BeaconcryptCore.Refinement.RegistrationArraySourceBytesSix
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The original public Init encoder composes actual complete-size admission, all six field actions, singleton counters, mutable slice writebacks and count-six array rotation. For the four current schema widths and every fitting output slice it returns 1490, preserves slice length and writes every original field including every attached Ed25519 signature with an untouched suffix. Unsupported branch interpretations remain arbitrary; no codec-law premise is introduced. Public decoding and native-instance composition are separate. -/
namespace BeaconcryptCore.Refinement.RegistrationSerializerInitBytes
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical RegistrationSerializerFields
open RegistrationSerializerReachableSource RegistrationSerializerStages

def InitShape (value : transport.initkex) : Prop :=
  value.identity_key.length = 33 ∧ value.pre_key.length = 98 ∧
  value.one_time_key.length = 98 ∧ value.pq_key.length = 1249

def fieldBytes (input : Slice U8) : List U8 :=
  encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 input.len) ++ input.val

def payload (value : transport.initkex) : List U8 :=
  [3#u8, 0#u8] ++ fieldBytes value.identity_key ++ fieldBytes value.pre_key ++
    fieldBytes value.one_time_key ++ fieldBytes value.pq_key

theorem constant_field (input : Slice U8) (length expectedHeader expectedTotal : Usize)
    (lengthEq : input.length = length.val)
    (headerEq : writtenCount (UScalar.cast .U64 length) = expectedHeader)
    (totalEq : length.val + expectedHeader.val = expectedTotal.val) :
    byteCount input = expectedTotal := by
  have len : input.len = length := UScalar.eq_of_val_eq (by rw [Slice.len_val]; exact lengthEq)
  unfold byteCount
  rw [len, headerEq]
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq, Nat.add_comm, totalEq, UScalar.size_def,
    Nat.mod_eq_of_lt expectedTotal.hBounds]

theorem stage_append {work : Work} {before : Slice U8} {offset count : Usize} {body : List U8}
    (stage : Stage work before offset count body) (origin headBytes : List U8)
    (prior : before.val = headBytes ++ origin.drop offset.val)
    (prefixLength : headBytes.length = offset.val) :
    stage.after.val = (headBytes ++ body) ++ origin.drop (offset.val + count.val) := by
  have head : before.val.take offset.val = headBytes := by
    rw [prior]
    exact List.take_left' prefixLength
  have tail : before.val.drop (offset.val + count.val) = origin.drop (offset.val + count.val) := by
    rw [prior, List.drop_append, prefixLength, Nat.add_sub_cancel_left]
    have empty : headBytes.drop (offset.val + count.val) = [] := by
      rw [← List.drop_drop (i := count.val) (j := offset.val), ← prefixLength, List.drop_length]
      exact List.drop_nil
    rw [empty, List.nil_append, List.drop_drop]
  rw [Stage.after, stage.bytes, head, tail]

structure UIntStage (other : OtherBranches) (before : Slice U8) (offset : Usize) (value : U64) where
  raw : cbor_raw
  stage : Stage (@transport.serialize_uint (operations other) value) before offset (writtenCount value)
    (encodedBytes cbor_major_type_uint64 value)
  factory : cbordetver.cbor_det_mk_int64 .UInt64 value = .ok raw
  actualSerialize : @cbordetver.cbor_det_serialize (operations other) raw stage.tail =
    .ok (.Some (writtenCount value), stage.changed)

theorem source_uint_stage (other : OtherBranches) (before : Slice U8) (offset : Usize) (value : U64)
    (room : offset.val + (writtenCount value).val ≤ before.length) :
    Nonempty (UIntStage other before offset value) := by
  obtain ⟨size, factory⟩ := RegistrationConstructorGuards.mk_uint value
  obtain ⟨front, tail, back, splitSource, frontLength, tailLength, frontBytes, tailBytes, backLaw⟩ :=
    RegistrationByteCopy.split_mut_success before offset (by omega)
  obtain ⟨changed, actual, changedLength, changedBytes⟩ :=
    uint_serialize_raw other tail value _ factory (by omega)
  have returned := backLaw front changed frontLength (by rw [changedLength]; exact tailLength)
  have publicRun : @transport.serialize_uint (operations other) value tail = .ok (writtenCount value, changed) := by
    unfold transport.serialize_uint
    simp only [transport.evercddl_uint_left, bind_tc_ok]
    rw [factory]
    simp only [bind_tc_ok]
    rw [actual]
    rfl
  have finalBytes : (back (front, changed)).val =
      before.val.take offset.val ++ encodedBytes cbor_major_type_uint64 value ++
        before.val.drop (offset.val + (writtenCount value).val) := by
    rw [returned.1, frontBytes, changedBytes, tailBytes, List.drop_drop]
    simp only [List.append_assoc]
  exact ⟨⟨_, ⟨front, tail, changed, back, splitSource, publicRun, returned.2, finalBytes⟩, factory, actual⟩⟩

structure InitStages (other : OtherBranches) (value : transport.initkex) (out : Slice U8) where
  first : UIntStage other out 0#usize 3#u64
  second : UIntStage other first.stage.after 1#usize 0#u64
  field0 : Stage (@transport.serialize_bstr (operations other) value.identity_key) second.stage.after
    2#usize 35#usize (fieldBytes value.identity_key)
  field1 : Stage (@transport.serialize_bstr (operations other) value.pre_key) field0.after
    37#usize 100#usize (fieldBytes value.pre_key)
  field2 : Stage (@transport.serialize_bstr (operations other) value.one_time_key) field1.after
    137#usize 100#usize (fieldBytes value.one_time_key)
  field3 : Stage (@transport.serialize_bstr (operations other) value.pq_key) field2.after
    237#usize 1252#usize (fieldBytes value.pq_key)

theorem init_stages (other : OtherBranches) (value : transport.initkex) (out : Slice U8)
    (shape : InitShape value) (room : 1490 ≤ out.length) :
    Nonempty (InitStages other value out) := by
  rcases shape with ⟨identityLength, preLength, oneLength, pqLength⟩
  obtain ⟨first⟩ := source_uint_stage other out 0#usize 3#u64 (by
    change (0#usize).val + 1 ≤ out.length
    scalar_tac)
  have firstLength : first.stage.after.length = out.length := first.stage.sameLength
  obtain ⟨second⟩ := source_uint_stage other first.stage.after 1#usize 0#u64 (by
    rw [firstLength]
    change (1#usize).val + 1 ≤ out.length
    scalar_tac)
  have secondLength : second.stage.after.length = out.length := second.stage.sameLength.trans firstLength
  have header0 : (writtenCount (UScalar.cast .U64 value.identity_key.len)).val = 2 := by
    have cast := usize_cast value.identity_key.len
    have len : value.identity_key.len.val = 33 := by rw [Slice.len_val]; exact identityLength
    simp only [writtenCount, cast, len]
    rfl
  have count0 : byteCount value.identity_key = 35#usize := by
    apply constant_field value.identity_key 33#usize 2#usize 35#usize
    · simpa only [show (33#usize).val = 33 by scalar_tac] using identityLength
    · simp only [writtenCount, usize_cast, show (33#usize).val = 33 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨field0⟩ := bytes_stage other second.stage.after value.identity_key 2#usize (by
    rw [secondLength, header0, identityLength]
    scalar_tac)
  rw [count0] at field0
  have field0Length : field0.after.length = out.length := field0.sameLength.trans secondLength
  have header1 : (writtenCount (UScalar.cast .U64 value.pre_key.len)).val = 2 := by
    have cast := usize_cast value.pre_key.len
    have len : value.pre_key.len.val = 98 := by rw [Slice.len_val]; exact preLength
    simp only [writtenCount, cast, len]
    rfl
  have count1 : byteCount value.pre_key = 100#usize := by
    apply constant_field value.pre_key 98#usize 2#usize 100#usize
    · simpa only [show (98#usize).val = 98 by scalar_tac] using preLength
    · simp only [writtenCount, usize_cast, show (98#usize).val = 98 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨field1⟩ := bytes_stage other field0.after value.pre_key 37#usize (by
    rw [field0Length, header1, preLength]
    scalar_tac)
  rw [count1] at field1
  have field1Length : field1.after.length = out.length := field1.sameLength.trans field0Length
  have header2 : (writtenCount (UScalar.cast .U64 value.one_time_key.len)).val = 2 := by
    have cast := usize_cast value.one_time_key.len
    have len : value.one_time_key.len.val = 98 := by rw [Slice.len_val]; exact oneLength
    simp only [writtenCount, cast, len]
    rfl
  have count2 : byteCount value.one_time_key = 100#usize := by
    apply constant_field value.one_time_key 98#usize 2#usize 100#usize
    · simpa only [show (98#usize).val = 98 by scalar_tac] using oneLength
    · simp only [writtenCount, usize_cast, show (98#usize).val = 98 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨field2⟩ := bytes_stage other field1.after value.one_time_key 137#usize (by
    rw [field1Length, header2, oneLength]
    scalar_tac)
  rw [count2] at field2
  have field2Length : field2.after.length = out.length := field2.sameLength.trans field1Length
  have header3 : (writtenCount (UScalar.cast .U64 value.pq_key.len)).val = 3 := by
    have cast := usize_cast value.pq_key.len
    have len : value.pq_key.len.val = 1249 := by rw [Slice.len_val]; exact pqLength
    simp only [writtenCount, cast, len]
    rfl
  have count3 : byteCount value.pq_key = 1252#usize := by
    apply constant_field value.pq_key 1249#usize 3#usize 1252#usize
    · simpa only [show (1249#usize).val = 1249 by scalar_tac] using pqLength
    · simp only [writtenCount, usize_cast, show (1249#usize).val = 1249 by scalar_tac]
      rfl
    · scalar_tac
  obtain ⟨field3⟩ := bytes_stage other field2.after value.pq_key 237#usize (by
    rw [field2Length, header3, pqLength]
    scalar_tac)
  rw [count3] at field3
  have field3Length : field3.after.length = out.length := field3.sameLength.trans field2Length
  exact ⟨⟨first, second, field0, field1, field2, field3⟩⟩

theorem encoded_three : encodedBytes cbor_major_type_uint64 3#u64 = [3#u8] := by
  have cast : UScalar.cast .U8 3#u64 = 3#u8 := by
    apply UScalar.eq_of_val_eq
    rw [cast_value .U8 3#u64 (by scalar_tac)]
    rfl
  simp only [encodedBytes, show (3#u64).val < 24 by scalar_tac, ↓reduceIte,
    cast, cbor_major_type_uint64]
  rfl

theorem encoded_zero : encodedBytes cbor_major_type_uint64 0#u64 = [0#u8] := by
  have cast : UScalar.cast .U8 0#u64 = 0#u8 := by
    apply UScalar.eq_of_val_eq
    rw [cast_value .U8 0#u64 (by scalar_tac)]
    rfl
  simp only [encodedBytes, show (0#u64).val < 24 by scalar_tac, ↓reduceIte,
    cast, cbor_major_type_uint64]
  rfl

theorem stages_framed (other : OtherBranches) (value : transport.initkex) (out : Slice U8)
    (stages : InitStages other value out) (shape : InitShape value) :
    stages.field3.after.val = payload value ++ out.val.drop 1489 ∧
      (payload value).length = 1489 ∧ stages.field3.after.length = out.length := by
  rcases shape with ⟨identityLength, preLength, oneLength, pqLength⟩
  have val0 : (0#usize).val = 0 := by scalar_tac
  have val1 : (1#usize).val = 1 := by scalar_tac
  have val2 : (2#usize).val = 2 := by scalar_tac
  have val35 : (35#usize).val = 35 := by scalar_tac
  have val37 : (37#usize).val = 37 := by scalar_tac
  have val100 : (100#usize).val = 100 := by scalar_tac
  have val137 : (137#usize).val = 137 := by scalar_tac
  have val237 : (237#usize).val = 237 := by scalar_tac
  have val1252 : (1252#usize).val = 1252 := by scalar_tac
  have val1489 : (1489#usize).val = 1489 := by scalar_tac
  have bytes0 : (fieldBytes value.identity_key).length = 35 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, identityLength]
    rfl
  have bytes1 : (fieldBytes value.pre_key).length = 100 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, preLength]
    rfl
  have bytes2 : (fieldBytes value.one_time_key).length = 100 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, oneLength]
    rfl
  have bytes3 : (fieldBytes value.pq_key).length = 1252 := by
    simp only [fieldBytes, List.length_append, encoded_length, writtenCount, usize_cast, Slice.len_val, pqLength]
    rfl
  have first := stage_append stages.first.stage out.val [] (by simp) (by simp)
  have firstBytes : stages.first.stage.after.val = [3#u8] ++ out.val.drop 1 := by
    simpa only [encoded_three,
      show (writtenCount 3#u64).val = 1 from rfl, val0, List.nil_append, Nat.zero_add] using first
  have second := stage_append stages.second.stage out.val [3#u8] firstBytes (by simp only [List.length_cons, List.length_nil, val1])
  let part0 : List U8 := [3#u8, 0#u8]
  have prior0 : stages.second.stage.after.val = part0 ++ out.val.drop 2 := by
    change stages.second.stage.after.val = [3#u8, 0#u8] ++ out.val.drop 2
    simpa only [encoded_zero,
      show (writtenCount 0#u64).val = 1 from rfl, val1, List.cons_append, List.nil_append] using second
  let part1 := part0 ++ fieldBytes value.identity_key
  have length0 : part0.length = (2#usize).val := by
    simp only [part0,
      List.length_cons, List.length_nil, val2]
  have next0 := stage_append stages.field0 out.val part0 prior0 length0
  have prior1 : stages.field0.after.val = part1 ++ out.val.drop 37 := by
    simpa only [val2, val35] using next0
  let part2 := part1 ++ fieldBytes value.pre_key
  have length1 : part1.length = (37#usize).val := by
    simp only [part0, part1, List.length_append,
      List.length_cons, List.length_nil, bytes0, val37]
  have next1 := stage_append stages.field1 out.val part1 prior1 length1
  have prior2 : stages.field1.after.val = part2 ++ out.val.drop 137 := by
    simpa only [val37, val100] using next1
  let part3 := part2 ++ fieldBytes value.one_time_key
  have length2 : part2.length = (137#usize).val := by
    simp only [part0, part1, part2, List.length_append,
      List.length_cons, List.length_nil, bytes0, bytes1, val137]
  have next2 := stage_append stages.field2 out.val part2 prior2 length2
  have prior3 : stages.field2.after.val = part3 ++ out.val.drop 237 := by
    simpa only [val137, val100] using next2
  let part4 := part3 ++ fieldBytes value.pq_key
  have length3 : part3.length = (237#usize).val := by
    simp only [part0, part1, part2, part3, List.length_append,
      List.length_cons, List.length_nil, bytes0, bytes1, bytes2, val237]
  have next3 := stage_append stages.field3 out.val part3 prior3 length3
  have prior4 : stages.field3.after.val = part4 ++ out.val.drop 1489 := by
    simpa only [val237, val1252] using next3
  have total : part4.length = 1489 := by
    simp only [part4, part3, part2, part1, part0, List.length_append,
      List.length_cons, List.length_nil, bytes0, bytes1, bytes2, bytes3]
  have original : part4 = payload value := by
    simp only [part4, part3, part2, part1, part0, payload, List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rwa [original] at prior4
  · rwa [original] at total
  · exact stages.field3.sameLength.trans (stages.field2.sameLength.trans
      (stages.field1.sameLength.trans (stages.field0.sameLength.trans
        (stages.second.stage.sameLength.trans stages.first.stage.sameLength))))

theorem index_singleton {S : Type} (value : S) :
    Array.index_usize (Array.repeat 1#usize value) 0#usize = .ok value := rfl

theorem update_singleton {S : Type} (before after : S) :
    Array.update (Array.repeat 1#usize before) 0#usize after = .ok (Array.repeat 1#usize after) := rfl

-- Compose already-proved source leaf calls through their exact result equations.
attribute [local irreducible] cbordetver.cbor_det_serialize cbordetver.cbor_det_mk_int64
  transport.serialize_bstr core.slice.Slice.split_at_mut
  transport.extraction_serialize_initkex_size_0 transport.extraction_serialize_initkex_size_1
  transport.extraction_serialize_initkex_size_2 transport.extraction_serialize_initkex_size_3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem controller_to_array (other : OtherBranches) (value : transport.initkex) (out : Slice U8)
    (stages : InitStages other value out) (shape : InitShape value) :
    @transport.extraction_serialize_initkex (operations other) value out =
      extraction_array_entry 6#u64 stages.field3.after 1489#usize := by
  let _ : RegistrationSerializerPrimitive.Operations := operations other
  rcases shape with ⟨identityLength, preLength, oneLength, pqLength⟩
  have bound0 : 0#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound1 : 1#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound2 : 2#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound3 : 3#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound4 : 4#u64 < 18446744073709551615#u64 := by scalar_tac
  have bound5 : 5#u64 < 18446744073709551615#u64 := by scalar_tac
  have nonzero1 : ¬(1#usize = 0#usize) := by scalar_tac
  have nonzero35 : ¬(35#usize = 0#usize) := by scalar_tac
  have nonzero100 : ¬(100#usize = 0#usize) := by scalar_tac
  have nonzero1252 : ¬(1252#usize = 0#usize) := by scalar_tac
  have low0 : u64_lte_sizet 33#u64 value.identity_key.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, identityLength]
    rfl
  have high0 : sizet_lte_u64 value.identity_key.len 33#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, identityLength]
    rfl
  have low1 : u64_lte_sizet 98#u64 value.pre_key.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, preLength]
    rfl
  have high1 : sizet_lte_u64 value.pre_key.len 98#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, preLength]
    rfl
  have low2 : u64_lte_sizet 98#u64 value.one_time_key.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, oneLength]
    rfl
  have high2 : sizet_lte_u64 value.one_time_key.len 98#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, oneLength]
    rfl
  have low3 : u64_lte_sizet 1249#u64 value.pq_key.len = .ok true := by
    rw [u64_lte_usize]
    simp only [Slice.len_val, pqLength]
    rfl
  have high3 : sizet_lte_u64 value.pq_key.len 1249#u64 = .ok true := by
    rw [usize_lte_u64]
    simp only [Slice.len_val, pqLength]
    rfl
  have split0 := stages.first.stage.splitSource
  have split1 := stages.second.stage.splitSource
  dsimp only [Stage.after] at split1
  have split2 := stages.field0.splitSource
  dsimp only [Stage.after] at split2
  have split3 := stages.field1.splitSource
  dsimp only [Stage.after] at split3
  have split4 := stages.field2.splitSource
  dsimp only [Stage.after] at split4
  have split5 := stages.field3.splitSource
  dsimp only [Stage.after] at split5
  unfold transport.extraction_serialize_initkex
  simp only [transport.initkex_left, index_singleton, bind_tc_ok, uncurry]
  simp only [bind_tc_ok, uncurry, index_singleton, update_singleton, index_mut_singleton, bound0, ↓reduceIte]
  rw [split0]
  simp only [bind_tc_ok, uncurry]
  rw [stages.first.factory]
  simp only [bind_tc_ok]
  rw [stages.first.actualSerialize]
  simp only [show writtenCount 3#u64 = 1#usize from rfl, bind_tc_ok]
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
  simp only [show writtenCount 0#u64 = 1#usize from rfl, bind_tc_ok]
  simp only [bind_tc_ok, uncurry, nonzero1, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 1#u64 1#u64 = .ok 2#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 1#usize 1#usize 2#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound2, ↓reduceIte]
  rw [split2]
  simp only [bind_tc_ok, uncurry]
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  rw [low0, high0]
  simp only [bind_tc_ok, initkex_field_0]
  rw [stages.field0.runSource]
  simp only [bind_tc_ok, uncurry, nonzero35, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 2#u64 1#u64 = .ok 3#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 2#usize 35#usize 37#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound3, ↓reduceIte]
  rw [split3]
  simp only [bind_tc_ok, uncurry]

  rw [low1, high1]
  simp only [bind_tc_ok, initkex_field_1]
  rw [stages.field1.runSource]
  simp only [bind_tc_ok, uncurry, nonzero100, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 3#u64 1#u64 = .ok 4#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 37#usize 100#usize 137#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound4, ↓reduceIte]
  rw [split4]
  simp only [bind_tc_ok, uncurry]

  rw [low2, high2]
  simp only [bind_tc_ok, initkex_field_2]
  rw [stages.field2.runSource]
  simp only [bind_tc_ok, uncurry, nonzero100, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 4#u64 1#u64 = .ok 5#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 137#usize 100#usize 237#usize (by scalar_tac)]
  simp only [bind_tc_ok, bound5, ↓reduceIte]
  rw [split5]
  simp only [bind_tc_ok, uncurry]

  rw [low3, high3]
  simp only [bind_tc_ok, initkex_field_3]
  rw [stages.field3.runSource]
  simp only [bind_tc_ok, uncurry, nonzero1252, ↓reduceIte]
  rw [show core.num.U64.wrapping_add 5#u64 1#u64 = .ok 6#u64 from rfl]
  simp only [bind_tc_ok]
  rw [add_usize 237#usize 1252#usize 1489#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rfl

theorem controller_bytes (other : OtherBranches) (value : transport.initkex) (out : Slice U8)
    (shape : InitShape value) (room : 1490 ≤ out.length) :
    ∃ after, @transport.extraction_serialize_initkex (operations other) value out = .ok (1490#usize, after) ∧
      after.length = out.length ∧
      after.val = (134#u8 :: payload value) ++ out.val.drop 1490 := by
  obtain ⟨stages⟩ := init_stages other value out shape room
  obtain ⟨framed, bodyLength, sameLength⟩ := stages_framed other value out stages shape
  have offset : (1489#usize).val = 1489 := by scalar_tac
  have available : (1489#usize).val < stages.field3.after.length := by rw [offset, sameLength]; omega
  obtain ⟨after, actual, afterLength, afterBytes⟩ :=
    RegistrationArraySourceBytesSix.entry6 stages.field3.after 1489#usize available
  have cursor : RegistrationArraySerializeSix.cursor 1489#usize = 1490#usize := by
    apply UScalar.eq_of_val_eq
    rw [RegistrationArraySerializeSix.cursor_value stages.field3.after 1489#usize available]
    scalar_tac
  refine ⟨after, ?_, afterLength.trans sameLength, ?_⟩
  · rw [controller_to_array other value out stages shape, actual, cursor]
  · have head : stages.field3.after.val.take 1489 = payload value := by
      rw [framed]
      exact List.take_left' bodyLength
    have tail : stages.field3.after.val.drop 1490 = out.val.drop 1490 := by
      rw [framed, List.drop_append, bodyLength]
      have empty : (payload value).drop 1490 = [] := by
        rw [show 1490 = 1489 + 1 from rfl,
          ← List.drop_drop (i := 1) (j := 1489), ← bodyLength, List.drop_length]
        exact List.drop_nil
      rw [empty, List.nil_append, List.drop_drop]
    simpa only [offset, head, tail] using afterBytes

theorem public_bytes (other : OtherBranches) (value : transport.initkex) (out : Slice U8)
    (shape : InitShape value) (room : 1490 ≤ out.length) :
    ∃ after, @extraction_encode_init (operations other) value out = .ok (1490#usize, after) ∧
      after.length = out.length ∧
      after.val = (134#u8 :: payload value) ++ out.val.drop 1490 := by
  obtain ⟨after, actual, sameLength, bytes⟩ := controller_bytes other value out shape room
  rcases shape with ⟨identityLength, preLength, oneLength, pqLength⟩
  have length0 : value.identity_key.len = 33#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, identityLength]
    scalar_tac
  have length1 : value.pre_key.len = 98#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, preLength]
    scalar_tac
  have length2 : value.one_time_key.len = 98#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, oneLength]
    scalar_tac
  have length3 : value.pq_key.len = 1249#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, pqLength]
    scalar_tac
  obtain ⟨reply, sized, admitted⟩ :=
    BeaconcryptCore.Computational.TransportSizingBridge.encoded_current_init_len_exact
  refine ⟨after, ?_, sameLength, bytes⟩
  unfold extraction_encode_init
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok,
    length0, length1, length2, length3]
  rw [sized]
  simp only [bind_tc_ok]
  cases reply with
  | none => simp only [BeaconcryptCore.Refinement.Transport.absLength, reduceCtorEq] at admitted
  | some capacity =>
    simp only [core.option.Option.is_none]
    exact actual

end BeaconcryptCore.Refinement.RegistrationSerializerInitBytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.constant_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.constant_field

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.stage_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.stage_append

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.source_uint_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.source_uint_stage

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.init_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.init_stages

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.encoded_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.encoded_three

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.encoded_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.encoded_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.stages_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.stages_framed

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.index_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.index_singleton

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.update_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.update_singleton

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.controller_to_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.controller_to_array

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.controller_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.controller_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.public_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerInitBytes.public_bytes
