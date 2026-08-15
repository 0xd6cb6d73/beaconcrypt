/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_core.Commitment.Lemmas

open FStar.Mul
open Rust_primitives.Integers
open Rust_primitives.Arrays
open Beaconcrypt_core.Commitment

#set-options "--fuel 1 --ifuel 1 --z3rlimit 600"

/// The proof-visible integer encoder is exactly little endian.
let encode_u64_le_is_exact (value:u64)
  : Lemma
      (let bytes = encode_u64_le value in
       Seq.index bytes 0 == (Rust_primitives.cast (value <: u64) <: u8) /\
       Seq.index bytes 1 ==
         (Rust_primitives.cast (value >>! mk_i32 8 <: u64) <: u8) /\
       Seq.index bytes 2 ==
         (Rust_primitives.cast (value >>! mk_i32 16 <: u64) <: u8) /\
       Seq.index bytes 3 ==
         (Rust_primitives.cast (value >>! mk_i32 24 <: u64) <: u8) /\
       Seq.index bytes 4 ==
         (Rust_primitives.cast (value >>! mk_i32 32 <: u64) <: u8) /\
       Seq.index bytes 5 ==
         (Rust_primitives.cast (value >>! mk_i32 40 <: u64) <: u8) /\
       Seq.index bytes 6 ==
         (Rust_primitives.cast (value >>! mk_i32 48 <: u64) <: u8) /\
       Seq.index bytes 7 ==
         (Rust_primitives.cast (value >>! mk_i32 56 <: u64) <: u8))
  = ()

let encode_u64_le_has_le64_values (value:u64)
  : Lemma
      (let bytes = encode_u64_le value in
       v (Seq.index bytes 0) == v value % 256 /\
       v (Seq.index bytes 1) == (v value / pow2 8) % 256 /\
       v (Seq.index bytes 2) == (v value / pow2 16) % 256 /\
       v (Seq.index bytes 3) == (v value / pow2 24) % 256 /\
       v (Seq.index bytes 4) == (v value / pow2 32) % 256 /\
       v (Seq.index bytes 5) == (v value / pow2 40) % 256 /\
       v (Seq.index bytes 6) == (v value / pow2 48) % 256 /\
       v (Seq.index bytes 7) == (v value / pow2 56) % 256)
  = shift_right_lemma value (mk_i32 8);
    shift_right_lemma value (mk_i32 16);
    shift_right_lemma value (mk_i32 24);
    shift_right_lemma value (mk_i32 32);
    shift_right_lemma value (mk_i32 40);
    shift_right_lemma value (mk_i32 48);
    shift_right_lemma value (mk_i32 56)

/// Per-byte view of the monomorphized fixed-range update contract.
let update_at_range_byte_view
    (s:t_Slice u8)
    (range:Core_models.Ops.Range.t_Range usize)
    (replacement:t_Slice u8)
  : Lemma
      (requires
        v range.f_start >= 0 /\
        v range.f_start <= Seq.length s /\
        v range.f_end <= Seq.length s /\
        Seq.length replacement == v range.f_end - v range.f_start)
      (ensures
        (let out =
           Rust_primitives.Hax.Monomorphized_update_at.update_at_range
             s range replacement in
         forall (i:nat).
           (i < v range.f_start ==> Seq.index out i == Seq.index s i) /\
           (i >= v range.f_start /\ i < v range.f_end ==>
              Seq.index out i ==
                Seq.index replacement (i - v range.f_start)) /\
           (i >= v range.f_end /\ i < Seq.length out ==>
              Seq.index out i == Seq.index s i)))
  =
  let out = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    s range replacement in
  let byte_view (i:nat) : Lemma
      ((i < v range.f_start ==> Seq.index out i == Seq.index s i) /\
       (i >= v range.f_start /\ i < v range.f_end ==>
          Seq.index out i == Seq.index replacement (i - v range.f_start)) /\
       (i >= v range.f_end /\ i < Seq.length out ==>
          Seq.index out i == Seq.index s i))
    =
    if i < v range.f_start then
      (FStar.Seq.Base.lemma_index_slice out 0 (v range.f_start) i;
       FStar.Seq.Base.lemma_index_slice s 0 (v range.f_start) i)
    else if i < v range.f_end then
      FStar.Seq.Base.lemma_index_slice
        out (v range.f_start) (v range.f_end) (i - v range.f_start)
    else if i < Seq.length out then
      (FStar.Seq.Base.lemma_index_slice
         out (v range.f_end) (Seq.length out) (i - v range.f_end);
       FStar.Seq.Base.lemma_index_slice
         s (v range.f_end) (Seq.length s) (i - v range.f_end))
    else
      ()
  in
  FStar.Classical.forall_intro byte_view

let v_KEY_RANGE:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 0;
    Core_models.Ops.Range.f_end = mk_usize 32 }

let v_NONCE_RANGE:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 32;
    Core_models.Ops.Range.f_end = mk_usize 44 }

let v_AD_RANGE:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 44;
    Core_models.Ops.Range.f_end = mk_usize 197 }

let v_TAG_RANGE:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 197;
    Core_models.Ops.Range.f_end = mk_usize 213 }

let v_SEQUENCE_RANGE:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 213;
    Core_models.Ops.Range.f_end = mk_usize 221 }

let v_SENDER_ID_RANGE:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 221;
    Core_models.Ops.Range.f_end = mk_usize 229 }

/// A proof-only name for the fixed-range update expression extracted from `build_commitment_transcript`.
let commitment_transcript_bytes
    (key:t_Array u8 (mk_usize 32))
    (nonce:t_Array u8 (mk_usize 12))
    (associated_data:t_Array u8 (mk_usize 153))
    (tag:t_Array u8 (mk_usize 16))
    (sequence sender_id:u64)
  : t_Array u8 (mk_usize 229) =
  let sequence_bytes = encode_u64_le sequence in
  let sender_id_bytes = encode_u64_le sender_id in
  let b0 = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 229) in
  let b1 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b0 v_KEY_RANGE key in
  let b2 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b1 v_NONCE_RANGE nonce in
  let b3 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b2 v_AD_RANGE associated_data in
  let b4 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b3 v_TAG_RANGE tag in
  let b5 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b4 v_SEQUENCE_RANGE sequence_bytes in
  Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b5 v_SENDER_ID_RANGE sender_id_bytes

let production_commitment_transcript_uses_exact_bytes
    (key:t_Array u8 (mk_usize 32))
    (nonce:t_Array u8 (mk_usize 12))
    (associated_data:t_Array u8 (mk_usize 153))
    (tag:t_Array u8 (mk_usize 16))
    (sequence sender_id:u64)
  : Lemma
      ((build_commitment_transcript
          key nonce associated_data tag sequence sender_id).f_bytes ==
       commitment_transcript_bytes
         key nonce associated_data tag sequence sender_id)
  = ()

let commitment_transcript_byte_is_exact
    (key:t_Array u8 (mk_usize 32))
    (nonce:t_Array u8 (mk_usize 12))
    (associated_data:t_Array u8 (mk_usize 153))
    (tag:t_Array u8 (mk_usize 16))
    (sequence sender_id:u64)
    (i:nat { i < 229 })
  : Lemma
      (Seq.index
         (commitment_transcript_bytes
            key nonce associated_data tag sequence sender_id) i ==
       (if i < 32 then Seq.index key i
       else if i < 44 then Seq.index nonce (i - 32)
       else if i < 197 then Seq.index associated_data (i - 44)
       else if i < 213 then Seq.index tag (i - 197)
       else if i < 221 then Seq.index (encode_u64_le sequence) (i - 213)
       else Seq.index (encode_u64_le sender_id) (i - 221)))
  =
  let sequence_bytes = encode_u64_le sequence in
  let sender_id_bytes = encode_u64_le sender_id in
  let b0 = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 229) in
  let b1 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b0 v_KEY_RANGE key in
  let b2 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b1 v_NONCE_RANGE nonce in
  let b3 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b2 v_AD_RANGE associated_data in
  let b4 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b3 v_TAG_RANGE tag in
  let b5 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b4 v_SEQUENCE_RANGE sequence_bytes in
  update_at_range_byte_view b0 v_KEY_RANGE key;
  update_at_range_byte_view b1 v_NONCE_RANGE nonce;
  update_at_range_byte_view b2 v_AD_RANGE associated_data;
  update_at_range_byte_view b3 v_TAG_RANGE tag;
  update_at_range_byte_view b4 v_SEQUENCE_RANGE sequence_bytes;
  update_at_range_byte_view b5 v_SENDER_ID_RANGE sender_id_bytes

/// The extracted production helper preserves every field.
/// It places the fields in the exact order consumed by BLAKE2b.
let commitment_transcript_is_exact
    (key:t_Array u8 (mk_usize 32))
    (nonce:t_Array u8 (mk_usize 12))
    (associated_data:t_Array u8 (mk_usize 153))
    (tag:t_Array u8 (mk_usize 16))
    (sequence sender_id:u64)
  : Lemma
      (let bytes =
         (build_commitment_transcript
            key nonce associated_data tag sequence sender_id).f_bytes in
       forall (i:nat { i < 229 }).
         Seq.index bytes i ==
         (if i < 32 then Seq.index key i
         else if i < 44 then Seq.index nonce (i - 32)
         else if i < 197 then Seq.index associated_data (i - 44)
         else if i < 213 then Seq.index tag (i - 197)
         else if i < 221 then Seq.index (encode_u64_le sequence) (i - 213)
         else Seq.index (encode_u64_le sender_id) (i - 221)))
  = production_commitment_transcript_uses_exact_bytes
      key nonce associated_data tag sequence sender_id;
    FStar.Classical.forall_intro
      (commitment_transcript_byte_is_exact
         key nonce associated_data tag sequence sender_id)

/// Both integer fields in the extracted production transcript have their declared little-endian numeric values.
let commitment_transcript_integer_fields_are_le64
    (key:t_Array u8 (mk_usize 32))
    (nonce:t_Array u8 (mk_usize 12))
    (associated_data:t_Array u8 (mk_usize 153))
    (tag:t_Array u8 (mk_usize 16))
    (sequence sender_id:u64)
  : Lemma
      (let bytes =
         (build_commitment_transcript
            key nonce associated_data tag sequence sender_id).f_bytes in
       v (Seq.index bytes 213) == v sequence % 256 /\
       v (Seq.index bytes 214) == (v sequence / pow2 8) % 256 /\
       v (Seq.index bytes 215) == (v sequence / pow2 16) % 256 /\
       v (Seq.index bytes 216) == (v sequence / pow2 24) % 256 /\
       v (Seq.index bytes 217) == (v sequence / pow2 32) % 256 /\
       v (Seq.index bytes 218) == (v sequence / pow2 40) % 256 /\
       v (Seq.index bytes 219) == (v sequence / pow2 48) % 256 /\
       v (Seq.index bytes 220) == (v sequence / pow2 56) % 256 /\
       v (Seq.index bytes 221) == v sender_id % 256 /\
       v (Seq.index bytes 222) == (v sender_id / pow2 8) % 256 /\
       v (Seq.index bytes 223) == (v sender_id / pow2 16) % 256 /\
       v (Seq.index bytes 224) == (v sender_id / pow2 24) % 256 /\
       v (Seq.index bytes 225) == (v sender_id / pow2 32) % 256 /\
       v (Seq.index bytes 226) == (v sender_id / pow2 40) % 256 /\
       v (Seq.index bytes 227) == (v sender_id / pow2 48) % 256 /\
       v (Seq.index bytes 228) == (v sender_id / pow2 56) % 256)
  = commitment_transcript_is_exact
      key nonce associated_data tag sequence sender_id;
    encode_u64_le_has_le64_values sequence;
    encode_u64_le_has_le64_values sender_id

/// Interpret an eight-byte little-endian string as a natural number.
let decode_u64_le (bytes:t_Array u8 (mk_usize 8)) : nat =
  v (Seq.index bytes 0) +
  256 * v (Seq.index bytes 1) +
  65536 * v (Seq.index bytes 2) +
  16777216 * v (Seq.index bytes 3) +
  4294967296 * v (Seq.index bytes 4) +
  1099511627776 * v (Seq.index bytes 5) +
  281474976710656 * v (Seq.index bytes 6) +
  72057594037927936 * v (Seq.index bytes 7)

/// The extracted encoder has a left inverse over the full `u64` domain.
let decode_encode_u64_le (value:u64)
  : Lemma (decode_u64_le (encode_u64_le value) == v value)
  =
  let x = v value in
  encode_u64_le_has_le64_values value;
  pow2_values 8;
  pow2_values 16;
  pow2_values 24;
  pow2_values 32;
  pow2_values 40;
  pow2_values 48;
  pow2_values 56;
  pow2_values 64;
  FStar.Math.Lemmas.lemma_div_mod x 256;
  FStar.Math.Lemmas.lemma_div_mod (x / 256) 256;
  FStar.Math.Lemmas.lemma_div_mod (x / 65536) 256;
  FStar.Math.Lemmas.lemma_div_mod (x / 16777216) 256;
  FStar.Math.Lemmas.lemma_div_mod (x / 4294967296) 256;
  FStar.Math.Lemmas.lemma_div_mod (x / 1099511627776) 256;
  FStar.Math.Lemmas.lemma_div_mod (x / 281474976710656) 256;
  FStar.Math.Lemmas.lemma_div_mod (x / 72057594037927936) 256;
  FStar.Math.Lemmas.division_multiplication_lemma x 256 256;
  FStar.Math.Lemmas.division_multiplication_lemma x 65536 256;
  FStar.Math.Lemmas.division_multiplication_lemma x 16777216 256;
  FStar.Math.Lemmas.division_multiplication_lemma x 4294967296 256;
  FStar.Math.Lemmas.division_multiplication_lemma x 1099511627776 256;
  FStar.Math.Lemmas.division_multiplication_lemma x 281474976710656 256;
  FStar.Math.Lemmas.division_multiplication_lemma x 72057594037927936 256;
  FStar.Math.Lemmas.small_division_lemma_1 x 18446744073709551616

let encode_u64_le_is_injective (left right:u64)
  : Lemma
      (requires (encode_u64_le left == encode_u64_le right))
      (ensures (left == right))
  = decode_encode_u64_le left;
    decode_encode_u64_le right;
    mk_int_v_lemma left;
    mk_int_v_lemma right

/// Equal inputs have equal same-offset segments when each segment has the declared byte view.
let equal_embedded_segment
    (left_input right_input:t_Slice u8)
    (left_segment right_segment:t_Slice u8)
    (offset:nat {
      offset + Seq.length left_segment <= Seq.length left_input /\
      offset + Seq.length right_segment <= Seq.length right_input })
  : Lemma
      (requires
        (left_input == right_input /\
         Seq.length left_segment == Seq.length right_segment /\
         (forall (i:nat { i < Seq.length left_segment }).
            Seq.index left_input (offset + i) ==
            Seq.index left_segment i) /\
         (forall (i:nat { i < Seq.length right_segment }).
            Seq.index right_input (offset + i) ==
            Seq.index right_segment i)))
      (ensures (left_segment == right_segment))
  =
  let segment_byte (i:nat { i < Seq.length left_segment })
    : Lemma (Seq.index left_segment i == Seq.index right_segment i)
    = assert
        (Seq.index left_input (offset + i) ==
         Seq.index left_segment i);
      assert
        (Seq.index right_input (offset + i) ==
         Seq.index right_segment i)
  in
  FStar.Classical.forall_intro segment_byte;
  FStar.Seq.Base.lemma_eq_intro left_segment right_segment;
  FStar.Seq.Base.lemma_eq_elim left_segment right_segment

let production_commitment_input
    (key:t_Array u8 (mk_usize 32))
    (nonce:t_Array u8 (mk_usize 12))
    (associated_data:t_Array u8 (mk_usize 153))
    (tag:t_Array u8 (mk_usize 16))
    (sequence sender_id:u64)
  : t_Array u8 (mk_usize 229) =
  (build_commitment_transcript
     key nonce associated_data tag sequence sender_id).f_bytes

/// Equality of production transcript bytes implies equality of all six semantic fields.
let production_commitment_input_is_injective
    (left_key right_key:t_Array u8 (mk_usize 32))
    (left_nonce right_nonce:t_Array u8 (mk_usize 12))
    (left_associated_data right_associated_data:t_Array u8 (mk_usize 153))
    (left_tag right_tag:t_Array u8 (mk_usize 16))
    (left_sequence right_sequence left_sender_id right_sender_id:u64)
  : Lemma
      (requires
        (production_commitment_input
           left_key left_nonce left_associated_data left_tag
           left_sequence left_sender_id ==
         production_commitment_input
           right_key right_nonce right_associated_data right_tag
           right_sequence right_sender_id))
      (ensures
        (left_key == right_key /\
         left_nonce == right_nonce /\
         left_associated_data == right_associated_data /\
         left_tag == right_tag /\
         left_sequence == right_sequence /\
         left_sender_id == right_sender_id))
  =
  let left_input = production_commitment_input
    left_key left_nonce left_associated_data left_tag
    left_sequence left_sender_id in
  let right_input = production_commitment_input
    right_key right_nonce right_associated_data right_tag
    right_sequence right_sender_id in
  commitment_transcript_is_exact
    left_key left_nonce left_associated_data left_tag
    left_sequence left_sender_id;
  commitment_transcript_is_exact
    right_key right_nonce right_associated_data right_tag
    right_sequence right_sender_id;
  equal_embedded_segment left_input right_input left_key right_key 0;
  equal_embedded_segment left_input right_input left_nonce right_nonce 32;
  equal_embedded_segment
    left_input right_input left_associated_data right_associated_data 44;
  equal_embedded_segment left_input right_input left_tag right_tag 197;
  equal_embedded_segment
    left_input right_input
    (encode_u64_le left_sequence) (encode_u64_le right_sequence) 213;
  encode_u64_le_is_injective left_sequence right_sequence;
  equal_embedded_segment
    left_input right_input
    (encode_u64_le left_sender_id) (encode_u64_le right_sender_id) 221;
  encode_u64_le_is_injective left_sender_id right_sender_id

let ctx_opening_accepted
    (#ciphertext_t:Type)
    (#plaintext_t:Type)
    (hash:
      t_Array u8 (mk_usize 229) ->
      t_Array u8 (mk_usize 64))
    (aead_open:
      t_Array u8 (mk_usize 32) ->
      t_Array u8 (mk_usize 12) ->
      t_Array u8 (mk_usize 153) ->
      ciphertext_t ->
      t_Array u8 (mk_usize 16) ->
      Core_models.Option.t_Option plaintext_t)
    (ciphertext:ciphertext_t)
    (commitment:t_Array u8 (mk_usize 64))
    (key:t_Array u8 (mk_usize 32))
    (nonce:t_Array u8 (mk_usize 12))
    (associated_data:t_Array u8 (mk_usize 153))
    (tag:t_Array u8 (mk_usize 16))
    (sequence sender_id:u64)
    (plaintext:plaintext_t)
  : prop =
  hash
    (production_commitment_input
       key nonce associated_data tag sequence sender_id) == commitment /\
  aead_open key nonce associated_data ciphertext tag ==
    Core_models.Option.Option_Some plaintext

let ctx_explanations_are_distinct
    (#plaintext_t:Type)
    (left_key right_key:t_Array u8 (mk_usize 32))
    (left_nonce right_nonce:t_Array u8 (mk_usize 12))
    (left_associated_data right_associated_data:t_Array u8 (mk_usize 153))
    (left_sequence right_sequence left_sender_id right_sender_id:u64)
    (left_plaintext right_plaintext:plaintext_t)
  : prop =
  left_key <> right_key \/
  left_nonce <> right_nonce \/
  left_associated_data <> right_associated_data \/
  left_sequence <> right_sequence \/
  left_sender_id <> right_sender_id \/
  (left_plaintext == right_plaintext ==> False)

type t_HashCollisionWitness = {
  f_left_input:t_Array u8 (mk_usize 229);
  f_right_input:t_Array u8 (mk_usize 229)
}

let valid_hash_collision_witness
    (hash:
      t_Array u8 (mk_usize 229) ->
      t_Array u8 (mk_usize 64))
    (witness:t_HashCollisionWitness)
  : prop =
  witness.f_left_input <> witness.f_right_input /\
  hash witness.f_left_input == hash witness.f_right_input

/// Two distinct accepted explanations of one fixed `C || T || U` payload return an explicit hash-collision witness.
let ctx_distinct_openings_imply_hash_collision
    (#ciphertext_t:Type)
    (#plaintext_t:Type)
    (hash:
      t_Array u8 (mk_usize 229) ->
      t_Array u8 (mk_usize 64))
    (aead_open:
      t_Array u8 (mk_usize 32) ->
      t_Array u8 (mk_usize 12) ->
      t_Array u8 (mk_usize 153) ->
      ciphertext_t ->
      t_Array u8 (mk_usize 16) ->
      Core_models.Option.t_Option plaintext_t)
    (ciphertext:ciphertext_t)
    (tag:t_Array u8 (mk_usize 16))
    (commitment:t_Array u8 (mk_usize 64))
    (left_key right_key:t_Array u8 (mk_usize 32))
    (left_nonce right_nonce:t_Array u8 (mk_usize 12))
    (left_associated_data right_associated_data:t_Array u8 (mk_usize 153))
    (left_sequence right_sequence left_sender_id right_sender_id:u64)
    (left_plaintext right_plaintext:plaintext_t)
  : Pure t_HashCollisionWitness
      (requires
        (ctx_opening_accepted
           hash aead_open ciphertext commitment
           left_key left_nonce left_associated_data tag
           left_sequence left_sender_id left_plaintext /\
         ctx_opening_accepted
           hash aead_open ciphertext commitment
           right_key right_nonce right_associated_data tag
           right_sequence right_sender_id right_plaintext /\
         ctx_explanations_are_distinct
           left_key right_key left_nonce right_nonce
           left_associated_data right_associated_data
           left_sequence right_sequence left_sender_id right_sender_id
           left_plaintext right_plaintext))
      (ensures
        (fun witness ->
          witness.f_left_input == production_commitment_input
            left_key left_nonce left_associated_data tag
            left_sequence left_sender_id /\
          witness.f_right_input == production_commitment_input
            right_key right_nonce right_associated_data tag
            right_sequence right_sender_id /\
          valid_hash_collision_witness hash witness))
  =
  let left_input = production_commitment_input
    left_key left_nonce left_associated_data tag
    left_sequence left_sender_id in
  let right_input = production_commitment_input
    right_key right_nonce right_associated_data tag
    right_sequence right_sender_id in
  if FStar.Seq.Base.eq left_input right_input then
    (FStar.Seq.Base.lemma_eq_elim left_input right_input;
     production_commitment_input_is_injective
       left_key right_key left_nonce right_nonce
       left_associated_data right_associated_data tag tag
       left_sequence right_sequence left_sender_id right_sender_id)
  else
    ();
  { f_left_input = left_input; f_right_input = right_input }
