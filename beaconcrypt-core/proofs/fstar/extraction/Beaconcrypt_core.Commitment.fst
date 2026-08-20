module Beaconcrypt_core.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let v_AEAD_KEY_SIZE: usize = mk_usize 32

/// Fixed-width input to the production BLAKE2b-512 commitment operation.
type t_CommitmentTranscript = { f_bytes:t_Array u8 (mk_usize 229) }

let encode_u64_le (value: u64) : t_Array u8 (mk_usize 8) =
  let list =
    [
      cast (value <: u64) <: u8;
      cast (value >>! mk_i32 8 <: u64) <: u8;
      cast (value >>! mk_i32 16 <: u64) <: u8;
      cast (value >>! mk_i32 24 <: u64) <: u8;
      cast (value >>! mk_i32 32 <: u64) <: u8;
      cast (value >>! mk_i32 40 <: u64) <: u8;
      cast (value >>! mk_i32 48 <: u64) <: u8;
      cast (value >>! mk_i32 56 <: u64) <: u8
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list 8 list

/// Build `key || nonce || associated_data || tag || LE64(sequence) || LE64(sender_id)` without hashing it.
let build_commitment_transcript
      (key: t_Array u8 (mk_usize 32))
      (nonce: t_Array u8 (mk_usize 12))
      (associated_data: t_Array u8 (mk_usize 153))
      (tag: t_Array u8 (mk_usize 16))
      (sequence sender_id: u64)
    : t_CommitmentTranscript =
  let sequence:t_Array u8 (mk_usize 8) = encode_u64_le sequence in
  let sender_id:t_Array u8 (mk_usize 8) = encode_u64_le sender_id in
  let bytes:t_Array u8 (mk_usize 229) =
    Core_models.Array.from_fn #u8
      (mk_usize 229)
      #(usize -> u8)
      (fun i ->
          let i:usize = i in
          if i <. mk_usize 32 <: bool
          then key.[ i ] <: u8
          else
            if i <. mk_usize 44 <: bool
            then nonce.[ i -! mk_usize 32 <: usize ] <: u8
            else
              if i <. mk_usize 197 <: bool
              then associated_data.[ i -! mk_usize 44 <: usize ] <: u8
              else
                if i <. mk_usize 213 <: bool
                then tag.[ i -! mk_usize 197 <: usize ] <: u8
                else
                  if i <. mk_usize 221 <: bool
                  then sequence.[ i -! mk_usize 213 <: usize ] <: u8
                  else sender_id.[ i -! mk_usize 221 <: usize ] <: u8)
  in
  { f_bytes = bytes } <: t_CommitmentTranscript
