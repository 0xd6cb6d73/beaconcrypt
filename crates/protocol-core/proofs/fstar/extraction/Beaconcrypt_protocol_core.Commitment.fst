module Beaconcrypt_protocol_core.Commitment
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

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
  let bytes:t_Array u8 (mk_usize 229) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 229) in
  let bytes:t_Array u8 (mk_usize 229) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core_models.Ops.Range.f_start = mk_usize 0; Core_models.Ops.Range.f_end = mk_usize 32 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (bytes.[ {
                Core_models.Ops.Range.f_start = mk_usize 0;
                Core_models.Ops.Range.f_end = mk_usize 32
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (key <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let bytes:t_Array u8 (mk_usize 229) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core_models.Ops.Range.f_start = mk_usize 32; Core_models.Ops.Range.f_end = mk_usize 44 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (bytes.[ {
                Core_models.Ops.Range.f_start = mk_usize 32;
                Core_models.Ops.Range.f_end = mk_usize 44
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (nonce <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let bytes:t_Array u8 (mk_usize 229) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core_models.Ops.Range.f_start = mk_usize 44; Core_models.Ops.Range.f_end = mk_usize 197 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (bytes.[ {
                Core_models.Ops.Range.f_start = mk_usize 44;
                Core_models.Ops.Range.f_end = mk_usize 197
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (associated_data <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let bytes:t_Array u8 (mk_usize 229) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core_models.Ops.Range.f_start = mk_usize 197; Core_models.Ops.Range.f_end = mk_usize 213 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (bytes.[ {
                Core_models.Ops.Range.f_start = mk_usize 197;
                Core_models.Ops.Range.f_end = mk_usize 213
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (tag <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let bytes:t_Array u8 (mk_usize 229) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core_models.Ops.Range.f_start = mk_usize 213; Core_models.Ops.Range.f_end = mk_usize 221 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (bytes.[ {
                Core_models.Ops.Range.f_start = mk_usize 213;
                Core_models.Ops.Range.f_end = mk_usize 221
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (sequence <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let bytes:t_Array u8 (mk_usize 229) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range bytes
      ({ Core_models.Ops.Range.f_start = mk_usize 221; Core_models.Ops.Range.f_end = mk_usize 229 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (bytes.[ {
                Core_models.Ops.Range.f_start = mk_usize 221;
                Core_models.Ops.Range.f_end = mk_usize 229
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (sender_id <: t_Slice u8)
        <:
        t_Slice u8)
  in
  { f_bytes = bytes } <: t_CommitmentTranscript
