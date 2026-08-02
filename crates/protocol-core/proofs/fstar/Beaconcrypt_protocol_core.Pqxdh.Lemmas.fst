/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_protocol_core.Pqxdh.Lemmas

open Rust_primitives.Integers
open Rust_primitives.Arrays
open Beaconcrypt_protocol_core.Pqxdh

#set-options "--fuel 1 --ifuel 1 --z3rlimit 600"

/// Per-byte view of the monomorphized fixed-range update contract.  Keeping
/// this small derived lemma local lets the manual proof module cache cleanly
/// without adding another proof-library module to the generated dependency
/// graph.
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

/// The adapter contract for an honest PQXDH execution: both roles supply the
/// same four ordered X25519 results and the same ML-KEM shared secret.  The
/// cryptographic primitive implementations establish this relation; this
/// module proves what the protocol core derives from it.
let honest_shared_secrets
    (beacon server:t_PqxdhSharedSecrets)
  : prop =
  beacon.f_dh1 == server.f_dh1 /\
  beacon.f_dh2 == server.f_dh2 /\
  beacon.f_dh3 == server.f_dh3 /\
  beacon.f_dh4 == server.f_dh4 /\
  beacon.f_kem_shared_secret == server.f_kem_shared_secret

/// The algorithm tags are concrete and pairwise disjoint.
let key_type_tags_are_disjoint (_:Prims.unit)
  : Lemma
      (v_SIGN_TYPE_ED25519 == mk_u8 1 /\
       v_KEM_TYPE_MLKEM768 == mk_u8 3 /\
       v_KEM_TYPE_X25519 == mk_u8 4 /\
       v_SIGN_TYPE_ED25519 <> v_KEM_TYPE_MLKEM768 /\
       v_SIGN_TYPE_ED25519 <> v_KEM_TYPE_X25519 /\
       v_KEM_TYPE_MLKEM768 <> v_KEM_TYPE_X25519)
  = ()

/// Each tagged encoding consists of exactly one algorithm byte followed by
/// the unmodified key bytes.
let sign_key_tag_is_exact (key:t_Array u8 (mk_usize 32))
  : Lemma
      (Seq.index (tag_sign_key key) 0 == v_SIGN_TYPE_ED25519 /\
       Seq.slice (tag_sign_key key) 1 33 == key)
  =
  let initialized =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 33))
      (mk_usize 0)
      v_SIGN_TYPE_ED25519 in
  FStar.Seq.Base.lemma_index_slice initialized 0 1 0;
  FStar.Seq.Base.lemma_index_slice (tag_sign_key key) 0 1 0

let x25519_key_tag_is_exact (key:t_Array u8 (mk_usize 32))
  : Lemma
      (Seq.index (tag_x25519_key key) 0 == v_KEM_TYPE_X25519 /\
       Seq.slice (tag_x25519_key key) 1 33 == key)
  =
  let initialized =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 33))
      (mk_usize 0)
      v_KEM_TYPE_X25519 in
  FStar.Seq.Base.lemma_index_slice initialized 0 1 0;
  FStar.Seq.Base.lemma_index_slice (tag_x25519_key key) 0 1 0

let mlkem768_key_tag_is_exact (key:t_Array u8 (mk_usize 1184))
  : Lemma
      (Seq.index (tag_mlkem768_key key) 0 == v_KEM_TYPE_MLKEM768 /\
       Seq.slice (tag_mlkem768_key key) 1 1185 == key)
  =
  let initialized =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 1185))
      (mk_usize 0)
      v_KEM_TYPE_MLKEM768 in
  FStar.Seq.Base.lemma_index_slice initialized 0 1 0;
  FStar.Seq.Base.lemma_index_slice (tag_mlkem768_key key) 0 1 0

/// The protocol-owned encoders and decoders are exact inverses.
let sign_key_tag_round_trip (key:t_Array u8 (mk_usize 32))
  : Lemma
      (untag_sign_key (tag_sign_key key) ==
       Core_models.Option.Option_Some key)
  = sign_key_tag_is_exact key

let x25519_key_tag_round_trip (key:t_Array u8 (mk_usize 32))
  : Lemma
      (untag_x25519_key (tag_x25519_key key) ==
       Core_models.Option.Option_Some key)
  = x25519_key_tag_is_exact key

let mlkem768_key_tag_round_trip (key:t_Array u8 (mk_usize 1184))
  : Lemma
      (untag_mlkem768_key (tag_mlkem768_key key) ==
       Core_models.Option.Option_Some key)
  = mlkem768_key_tag_is_exact key

/// A message emitted by `beacon_start` validates to exactly the public
/// material from which it was constructed.
let beacon_start_validates
    (state:t_BeaconFresh)
    (inputs:t_BeaconStartInputs)
    (coins:t_BeaconCoins)
  : Lemma
      (let started = beacon_start state inputs coins in
       match validate_init_kex started.f_message with
       | Core_models.Result.Result_Ok verified ->
           verified.f_beacon_identity_public_key == inputs.f_identity_public_key /\
           verified.f_beacon_prekey_public_key == inputs.f_prekey_public_key /\
           verified.f_beacon_one_time_public_key == coins.f_one_time_public_key /\
           verified.f_beacon_pq_public_key == inputs.f_pq_public_key /\
           started.f_state.f_server_key_id == state.f_server_key_id /\
           started.f_state.f_beacon_identity_public_key == inputs.f_identity_public_key
       | Core_models.Result.Result_Err _ -> False)
  =
  sign_key_tag_round_trip inputs.f_identity_public_key;
  x25519_key_tag_round_trip inputs.f_prekey_public_key;
  x25519_key_tag_round_trip coins.f_one_time_public_key;
  mlkem768_key_tag_round_trip inputs.f_pq_public_key

/// The replay identifier is the exact, collision-free concatenation of the
/// authenticated identity and one-time public keys.
let registration_id_is_exact (registration:t_VerifiedInitKex)
  : Lemma
      (let id = impl_VerifiedInitKex__registration_id registration in
       Seq.slice id.f_bytes 0 32 == registration.f_beacon_identity_public_key /\
       Seq.slice id.f_bytes 32 64 == registration.f_beacon_one_time_public_key)
  = ()

let valid_shared_secrets (secrets:t_PqxdhSharedSecrets) : prop =
  not (is_all_zero secrets.f_dh1) /\
  not (is_all_zero secrets.f_dh2) /\
  not (is_all_zero secrets.f_dh3) /\
  not (is_all_zero secrets.f_dh4)

let v_ROOT_RANGE_1:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 32;
    Core_models.Ops.Range.f_end = mk_usize 64 }

let v_ROOT_RANGE_2:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 64;
    Core_models.Ops.Range.f_end = mk_usize 96 }

let v_ROOT_RANGE_3:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 96;
    Core_models.Ops.Range.f_end = mk_usize 128 }

let v_ROOT_RANGE_4:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 128;
    Core_models.Ops.Range.f_end = mk_usize 160 }

let v_ROOT_RANGE_5:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 160;
    Core_models.Ops.Range.f_end = mk_usize 192 }

/// A proof-only name for the straight-line fixed-range update expression in
/// `build_root_key_input`.
let root_transcript_bytes (secrets:t_PqxdhSharedSecrets)
  : t_Array u8 (mk_usize 192) =
  let b0 = Rust_primitives.Hax.repeat (mk_u8 255) (mk_usize 192) in
  let b1 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b0 v_ROOT_RANGE_1 secrets.f_dh1 in
  let b2 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b1 v_ROOT_RANGE_2 secrets.f_dh2 in
  let b3 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b2 v_ROOT_RANGE_3 secrets.f_dh3 in
  let b4 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b3 v_ROOT_RANGE_4 secrets.f_dh4 in
  Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b4 v_ROOT_RANGE_5 secrets.f_kem_shared_secret

let root_transcript_byte_is_exact
    (secrets:t_PqxdhSharedSecrets)
    (i:nat { i < 192 })
  : Lemma
      (Seq.index (root_transcript_bytes secrets) i ==
       (if i < 32 then mk_u8 255
       else if i < 64 then Seq.index secrets.f_dh1 (i - 32)
       else if i < 96 then Seq.index secrets.f_dh2 (i - 64)
       else if i < 128 then Seq.index secrets.f_dh3 (i - 96)
       else if i < 160 then Seq.index secrets.f_dh4 (i - 128)
       else Seq.index secrets.f_kem_shared_secret (i - 160)))
  =
  let b0 = Rust_primitives.Hax.repeat (mk_u8 255) (mk_usize 192) in
  let b1 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b0 v_ROOT_RANGE_1 secrets.f_dh1 in
  let b2 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b1 v_ROOT_RANGE_2 secrets.f_dh2 in
  let b3 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b2 v_ROOT_RANGE_3 secrets.f_dh3 in
  let b4 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b3 v_ROOT_RANGE_4 secrets.f_dh4 in
  update_at_range_byte_view b0 v_ROOT_RANGE_1 secrets.f_dh1;
  update_at_range_byte_view b1 v_ROOT_RANGE_2 secrets.f_dh2;
  update_at_range_byte_view b2 v_ROOT_RANGE_3 secrets.f_dh3;
  update_at_range_byte_view b3 v_ROOT_RANGE_4 secrets.f_dh4;
  update_at_range_byte_view b4 v_ROOT_RANGE_5 secrets.f_kem_shared_secret;
  FStar.Seq.Base.lemma_index_create 192 (mk_u8 255) i

let valid_root_build_uses_exact_bytes
    (secrets:t_PqxdhSharedSecrets { valid_shared_secrets secrets })
  : Lemma
      (build_root_key_input secrets ==
       Core_models.Result.Result_Ok
         ({ f_bytes = root_transcript_bytes secrets } <: t_RootKeyInput))
  = ()

/// With four valid classical DH contributions the returned transcript is
/// exactly `0xff^32 || DH1 || DH2 || DH3 || DH4 || ML-KEM-SS`.
let root_key_transcript_is_exact
    (secrets:t_PqxdhSharedSecrets { valid_shared_secrets secrets })
  : Lemma
      (match build_root_key_input secrets with
       | Core_models.Result.Result_Ok root ->
           forall (i:nat { i < 192 }).
             Seq.index root.f_bytes i ==
             (if i < 32 then mk_u8 255
             else if i < 64 then Seq.index secrets.f_dh1 (i - 32)
             else if i < 96 then Seq.index secrets.f_dh2 (i - 64)
             else if i < 128 then Seq.index secrets.f_dh3 (i - 96)
             else if i < 160 then Seq.index secrets.f_dh4 (i - 128)
             else Seq.index secrets.f_kem_shared_secret (i - 160))
       | Core_models.Result.Result_Err _ -> False)
  = valid_root_build_uses_exact_bytes secrets;
    FStar.Classical.forall_intro (root_transcript_byte_is_exact secrets)

let all_zero_dh_is_rejected
    (secrets:t_PqxdhSharedSecrets {
       is_all_zero secrets.f_dh1 \/
       is_all_zero secrets.f_dh2 \/
       is_all_zero secrets.f_dh3 \/
       is_all_zero secrets.f_dh4 })
  : Lemma
      (build_root_key_input secrets ==
       Core_models.Result.Result_Err RegistrationError_InvalidDhOutput)
  = ()

/// Conditional honest-role agreement.  It deliberately exposes the adapter
/// obligation instead of treating X25519 or ML-KEM agreement as an axiom.
let honest_roles_build_the_same_root
    (beacon_secrets server_secrets:t_PqxdhSharedSecrets {
       honest_shared_secrets beacon_secrets server_secrets })
  : Lemma
      (match build_root_key_input beacon_secrets,
             build_root_key_input server_secrets with
       | Core_models.Result.Result_Ok beacon_root,
         Core_models.Result.Result_Ok server_root -> beacon_root == server_root
       | Core_models.Result.Result_Err beacon_error,
         Core_models.Result.Result_Err server_error -> beacon_error == server_error
       | _ -> False)
  = ()

let v_AD_RANGE_1:Core_models.Ops.Range.t_RangeTo usize =
  { Core_models.Ops.Range.f_end = mk_usize 33 }

let v_AD_RANGE_2:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 33;
    Core_models.Ops.Range.f_end = mk_usize 66 }

let v_AD_RANGE_3:Core_models.Ops.Range.t_Range usize =
  { Core_models.Ops.Range.f_start = mk_usize 66;
    Core_models.Ops.Range.f_end = mk_usize 112 }

let v_AD_RANGE_4:Core_models.Ops.Range.t_RangeFrom usize =
  { Core_models.Ops.Range.f_start = mk_usize 112 }

let associated_data_bytes
    (server_identity beacon_identity:t_Array u8 (mk_usize 32))
  : t_Array u8 (mk_usize 153) =
  let server_tag = tag_sign_key server_identity in
  let beacon_tag = tag_sign_key beacon_identity in
  let b0 = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 153) in
  let b1 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to
    b0 v_AD_RANGE_1 server_tag in
  let b2 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b1 v_AD_RANGE_2 beacon_tag in
  let b3 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b2 v_AD_RANGE_3 v_PQXDH_INFO in
  Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from
    b3 v_AD_RANGE_4 v_SYM_RATCHET_INFO

let ad_range_to_byte
    (s:t_Array u8 (mk_usize 153))
    (x:t_Array u8 (mk_usize 33))
    (i:nat { i < 153 })
  : Lemma
      (let out =
         Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to
           s v_AD_RANGE_1 x in
       Seq.index out i == (if i < 33 then Seq.index x i else Seq.index s i))
  =
  let out = Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to
    s v_AD_RANGE_1 x in
  if i < 33 then
    FStar.Seq.Base.lemma_index_slice out 0 33 i
  else
    (FStar.Seq.Base.lemma_index_slice out 33 153 (i - 33);
     FStar.Seq.Base.lemma_index_slice s 33 153 (i - 33))

let ad_range_from_byte
    (s:t_Array u8 (mk_usize 153))
    (x:t_Array u8 (mk_usize 41))
    (i:nat { i < 153 })
  : Lemma
      (let out =
         Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from
           s v_AD_RANGE_4 x in
       Seq.index out i ==
         (if i < 112 then Seq.index s i else Seq.index x (i - 112)))
  =
  let out = Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from
    s v_AD_RANGE_4 x in
  if i < 112 then
    (FStar.Seq.Base.lemma_index_slice out 0 112 i;
     FStar.Seq.Base.lemma_index_slice s 0 112 i)
  else
    FStar.Seq.Base.lemma_index_slice out 112 153 (i - 112)

let associated_data_byte_is_exact
    (server_identity beacon_identity:t_Array u8 (mk_usize 32))
    (i:nat { i < 153 })
  : Lemma
      (Seq.index (associated_data_bytes server_identity beacon_identity) i ==
       (if i < 33 then Seq.index (tag_sign_key server_identity) i
        else if i < 66 then Seq.index (tag_sign_key beacon_identity) (i - 33)
        else if i < 112 then Seq.index v_PQXDH_INFO (i - 66)
        else Seq.index v_SYM_RATCHET_INFO (i - 112)))
  =
  let server_tag = tag_sign_key server_identity in
  let beacon_tag = tag_sign_key beacon_identity in
  let b0 = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 153) in
  let b1 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to
    b0 v_AD_RANGE_1 server_tag in
  let b2 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b1 v_AD_RANGE_2 beacon_tag in
  let b3 = Rust_primitives.Hax.Monomorphized_update_at.update_at_range
    b2 v_AD_RANGE_3 v_PQXDH_INFO in
  ad_range_to_byte b0 server_tag i;
  update_at_range_byte_view b1 v_AD_RANGE_2 beacon_tag;
  update_at_range_byte_view b2 v_AD_RANGE_3 v_PQXDH_INFO;
  ad_range_from_byte b3 v_SYM_RATCHET_INFO i

let associated_data_build_uses_exact_bytes
    (server_identity beacon_identity:t_Array u8 (mk_usize 32))
  : Lemma
      (build_associated_data server_identity beacon_identity ==
       associated_data_bytes server_identity beacon_identity)
  = ()

/// Associated data is the exact ordered transcript
/// `tag(server) || tag(beacon) || PQXDH_INFO || SYM_RATCHET_INFO`.
let associated_data_is_exact
    (server_identity beacon_identity:t_Array u8 (mk_usize 32))
  : Lemma
      (let ad = build_associated_data server_identity beacon_identity in
       forall (i:nat { i < 153 }).
         Seq.index ad i ==
         (if i < 33 then Seq.index (tag_sign_key server_identity) i
          else if i < 66 then Seq.index (tag_sign_key beacon_identity) (i - 33)
          else if i < 112 then Seq.index v_PQXDH_INFO (i - 66)
          else Seq.index v_SYM_RATCHET_INFO (i - 112)))
  = associated_data_build_uses_exact_bytes server_identity beacon_identity;
    FStar.Classical.forall_intro
      (associated_data_byte_is_exact server_identity beacon_identity)

/// Role agreement on the two authenticated identities implies byte-for-byte
/// associated-data agreement.
let honest_roles_build_the_same_associated_data
    (beacon_server_identity server_server_identity:t_Array u8 (mk_usize 32) {
       beacon_server_identity == server_server_identity })
    (beacon_identity server_beacon_identity:t_Array u8 (mk_usize 32) {
       beacon_identity == server_beacon_identity })
  : Lemma
      (build_associated_data beacon_server_identity beacon_identity ==
       build_associated_data server_server_identity server_beacon_identity)
  = ()

/// Both public utilities and the candidate methods select complementary,
/// bounded halves of the 64-byte ratchet KDF output.
let ratchet_initializations_are_complementary (_:Prims.unit)
  : Lemma
      ((beacon_ratchet_initialization ()).f_send_offset == mk_u8 32 /\
       (beacon_ratchet_initialization ()).f_receive_offset == mk_u8 0 /\
       (server_ratchet_initialization ()).f_send_offset == mk_u8 0 /\
       (server_ratchet_initialization ()).f_receive_offset == mk_u8 32 /\
       (beacon_ratchet_initialization ()).f_send_offset ==
         (server_ratchet_initialization ()).f_receive_offset /\
       (beacon_ratchet_initialization ()).f_receive_offset ==
         (server_ratchet_initialization ()).f_send_offset)
  = ()

let candidate_ratchet_initializations_are_complementary
    (beacon:t_BeaconRegistrationCandidate)
    (server:t_ServerRegistrationCandidate)
  : Lemma
      ((impl_BeaconRegistrationCandidate__ratchet_initialization beacon).f_send_offset ==
         (impl_ServerRegistrationCandidate__ratchet_initialization server).f_receive_offset /\
       (impl_BeaconRegistrationCandidate__ratchet_initialization beacon).f_receive_offset ==
         (impl_ServerRegistrationCandidate__ratchet_initialization server).f_send_offset)
  = ()

/// The authenticated key-ID prefix is the exact little-endian representation
/// of the assigned 64-bit identifier.
let registration_key_id_binding_is_exact (key_id:u64)
  : Lemma
      (let bytes = (registration_key_id_binding key_id).f_bytes in
       Seq.index bytes 0 == (Rust_primitives.cast (key_id <: u64) <: u8) /\
       Seq.index bytes 1 ==
         (Rust_primitives.cast (key_id >>! mk_i32 8 <: u64) <: u8) /\
       Seq.index bytes 2 ==
         (Rust_primitives.cast (key_id >>! mk_i32 16 <: u64) <: u8) /\
       Seq.index bytes 3 ==
         (Rust_primitives.cast (key_id >>! mk_i32 24 <: u64) <: u8) /\
       Seq.index bytes 4 ==
         (Rust_primitives.cast (key_id >>! mk_i32 32 <: u64) <: u8) /\
       Seq.index bytes 5 ==
         (Rust_primitives.cast (key_id >>! mk_i32 40 <: u64) <: u8) /\
       Seq.index bytes 6 ==
         (Rust_primitives.cast (key_id >>! mk_i32 48 <: u64) <: u8) /\
       Seq.index bytes 7 ==
         (Rust_primitives.cast (key_id >>! mk_i32 56 <: u64) <: u8))
  = ()

let registration_key_id_binding_has_le64_values (key_id:u64)
  : Lemma
      (let bytes = (registration_key_id_binding key_id).f_bytes in
       v (Seq.index bytes 0) == v key_id % 256 /\
       v (Seq.index bytes 1) == (v key_id / pow2 8) % 256 /\
       v (Seq.index bytes 2) == (v key_id / pow2 16) % 256 /\
       v (Seq.index bytes 3) == (v key_id / pow2 24) % 256 /\
       v (Seq.index bytes 4) == (v key_id / pow2 32) % 256 /\
       v (Seq.index bytes 5) == (v key_id / pow2 40) % 256 /\
       v (Seq.index bytes 6) == (v key_id / pow2 48) % 256 /\
       v (Seq.index bytes 7) == (v key_id / pow2 56) % 256)
  = shift_right_lemma key_id (mk_i32 8);
    shift_right_lemma key_id (mk_i32 16);
    shift_right_lemma key_id (mk_i32 24);
    shift_right_lemma key_id (mk_i32 32);
    shift_right_lemma key_id (mk_i32 40);
    shift_right_lemma key_id (mk_i32 48);
    shift_right_lemma key_id (mk_i32 56)

let exact_key_id_binding_authenticates
    (candidate:t_BeaconRegistrationCandidate)
  : Lemma
      (authenticate_registration_key_id_binding candidate
         (impl_BeaconRegistrationCandidate__key_id_binding candidate).f_bytes ==
       Core_models.Result.Result_Ok
         ({ f_candidate = candidate } <: t_AuthenticatedBeaconRegistration))
  = ()

let mismatched_key_id_binding_is_rejected
    (candidate:t_BeaconRegistrationCandidate)
    (authenticated_binding:t_Array u8 (mk_usize 8) {
       authenticated_binding <>
         (impl_BeaconRegistrationCandidate__key_id_binding candidate).f_bytes })
  : Lemma
      (authenticate_registration_key_id_binding candidate authenticated_binding ==
       Core_models.Result.Result_Err RegistrationError_KeyIdMismatch)
  = ()

/// Only the authenticated typestate can reach commit, and commit publishes
/// exactly the candidate's server and assigned peer identifiers.
let beacon_commit_preserves_authenticated_ids
    (authenticated:t_AuthenticatedBeaconRegistration)
  : Lemma
      ((beacon_commit authenticated).f_server_key_id ==
         authenticated.f_candidate.f_server_key_id /\
       (beacon_commit authenticated).f_assigned_key_id ==
         authenticated.f_candidate.f_assigned_key_id)
  = ()

/// Replay-status refinement obligations supplied by the persistence adapter.
let fresh_registration_status_is_accepted (_:Prims.unit)
  : Lemma
      (validate_registration_status RegistrationStatus_Fresh ==
       Core_models.Result.Result_Ok ())
  = ()

let consumed_registration_status_is_rejected (_:Prims.unit)
  : Lemma
      (validate_registration_status RegistrationStatus_Consumed ==
       Core_models.Result.Result_Err RegistrationError_RegistrationReplay)
  = ()

let server_rejects_consumed_registration
    (state:t_ServerState)
    (registration:t_VerifiedInitKex)
    (binding:t_ServerBinding)
    (coins:t_ServerCoins)
    (secrets:t_PqxdhSharedSecrets)
  : Lemma
      (server_accept state registration RegistrationStatus_Consumed binding coins secrets ==
       Core_models.Result.Result_Err RegistrationError_RegistrationReplay)
  = ()

/// Fresh acceptance constructs a pending token but leaves the active counter
/// state byte-for-byte unchanged.  Root-input failure is propagated exactly.
let server_fresh_acceptance_shape
    (state:t_ServerState)
    (registration:t_VerifiedInitKex)
    (binding:t_ServerBinding)
    (coins:t_ServerCoins)
    (secrets:t_PqxdhSharedSecrets)
  : Lemma
      (match server_accept state registration RegistrationStatus_Fresh binding coins secrets,
             build_root_key_input secrets with
       | Core_models.Result.Result_Ok
           (returned_state, (pending:t_PendingServerRegistration)),
         Core_models.Result.Result_Ok root ->
           returned_state == state /\
           pending.f_server_binding == binding /\
           pending.f_registration_id ==
             impl_VerifiedInitKex__registration_id registration /\
           pending.f_beacon_identity_public_key ==
             registration.f_beacon_identity_public_key /\
           pending.f_ephemeral_public_key == coins.f_ephemeral_public_key /\
           pending.f_kem_ciphertext == coins.f_kem_ciphertext /\
           pending.f_root_key_input == root
       | Core_models.Result.Result_Err accept_error,
         Core_models.Result.Result_Err root_error -> accept_error == root_error
       | _ -> False)
  = ()

/// Counter allocation is checked mathematical increment or explicit
/// exhaustion; wrapping can never manufacture key ID zero.
let next_server_key_id_is_checked (state:t_ServerState)
  : Lemma
      (match server_next_key_id state with
       | Core_models.Result.Result_Ok next ->
           v next == v state.f_last_key_id + 1
       | Core_models.Result.Result_Err err ->
           err == RegistrationError_KeyIdExhausted /\
           state.f_last_key_id == Core_models.Num.impl_u64__MAX)
  = ()

let server_binding_mismatch_is_rejected
    (state:t_ServerState)
    (pending:t_PendingServerRegistration)
    (current:t_ServerBinding {
       pending.f_server_binding.f_identity_key_id <> current.f_identity_key_id \/
       pending.f_server_binding.f_identity_public_key <> current.f_identity_public_key })
    (availability:t_KeyIdAvailability)
  : Lemma
      (server_prepare_commit state pending current availability ==
       Core_models.Result.Result_Err RegistrationError_IdentityMismatch)
  = ()

let occupied_server_key_id_is_rejected
    (state:t_ServerState {
       state.f_last_key_id <> Core_models.Num.impl_u64__MAX })
    (pending:t_PendingServerRegistration)
    (current:t_ServerBinding {
       pending.f_server_binding == current })
  : Lemma
      (server_prepare_commit state pending current KeyIdAvailability_Occupied ==
       Core_models.Result.Result_Err RegistrationError_KeyIdCollision)
  = ()

/// A truthful `Available` refinement creates exactly one unpublished
/// candidate with the checked next ID and the exact associated data.
let available_server_key_id_candidate_shape
    (state:t_ServerState {
       state.f_last_key_id <> Core_models.Num.impl_u64__MAX })
    (pending:t_PendingServerRegistration)
    (current:t_ServerBinding {
       pending.f_server_binding == current })
  : Lemma
      (match server_prepare_commit state pending current KeyIdAvailability_Available with
       | Core_models.Result.Result_Ok candidate ->
           candidate.f_previous_state == state /\
           candidate.f_next_state.f_last_key_id == candidate.f_key_id /\
           v candidate.f_key_id == v state.f_last_key_id + 1 /\
           candidate.f_beacon_identity_public_key ==
             pending.f_beacon_identity_public_key /\
           candidate.f_server_identity_public_key == current.f_identity_public_key /\
           candidate.f_server_identity_key_id == current.f_identity_key_id /\
           candidate.f_ephemeral_public_key == pending.f_ephemeral_public_key /\
           candidate.f_kem_ciphertext == pending.f_kem_ciphertext /\
           candidate.f_associated_data ==
             build_associated_data current.f_identity_public_key
               pending.f_beacon_identity_public_key
       | Core_models.Result.Result_Err _ -> False)
  = ()

/// Commit publishes exactly the candidate's next counter and peer; abort
/// restores the exact previous active state.
let server_commit_shape (candidate:t_ServerRegistrationCandidate)
  : Lemma
      (let committed_state, peer = server_commit candidate in
       committed_state == candidate.f_next_state /\
       peer.f_key_id == candidate.f_key_id /\
       peer.f_identity_public_key == candidate.f_beacon_identity_public_key /\
       peer.f_associated_data == candidate.f_associated_data)
  = ()

let server_abort_is_state_neutral (candidate:t_ServerRegistrationCandidate)
  : Lemma (server_abort_candidate candidate == candidate.f_previous_state)
  = ()

/// End-to-end protocol-core correspondence for an honest successful run.  The
/// primitive relation, authenticated identities, truthful Fresh/Available
/// lookups, and non-exhausted local counter are explicit preconditions.  The
/// server's binding is then authenticated by the beacon typestate before both
/// roles commit, yielding the same published peer ID.
let conditional_honest_run_correspondence
    (beacon_state:t_BeaconInitSent)
    (server_state:t_ServerState {
       server_state.f_last_key_id <> Core_models.Num.impl_u64__MAX })
    (registration:t_VerifiedInitKex {
       registration.f_beacon_identity_public_key ==
         beacon_state.f_beacon_identity_public_key })
    (server_binding:t_ServerBinding)
    (coins:t_ServerCoins)
    (beacon_secrets:t_PqxdhSharedSecrets {
       valid_shared_secrets beacon_secrets })
    (server_secrets:t_PqxdhSharedSecrets {
       valid_shared_secrets server_secrets /\
       honest_shared_secrets beacon_secrets server_secrets })
  : Lemma
      (let next_id = server_state.f_last_key_id +! mk_u64 1 in
       let beacon_inputs =
         ({
            f_expected_server_identity = server_binding.f_identity_public_key;
            f_response_server_identity = server_binding.f_identity_public_key;
            f_assigned_key_id = next_id;
            f_shared_secrets = beacon_secrets
          }
          <: t_BeaconFinishInputs) in
       match beacon_prepare_finish beacon_state beacon_inputs with
       | Core_models.Result.Result_Ok beacon_candidate ->
           (match
              server_accept server_state registration RegistrationStatus_Fresh
                server_binding coins server_secrets
            with
            | Core_models.Result.Result_Ok (_, pending) ->
                (match
                   server_prepare_commit server_state pending server_binding
                     KeyIdAvailability_Available
                 with
                 | Core_models.Result.Result_Ok server_candidate ->
                     beacon_candidate.f_root_key_input == pending.f_root_key_input /\
                     beacon_candidate.f_associated_data ==
                       server_candidate.f_associated_data /\
                     beacon_candidate.f_assigned_key_id == server_candidate.f_key_id /\
                     (impl_BeaconRegistrationCandidate__key_id_binding
                        beacon_candidate).f_bytes ==
                       (impl_ServerRegistrationCandidate__key_id_binding
                          server_candidate).f_bytes /\
                     (impl_BeaconRegistrationCandidate__ratchet_initialization
                        beacon_candidate).f_send_offset ==
                       (impl_ServerRegistrationCandidate__ratchet_initialization
                          server_candidate).f_receive_offset /\
                     (impl_BeaconRegistrationCandidate__ratchet_initialization
                        beacon_candidate).f_receive_offset ==
                       (impl_ServerRegistrationCandidate__ratchet_initialization
                          server_candidate).f_send_offset /\
                     (match
                        authenticate_registration_key_id_binding
                          beacon_candidate
                          (impl_ServerRegistrationCandidate__key_id_binding
                             server_candidate).f_bytes
                      with
                      | Core_models.Result.Result_Ok authenticated ->
                          let beacon_established = beacon_commit authenticated in
                          let committed_state, peer = server_commit server_candidate in
                          authenticated.f_candidate == beacon_candidate /\
                          beacon_established.f_server_key_id ==
                            beacon_candidate.f_server_key_id /\
                          beacon_established.f_assigned_key_id == peer.f_key_id /\
                          committed_state == server_candidate.f_next_state /\
                          peer.f_identity_public_key ==
                            beacon_state.f_beacon_identity_public_key /\
                          peer.f_associated_data == beacon_candidate.f_associated_data
                      | Core_models.Result.Result_Err _ -> False)
                 | Core_models.Result.Result_Err _ -> False)
            | Core_models.Result.Result_Err _ -> False)
       | Core_models.Result.Result_Err _ -> False)
  = ()
