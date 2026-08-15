/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_core.Pqxdh.Lemmas

open Rust_primitives.Integers
open Rust_primitives.Arrays
open Beaconcrypt_core.Pqxdh
open Beaconcrypt_core.Ratchet
open Beaconcrypt_core.Ratchet.Control
open Beaconcrypt_core.Ratchet.Refined
open Beaconcrypt_core.Ratchet.Lemmas

friend Beaconcrypt_core.Ratchet
friend Beaconcrypt_core.Ratchet.Control
friend Beaconcrypt_core.Ratchet.Refined
friend Beaconcrypt_core.Ratchet.Lemmas

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

/// Algorithm/type markers occupy the low byte domain and X25519 role markers
/// occupy the high byte domain.  All concrete markers are disjoint.
let key_type_and_role_markers_are_disjoint (_:Prims.unit)
  : Lemma
      (v_SIGN_TYPE_ED25519 == mk_u8 1 /\
       v_KEM_TYPE_MLKEM768 == mk_u8 3 /\
       v_KEM_TYPE_X25519 == mk_u8 4 /\
       v_KEY_ROLE_PREKEY == mk_u8 128 /\
       v_KEY_ROLE_ONE_TIME == mk_u8 129 /\
       v_SIGN_TYPE_ED25519 <> v_KEM_TYPE_MLKEM768 /\
       v_SIGN_TYPE_ED25519 <> v_KEM_TYPE_X25519 /\
       v_KEM_TYPE_MLKEM768 <> v_KEM_TYPE_X25519 /\
       v_SIGN_TYPE_ED25519 <> v_KEY_ROLE_PREKEY /\
       v_SIGN_TYPE_ED25519 <> v_KEY_ROLE_ONE_TIME /\
       v_KEM_TYPE_MLKEM768 <> v_KEY_ROLE_PREKEY /\
       v_KEM_TYPE_MLKEM768 <> v_KEY_ROLE_ONE_TIME /\
       v_KEM_TYPE_X25519 <> v_KEY_ROLE_PREKEY /\
       v_KEM_TYPE_X25519 <> v_KEY_ROLE_ONE_TIME /\
       v_KEY_ROLE_PREKEY <> v_KEY_ROLE_ONE_TIME)
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

let x25519_key_tag_is_exact
    (role:u8)
    (key:t_Array u8 (mk_usize 32))
  : Lemma
      (Seq.index (tag_x25519_key role key) 0 == v_KEM_TYPE_X25519 /\
       Seq.index (tag_x25519_key role key) 1 == role /\
       Seq.slice (tag_x25519_key role key) 2 34 == key)
  =
  let type_tagged =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 34))
      (mk_usize 0)
      v_KEM_TYPE_X25519 in
  let initialized =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      type_tagged
      (mk_usize 1)
      role in
  FStar.Seq.Base.lemma_index_slice initialized 0 2 0;
  FStar.Seq.Base.lemma_index_slice initialized 0 2 1;
  FStar.Seq.Base.lemma_index_slice (tag_x25519_key role key) 0 2 0;
  FStar.Seq.Base.lemma_index_slice (tag_x25519_key role key) 0 2 1

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

let x25519_key_tag_round_trip
    (role:u8)
    (key:t_Array u8 (mk_usize 32))
  : Lemma
      (untag_x25519_key (tag_x25519_key role key) role ==
       Core_models.Option.Option_Some key)
  = x25519_key_tag_is_exact role key

/// A valid key signed for one X25519 field cannot validate in the other.
let x25519_key_roles_are_enforced (key:t_Array u8 (mk_usize 32))
  : Lemma
      (untag_x25519_key
         (tag_x25519_key v_KEY_ROLE_PREKEY key)
         v_KEY_ROLE_ONE_TIME == Core_models.Option.Option_None /\
       untag_x25519_key
         (tag_x25519_key v_KEY_ROLE_ONE_TIME key)
         v_KEY_ROLE_PREKEY == Core_models.Option.Option_None)
  =
  x25519_key_tag_is_exact v_KEY_ROLE_PREKEY key;
  x25519_key_tag_is_exact v_KEY_ROLE_ONE_TIME key

let mlkem768_key_tag_round_trip (key:t_Array u8 (mk_usize 1184))
  : Lemma
      (untag_mlkem768_key (tag_mlkem768_key key) ==
       Core_models.Option.Option_Some key)
  = mlkem768_key_tag_is_exact key

/// A message emitted by `beacon_start` validates to exactly the public
/// material from which it was constructed and carries both fields of the
/// configured server binding into the pending beacon state.
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
           started.f_state.f_expected_server_binding.f_identity_public_key ==
             state.f_expected_server_binding.f_identity_public_key /\
           started.f_state.f_expected_server_binding.f_identity_key_id ==
             state.f_expected_server_binding.f_identity_key_id /\
           started.f_state.f_beacon_identity_public_key == inputs.f_identity_public_key
       | Core_models.Result.Result_Err _ -> False)
  =
  sign_key_tag_round_trip inputs.f_identity_public_key;
  x25519_key_tag_round_trip v_KEY_ROLE_PREKEY inputs.f_prekey_public_key;
  x25519_key_tag_round_trip v_KEY_ROLE_ONE_TIME coins.f_one_time_public_key;
  x25519_key_roles_are_enforced inputs.f_prekey_public_key;
  x25519_key_roles_are_enforced coins.f_one_time_public_key;
  mlkem768_key_tag_round_trip inputs.f_pq_public_key

/// The consuming Fresh-to-InitSent transition preserves the configured trust
/// anchor as separate public-key and numeric-ID facts.
let beacon_start_preserves_expected_server_binding
    (state:t_BeaconFresh)
    (inputs:t_BeaconStartInputs)
    (coins:t_BeaconCoins)
  : Lemma
      (let started = beacon_start state inputs coins in
       started.f_state.f_expected_server_binding.f_identity_public_key ==
         state.f_expected_server_binding.f_identity_public_key /\
       started.f_state.f_expected_server_binding.f_identity_key_id ==
         state.f_expected_server_binding.f_identity_key_id)
  = ()

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

/// Equal verified root-input transcripts remain equal under one fixed pure 32-byte root derivation. This bridge does not claim or model concrete HKDF semantics.
let equal_root_inputs_derive_same_fixed_root
    (beacon_root:t_RootKeyInput)
    (server_root:t_RootKeyInput { server_root == beacon_root })
    (derive_root:t_RootKeyInput -> t_Array u8 (mk_usize 32))
  : Lemma
      (derive_root beacon_root == derive_root server_root)
  = ()

/// An authenticated beacon candidate and the corresponding pending server registration derive one common 32-byte root under the same fixed pure derivation when their verified root-input transcripts agree.
let authenticated_registration_derives_common_fixed_root
    (authenticated:t_AuthenticatedBeaconRegistration)
    (pending:t_PendingServerRegistration {
       authenticated.f_candidate.f_root_key_input == pending.f_root_key_input })
    (derive_root:t_RootKeyInput -> t_Array u8 (mk_usize 32))
  : Lemma
      (derive_root authenticated.f_candidate.f_root_key_input ==
       derive_root pending.f_root_key_input)
  = equal_root_inputs_derive_same_fixed_root
      authenticated.f_candidate.f_root_key_input pending.f_root_key_input
      derive_root

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

/// A response public key that differs from the key stored in BeaconInitSent
/// is rejected before root-input construction can yield a candidate.
let beacon_response_identity_mismatch_is_rejected
    (state:t_BeaconInitSent)
    (inputs:t_BeaconFinishInputs {
       inputs.f_response_server_identity <>
         state.f_expected_server_binding.f_identity_public_key })
  : Lemma
      (beacon_prepare_finish state inputs ==
       Core_models.Result.Result_Err RegistrationError_IdentityMismatch)
  = ()

/// A matching response either propagates root-input failure or constructs a
/// candidate carrying both expected binding fields and AD derived from the
/// stored server public key and the pending beacon identity.
let beacon_successful_finish_preserves_binding_and_ad
    (state:t_BeaconInitSent)
    (inputs:t_BeaconFinishInputs {
       inputs.f_response_server_identity ==
         state.f_expected_server_binding.f_identity_public_key })
  : Lemma
      (match beacon_prepare_finish state inputs,
             build_root_key_input inputs.f_shared_secrets with
       | Core_models.Result.Result_Ok
           (candidate:t_BeaconRegistrationCandidate),
         Core_models.Result.Result_Ok (root:t_RootKeyInput) ->
           candidate.f_server_binding.f_identity_public_key ==
             state.f_expected_server_binding.f_identity_public_key /\
           candidate.f_server_binding.f_identity_key_id ==
             state.f_expected_server_binding.f_identity_key_id /\
           candidate.f_assigned_key_id == inputs.f_assigned_key_id /\
           candidate.f_root_key_input == root /\
           candidate.f_associated_data ==
             build_associated_data
               candidate.f_server_binding.f_identity_public_key
               state.f_beacon_identity_public_key /\
           candidate.f_associated_data ==
             build_associated_data
               state.f_expected_server_binding.f_identity_public_key
               state.f_beacon_identity_public_key
       | Core_models.Result.Result_Err finish_error,
         Core_models.Result.Result_Err root_error -> finish_error == root_error
       | _ -> False)
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

/// The extracted initial adapter applies the opaque primitive to a core-owned request for the exact root and fixed label, splits both fixed halves, and selects complementary role directions.
let initial_ratchet_chains_use_exact_root_and_directions
    (root:t_Array u8 (mk_usize 32))
    (kdf:t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 64))
  : Lemma
      (let request = impl_SymmetricRatchetKdfRequest__new root in
       let output = kdf request in
       let beacon = derive_initial_ratchet_chains
         root (beacon_ratchet_initialization ()) kdf in
       let server = derive_initial_ratchet_chains
         root (server_ratchet_initialization ()) kdf in
       request.f_input == root /\
       request.f_info == v_SYM_RATCHET_INFO /\
       (forall (i:nat{i < 32}).
          Seq.index beacon.f_receive_chain.f_bytes i ==
            Seq.index output i) /\
       (forall (i:nat{i < 32}).
          Seq.index beacon.f_send_chain.f_bytes i ==
            Seq.index output (i + 32)) /\
       beacon.f_send_chain.f_bytes == server.f_receive_chain.f_bytes /\
       beacon.f_receive_chain.f_bytes == server.f_send_chain.f_bytes)
  = ()

/// Pair both production-specialized role kernels with the exact complementary origins derived from one agreed 32-byte root and one fixed pair of pure KDF executors.
let concrete_session
    (agreed_root:t_Array u8 (mk_usize 32))
    (initial_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 64))
    (ratchet_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 76))
    (beacon server:t_ConcreteRatchetKernel)
  : prop =
  let beacon_initial =
    derive_beacon_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  let server_initial =
    derive_server_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  concrete_reachable
    beacon_initial.f_refined.f_send_chain
    beacon_initial.f_refined.f_receive_chain beacon /\
  concrete_reachable
    server_initial.f_refined.f_send_chain
    server_initial.f_refined.f_receive_chain server

/// The two role-specific initial-kernel constructors bind the same lifetime executor to complementary concrete directional chains.
let concrete_initial_kernels_are_complementary
    (agreed_root:t_Array u8 (mk_usize 32))
    (initial_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 64))
    (ratchet_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 76))
  : Lemma
      (let beacon =
         derive_beacon_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
       let server =
         derive_server_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
       beacon.f_refined.f_send_chain == server.f_refined.f_receive_chain /\
       beacon.f_refined.f_receive_chain == server.f_refined.f_send_chain)
  =
  initial_ratchet_chains_use_exact_root_and_directions
    agreed_root initial_kdf;
  let beacon =
    derive_beacon_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  let server =
    derive_server_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  ratchet_chain_bytes_extensionality
    beacon.f_refined.f_send_chain.f_chain
    server.f_refined.f_receive_chain.f_chain;
  ratchet_chain_bytes_extensionality
    beacon.f_refined.f_receive_chain.f_chain
    server.f_refined.f_send_chain.f_chain;
  concrete_ratchet_chain_extensionality
    beacon.f_refined.f_send_chain server.f_refined.f_receive_chain;
  concrete_ratchet_chain_extensionality
    beacon.f_refined.f_receive_chain server.f_refined.f_send_chain

/// Fresh complementary concrete kernels are reachable under the same core-fixed step for their complete lifetimes.
let concrete_initial_kernels_are_reachable
    (agreed_root:t_Array u8 (mk_usize 32))
    (initial_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 64))
    (ratchet_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 76))
  : Lemma
      (concrete_session agreed_root initial_kdf ratchet_kdf
        (derive_beacon_ratchet_kernel
          agreed_root initial_kdf ratchet_kdf)
        (derive_server_ratchet_kernel
          agreed_root initial_kdf ratchet_kdf))
  =
  let beacon_chains = derive_initial_ratchet_chains
    agreed_root (beacon_ratchet_initialization ()) initial_kdf in
  let server_chains = derive_initial_ratchet_chains
    agreed_root (server_ratchet_initialization ()) initial_kdf in
  concrete_kernel_new_is_reachable
    beacon_chains.f_send_chain beacon_chains.f_receive_chain ratchet_kdf;
  concrete_kernel_new_is_reachable
    server_chains.f_send_chain server_chains.f_receive_chain ratchet_kdf

/// At every logical sequence, beacon-send material equals server-receive material, while server-send material equals beacon-receive material.
let concrete_directional_materials_agree
    (agreed_root:t_Array u8 (mk_usize 32))
    (initial_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 64))
    (ratchet_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 76))
    (sequence:nat)
  : Lemma
      (let beacon =
         derive_beacon_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
       let server =
         derive_server_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         beacon.f_refined.f_send_chain concrete_ratchet_step sequence ==
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         server.f_refined.f_receive_chain concrete_ratchet_step sequence /\
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         server.f_refined.f_send_chain concrete_ratchet_step sequence ==
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         beacon.f_refined.f_receive_chain concrete_ratchet_step sequence)
  = concrete_initial_kernels_are_complementary
      agreed_root initial_kdf ratchet_kdf

/// Authentication-linked root agreement composes with the role-bound constructors: the fresh kernels form one concrete session and their opposing directional materials agree at every arbitrary sequence.
let authenticated_registrations_establish_concrete_session
    (authenticated:t_AuthenticatedBeaconRegistration)
    (pending:t_PendingServerRegistration {
       authenticated.f_candidate.f_root_key_input == pending.f_root_key_input })
    (derive_root:t_RootKeyInput -> t_Array u8 (mk_usize 32))
    (initial_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 64))
    (ratchet_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 76))
    (sequence:nat)
  : Lemma
      (let common_root =
         derive_root authenticated.f_candidate.f_root_key_input in
       let pending_root = derive_root pending.f_root_key_input in
       let beacon =
         impl_BeaconRegistrationCandidate__derive_ratchet_kernel
           authenticated.f_candidate common_root initial_kdf ratchet_kdf in
       let server =
         derive_server_ratchet_kernel pending_root initial_kdf ratchet_kdf in
       common_root == pending_root /\
       concrete_session common_root initial_kdf ratchet_kdf beacon server /\
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         beacon.f_refined.f_send_chain concrete_ratchet_step sequence ==
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         server.f_refined.f_receive_chain concrete_ratchet_step sequence /\
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         server.f_refined.f_send_chain concrete_ratchet_step sequence ==
       material_at #t_ConcreteRatchetChain #t_RatchetMaterial
         beacon.f_refined.f_receive_chain concrete_ratchet_step sequence)
  =
  authenticated_registration_derives_common_fixed_root
    authenticated pending derive_root;
  let common_root =
    derive_root authenticated.f_candidate.f_root_key_input in
  concrete_initial_kernels_are_reachable
    common_root initial_kdf ratchet_kdf;
  concrete_directional_materials_agree
    common_root initial_kdf ratchet_kdf sequence

/// A beacon seal followed by any server open attempt preserves the paired concrete-session invariant on every callback outcome.
let beacon_seal_server_open_preserves_concrete_session
    (#v_SealContext #v_Ciphertext #v_OpenContext #v_Plaintext:Type0)
    (agreed_root:t_Array u8 (mk_usize 32))
    (initial_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 64))
    (ratchet_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 76))
    (beacon:t_ConcreteRatchetKernel)
    (server:t_ConcreteRatchetKernel {
       concrete_session agreed_root initial_kdf ratchet_kdf beacon server })
    (target:u64)
    (seal_context:v_SealContext)
    (seal:t_RatchetMaterial -> u64 -> v_SealContext ->
      Core_models.Option.t_Option v_Ciphertext)
    (open_context:v_OpenContext)
    (open_callback:t_RatchetMaterial -> u64 -> v_OpenContext ->
      Core_models.Option.t_Option v_Plaintext)
  : Lemma
      (let beacon', _ = concrete_seal_next beacon seal_context seal in
       let server', _ =
         concrete_open_and_finish server target open_context open_callback in
       concrete_session agreed_root initial_kdf ratchet_kdf beacon' server')
  =
  let beacon_initial =
    derive_beacon_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  let server_initial =
    derive_server_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  concrete_seal_next_preserves_reachability
    beacon_initial.f_refined.f_send_chain
    beacon_initial.f_refined.f_receive_chain beacon seal_context seal;
  concrete_open_and_finish_preserves_reachability
    server_initial.f_refined.f_send_chain
    server_initial.f_refined.f_receive_chain server target
    open_context open_callback

/// A server seal followed by any beacon open attempt preserves the paired concrete-session invariant on every callback outcome.
let server_seal_beacon_open_preserves_concrete_session
    (#v_SealContext #v_Ciphertext #v_OpenContext #v_Plaintext:Type0)
    (agreed_root:t_Array u8 (mk_usize 32))
    (initial_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 64))
    (ratchet_kdf:t_SymmetricRatchetKdfRequest ->
      t_Array u8 (mk_usize 76))
    (beacon:t_ConcreteRatchetKernel)
    (server:t_ConcreteRatchetKernel {
       concrete_session agreed_root initial_kdf ratchet_kdf beacon server })
    (target:u64)
    (seal_context:v_SealContext)
    (seal:t_RatchetMaterial -> u64 -> v_SealContext ->
      Core_models.Option.t_Option v_Ciphertext)
    (open_context:v_OpenContext)
    (open_callback:t_RatchetMaterial -> u64 -> v_OpenContext ->
      Core_models.Option.t_Option v_Plaintext)
  : Lemma
      (let server', _ = concrete_seal_next server seal_context seal in
       let beacon', _ =
         concrete_open_and_finish beacon target open_context open_callback in
       concrete_session agreed_root initial_kdf ratchet_kdf beacon' server')
  =
  let beacon_initial =
    derive_beacon_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  let server_initial =
    derive_server_ratchet_kernel agreed_root initial_kdf ratchet_kdf in
  concrete_seal_next_preserves_reachability
    server_initial.f_refined.f_send_chain
    server_initial.f_refined.f_receive_chain server seal_context seal;
  concrete_open_and_finish_preserves_reachability
    beacon_initial.f_refined.f_send_chain
    beacon_initial.f_refined.f_receive_chain beacon target
    open_context open_callback

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
         candidate.f_server_binding.f_identity_key_id
         (impl_BeaconRegistrationCandidate__key_id_binding candidate).f_bytes ==
       Core_models.Result.Result_Ok
         ({ f_candidate = candidate } <: t_AuthenticatedBeaconRegistration))
  = ()

let mismatched_authenticated_server_key_id_is_rejected
    (candidate:t_BeaconRegistrationCandidate)
    (authenticated_server_key_id:u64 {
       authenticated_server_key_id <>
         candidate.f_server_binding.f_identity_key_id })
    (authenticated_binding:t_Array u8 (mk_usize 8))
  : Lemma
      (authenticate_registration_key_id_binding candidate
         authenticated_server_key_id authenticated_binding ==
       Core_models.Result.Result_Err RegistrationError_IdentityMismatch)
  = ()

let mismatched_key_id_binding_is_rejected
    (candidate:t_BeaconRegistrationCandidate)
    (authenticated_binding:t_Array u8 (mk_usize 8) {
       authenticated_binding <>
         (impl_BeaconRegistrationCandidate__key_id_binding candidate).f_bytes })
  : Lemma
      (authenticate_registration_key_id_binding candidate
         candidate.f_server_binding.f_identity_key_id authenticated_binding ==
       Core_models.Result.Result_Err RegistrationError_KeyIdMismatch)
  = ()

/// Only the authenticated typestate can reach commit, and commit publishes
/// both fields of the candidate's server binding and its assigned peer ID.
let beacon_commit_preserves_authenticated_ids
    (authenticated:t_AuthenticatedBeaconRegistration)
  : Lemma
      ((beacon_commit authenticated).f_server_binding.f_identity_public_key ==
         authenticated.f_candidate.f_server_binding.f_identity_public_key /\
       (beacon_commit authenticated).f_server_binding.f_identity_key_id ==
         authenticated.f_candidate.f_server_binding.f_identity_key_id /\
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

/// Successful response-key checking followed by successful sender-ID and
/// assigned-ID authentication derives agreement with the accepting server
/// candidate; no equality between its binding fields and the stored beacon
/// binding is assumed.  The derived agreement is retained by the
/// authenticated typestate and established beacon state.
let successful_beacon_acceptance_implies_server_binding_agreement
    (state:t_BeaconInitSent)
    (accepting_server_candidate:t_ServerRegistrationCandidate)
    (secrets:t_PqxdhSharedSecrets)
  : Lemma
      (let inputs =
         ({
            f_response_server_identity =
              accepting_server_candidate.f_server_identity_public_key;
            f_assigned_key_id = accepting_server_candidate.f_key_id;
            f_shared_secrets = secrets
          }
          <: t_BeaconFinishInputs) in
       match beacon_prepare_finish state inputs with
       | Core_models.Result.Result_Ok
           (candidate:t_BeaconRegistrationCandidate) ->
           (match
              authenticate_registration_key_id_binding candidate
                accepting_server_candidate.f_server_identity_key_id
                (impl_ServerRegistrationCandidate__key_id_binding
                   accepting_server_candidate).f_bytes
            with
            | Core_models.Result.Result_Ok
                (authenticated:t_AuthenticatedBeaconRegistration) ->
                let established = beacon_commit authenticated in
                state.f_expected_server_binding.f_identity_public_key ==
                  accepting_server_candidate.f_server_identity_public_key /\
                state.f_expected_server_binding.f_identity_key_id ==
                  accepting_server_candidate.f_server_identity_key_id /\
                candidate.f_server_binding.f_identity_public_key ==
                  accepting_server_candidate.f_server_identity_public_key /\
                candidate.f_server_binding.f_identity_key_id ==
                  accepting_server_candidate.f_server_identity_key_id /\
                authenticated.f_candidate.f_server_binding.f_identity_public_key ==
                  accepting_server_candidate.f_server_identity_public_key /\
                authenticated.f_candidate.f_server_binding.f_identity_key_id ==
                  accepting_server_candidate.f_server_identity_key_id /\
                established.f_server_binding.f_identity_public_key ==
                  accepting_server_candidate.f_server_identity_public_key /\
                established.f_server_binding.f_identity_key_id ==
                  accepting_server_candidate.f_server_identity_key_id /\
                candidate.f_assigned_key_id == accepting_server_candidate.f_key_id /\
                authenticated.f_candidate.f_assigned_key_id ==
                  accepting_server_candidate.f_key_id /\
                established.f_assigned_key_id == accepting_server_candidate.f_key_id
            | Core_models.Result.Result_Err _ -> True)
       | Core_models.Result.Result_Err _ -> True)
  = ()

/// End-to-end beaconcrypt-core correspondence for an honest successful run.  The
/// primitive relation, authenticated identities, truthful Fresh/Available
/// lookups, non-exhausted local counter, and stored/accepting server-binding
/// equality are explicit preconditions.  The transitions check the response
/// public key and authenticated sender ID and preserve both binding fields
/// through commit, yielding the same published peer ID.  The successful server
/// candidate branch invokes the acceptance-implies-agreement result above.
let conditional_honest_run_correspondence
    (beacon_state:t_BeaconInitSent)
    (server_state:t_ServerState {
       server_state.f_last_key_id <> Core_models.Num.impl_u64__MAX })
    (registration:t_VerifiedInitKex {
       registration.f_beacon_identity_public_key ==
         beacon_state.f_beacon_identity_public_key })
    (server_binding:t_ServerBinding {
       server_binding.f_identity_public_key ==
         beacon_state.f_expected_server_binding.f_identity_public_key /\
       server_binding.f_identity_key_id ==
         beacon_state.f_expected_server_binding.f_identity_key_id })
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
                     beacon_candidate.f_server_binding.f_identity_public_key ==
                       server_candidate.f_server_identity_public_key /\
                     beacon_candidate.f_server_binding.f_identity_key_id ==
                       server_candidate.f_server_identity_key_id /\
                     server_candidate.f_server_identity_public_key ==
                       beacon_state.f_expected_server_binding.f_identity_public_key /\
                     server_candidate.f_server_identity_key_id ==
                       beacon_state.f_expected_server_binding.f_identity_key_id /\
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
                          server_candidate.f_server_identity_key_id
                          (impl_ServerRegistrationCandidate__key_id_binding
                             server_candidate).f_bytes
                      with
                      | Core_models.Result.Result_Ok authenticated ->
                          let beacon_established = beacon_commit authenticated in
                          let committed_state, peer = server_commit server_candidate in
                          authenticated.f_candidate == beacon_candidate /\
                          beacon_established.f_server_binding.f_identity_public_key ==
                            server_candidate.f_server_identity_public_key /\
                          beacon_established.f_server_binding.f_identity_key_id ==
                            server_candidate.f_server_identity_key_id /\
                          beacon_established.f_server_binding.f_identity_public_key ==
                            beacon_state.f_expected_server_binding.f_identity_public_key /\
                          beacon_established.f_server_binding.f_identity_key_id ==
                            beacon_state.f_expected_server_binding.f_identity_key_id /\
                          beacon_established.f_assigned_key_id == peer.f_key_id /\
                          committed_state == server_candidate.f_next_state /\
                          peer.f_identity_public_key ==
                            beacon_state.f_beacon_identity_public_key /\
                          peer.f_associated_data == beacon_candidate.f_associated_data
                      | Core_models.Result.Result_Err _ -> False)
                 | Core_models.Result.Result_Err _ -> False)
            | Core_models.Result.Result_Err _ -> False)
       | Core_models.Result.Result_Err _ -> False)
  =
  let next_id = server_state.f_last_key_id +! mk_u64 1 in
  let beacon_inputs =
    ({
       f_response_server_identity = server_binding.f_identity_public_key;
       f_assigned_key_id = next_id;
       f_shared_secrets = beacon_secrets
     }
     <: t_BeaconFinishInputs) in
  match beacon_prepare_finish beacon_state beacon_inputs with
  | Core_models.Result.Result_Ok _ ->
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
                successful_beacon_acceptance_implies_server_binding_agreement
                  beacon_state server_candidate beacon_secrets
            | Core_models.Result.Result_Err _ -> ())
       | Core_models.Result.Result_Err _ -> ())
  | Core_models.Result.Result_Err _ -> ()
