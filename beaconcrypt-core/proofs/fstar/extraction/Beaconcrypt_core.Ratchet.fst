module Beaconcrypt_core.Ratchet
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Fixed width of every symmetric-ratchet root and chain value.
let v_RATCHET_CHAIN_SIZE: usize = mk_usize 32

let v_SYM_RATCHET_INFO: t_Array u8 (mk_usize 41) =
  let list =
    [
      mk_u8 83; mk_u8 121; mk_u8 109; mk_u8 82; mk_u8 97; mk_u8 116; mk_u8 99; mk_u8 104; mk_u8 101;
      mk_u8 116; mk_u8 95; mk_u8 72; mk_u8 75; mk_u8 68; mk_u8 70; mk_u8 95; mk_u8 83; mk_u8 72;
      mk_u8 65; mk_u8 45; mk_u8 53; mk_u8 49; mk_u8 50; mk_u8 95; mk_u8 67; mk_u8 72; mk_u8 65;
      mk_u8 67; mk_u8 72; mk_u8 65; mk_u8 50; mk_u8 48; mk_u8 95; mk_u8 80; mk_u8 79; mk_u8 76;
      mk_u8 89; mk_u8 49; mk_u8 51; mk_u8 48; mk_u8 53
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 41);
  Rust_primitives.Hax.array_of_list 41 list

/// Fixed-width symmetric-ratchet chain bytes owned by the extracted boundary.
type t_RatchetChain = { f_bytes:t_Array u8 (mk_usize 32) }

let impl_RatchetChain__from_bytes (bytes: t_Array u8 (mk_usize 32)) : t_RatchetChain =
  { f_bytes = bytes } <: t_RatchetChain

let impl_RatchetChain__as_bytes (self: t_RatchetChain) : t_Array u8 (mk_usize 32) = self.f_bytes

let impl_RatchetChain__into_bytes (self: t_RatchetChain) : t_Array u8 (mk_usize 32) = self.f_bytes

/// Fixed-width symmetric-ratchet message-key bytes owned by the extracted boundary.
type t_RatchetKey = { f_bytes:t_Array u8 (mk_usize 32) }

let impl_RatchetKey__from_bytes (bytes: t_Array u8 (mk_usize 32)) : t_RatchetKey =
  { f_bytes = bytes } <: t_RatchetKey

let impl_RatchetKey__as_bytes (self: t_RatchetKey) : t_Array u8 (mk_usize 32) = self.f_bytes

let impl_RatchetKey__into_bytes (self: t_RatchetKey) : t_Array u8 (mk_usize 32) = self.f_bytes

/// Fixed-width symmetric-ratchet AEAD nonce bytes owned by the extracted boundary.
type t_RatchetNonce = { f_bytes:t_Array u8 (mk_usize 12) }

let impl_RatchetNonce__from_bytes (bytes: t_Array u8 (mk_usize 12)) : t_RatchetNonce =
  { f_bytes = bytes } <: t_RatchetNonce

let impl_RatchetNonce__as_bytes (self: t_RatchetNonce) : t_Array u8 (mk_usize 12) = self.f_bytes

let impl_RatchetNonce__into_bytes (self: t_RatchetNonce) : t_Array u8 (mk_usize 12) = self.f_bytes

/// Fixed-width key and nonce produced by one symmetric-ratchet step.
type t_RatchetMaterial = {
  f_key:t_RatchetKey;
  f_nonce:t_RatchetNonce
}

let impl_RatchetMaterial__key (self: t_RatchetMaterial) : t_RatchetKey = self.f_key

let impl_RatchetMaterial__nonce (self: t_RatchetMaterial) : t_RatchetNonce = self.f_nonce

/// Core-owned invocation of the symmetric-ratchet KDF domain.
/// Both fields are private so an executor can read but cannot alter the exact
/// input or protocol label selected by the core transition that created it.
type t_SymmetricRatchetKdfRequest = {
  f_input:t_Array u8 (mk_usize 32);
  f_info:t_Array u8 (mk_usize 41)
}

let impl_SymmetricRatchetKdfRequest__new (input: t_Array u8 (mk_usize 32))
    : t_SymmetricRatchetKdfRequest =
  { f_input = input; f_info = v_SYM_RATCHET_INFO } <: t_SymmetricRatchetKdfRequest

/// Proof-visible owned partition of one symmetric-ratchet HKDF expansion.
type t_RatchetKdfOutput = {
  f_key:t_RatchetKey;
  f_next_chain:t_RatchetChain;
  f_nonce:t_RatchetNonce
}

let impl_RatchetKdfOutput__key (self: t_RatchetKdfOutput) : t_RatchetKey = self.f_key

let impl_RatchetKdfOutput__next_chain (self: t_RatchetKdfOutput) : t_RatchetChain =
  self.f_next_chain

let impl_RatchetKdfOutput__nonce (self: t_RatchetKdfOutput) : t_RatchetNonce = self.f_nonce

/// Split `key || next_chain || nonce` into fixed-width values at the protocol's exact offsets.
let split_ratchet_kdf_output (output: t_Array u8 (mk_usize 76)) : t_RatchetKdfOutput =
  let key:t_Array u8 (mk_usize 32) =
    Core_models.Array.from_fn #u8
      (mk_usize 32)
      #(usize -> u8)
      (fun i ->
          let i:usize = i in
          output.[ i ] <: u8)
  in
  let next_chain:t_Array u8 (mk_usize 32) =
    Core_models.Array.from_fn #u8
      (mk_usize 32)
      #(usize -> u8)
      (fun i ->
          let i:usize = i in
          output.[ i +! Beaconcrypt_core.Commitment.v_AEAD_KEY_SIZE <: usize ] <: u8)
  in
  let nonce:t_Array u8 (mk_usize 12) =
    Core_models.Array.from_fn #u8
      (mk_usize 12)
      #(usize -> u8)
      (fun i ->
          let i:usize = i in
          output.[ (i +! Beaconcrypt_core.Commitment.v_AEAD_KEY_SIZE <: usize) +!
            v_RATCHET_CHAIN_SIZE
            <:
            usize ]
          <:
          u8)
  in
  {
    f_key = impl_RatchetKey__from_bytes key;
    f_next_chain = impl_RatchetChain__from_bytes next_chain;
    f_nonce = impl_RatchetNonce__from_bytes nonce
  }
  <:
  t_RatchetKdfOutput
