import Mathlib.Data.Nat.Notation

/-!
# BeaconCrypt modified PQXDH — primitives, domain strings and key encodings

This file is the first part of the *ideal model* of the BeaconCrypt registration /
key-establishment protocol described in `pqxdh_spec.md`.  It fixes

* the byte-string representation used throughout the model (`Pqxdh.Bytes`),
* the little-endian 64-bit encoding `Pqxdh.LE64` (spec §12),
* the two fixed HKDF domain strings `INFO_PQ` and `INFO_R` (spec §3),
* the authenticated public-key encodings `Tag_sig`, `Tag_X` and `Tag_PQ` together
  with their parsers and the domain-separation facts they provide (spec §4),
* the interface `Pqxdh.Crypto` of the cryptographic primitives the protocol is
  built from, with the *ideal* assumptions on them (correctness of signatures,
  of the Ed25519→X25519 conversions, X25519 agreement, ML-KEM correctness,
  AEAD correctness, and the output lengths).

Nothing in the model depends on how the primitives are implemented; a concrete
(toy) instance is given at the end of `BeaconcryptCore.Model.Pqxdh.Theorems` to
show that the assumptions are jointly satisfiable, so the model is not vacuous.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Pqxdh

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-- The all-zero 32-byte string, the rejected X25519 output (spec §7). -/
def zero32 : Bytes := List.replicate 32 0

/-- The 32-byte `FF` padding heading the PQXDH transcript (spec §8). -/
def padFF32 : Bytes := List.replicate 32 0xFF

theorem zero32_length : zero32.length = 32 := by simp [zero32]

theorem padFF32_length : padFF32.length = 32 := by simp [padFF32]

/-! ## Little-endian 64-bit encoding (spec §12) -/

/-- `LE64 n` is the little-endian 8-byte encoding of `n` (truncated mod `2^64`). -/
def LE64 (n : ℕ) : Bytes :=
  (List.range 8).map (fun i => UInt8.ofNat (n / 2 ^ (8 * i) % 256))

@[simp] theorem LE64_length (n : ℕ) : (LE64 n).length = 8 := by simp [LE64]

/-- The 64-bit encoding is injective on the range of 64-bit numbers, so the key
identifier carried inside the first encrypted record determines the identifier. -/
theorem LE64_inj {n m : ℕ} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (h : LE64 n = LE64 m) :
    n = m := by
  simp [LE64, List.range_succ] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e : ∀ a b : ℕ, UInt8.ofNat a = UInt8.ofNat b → a % 256 = b % 256 := by
    intro a b hab
    have := congrArg UInt8.toNat hab
    simpa using this
  have H0 := e _ _ h0
  have H1 := e _ _ h1
  have H2 := e _ _ h2
  have H3 := e _ _ h3
  have H4 := e _ _ h4
  have H5 := e _ _ h5
  have H6 := e _ _ h6
  have H7 := e _ _ h7
  omega

/-! ## Fixed HKDF domain strings (spec §3)

`INFO_PQ = "BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768"` (46 bytes) and
`INFO_R = "SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305"` (41 bytes), given as their
ASCII byte encodings. -/

/-- The PQXDH root-derivation domain string, 46 bytes. -/
def INFO_PQ : Bytes :=
  [66, 101, 97, 99, 111, 110, 99, 114, 121, 112, 116, 80, 113, 120, 100, 104, 95, 67,
   85, 82, 86, 69, 50, 53, 53, 49, 57, 95, 83, 72, 65, 45, 53, 49, 50, 95, 77, 76, 45,
   75, 69, 77, 45, 55, 54, 56]

/-- The symmetric-ratchet domain string, 41 bytes. -/
def INFO_R : Bytes :=
  [83, 121, 109, 82, 97, 116, 99, 104, 101, 116, 95, 72, 75, 68, 70, 95, 83, 72, 65, 45,
   53, 49, 50, 95, 67, 72, 65, 67, 72, 65, 50, 48, 95, 80, 79, 76, 89, 49, 51, 48, 53]

theorem INFO_PQ_length : INFO_PQ.length = 46 := rfl

theorem INFO_R_length : INFO_R.length = 41 := rfl

/-- The two domain strings are distinct, so the PQXDH and ratchet expansions are
domain separated. -/
theorem INFO_PQ_ne_INFO_R : INFO_PQ ≠ INFO_R := by decide

/-! ## Authenticated public-key encodings (spec §4) -/

/-- Role byte of the X25519 prekey, `0x80`. -/
def rolePre : UInt8 := 0x80

/-- Role byte of the X25519 one-time key, `0x81`. -/
def roleOtk : UInt8 := 0x81

/-- `Tag_sig(pk) = 0x01 ‖ pk`. -/
def tagSig (pk : Bytes) : Bytes := 0x01 :: pk

/-- `Tag_X(role, pk) = 0x04 ‖ role ‖ pk`. -/
def tagX (role : UInt8) (pk : Bytes) : Bytes := 0x04 :: role :: pk

/-- `Tag_PQ(pk) = 0x03 ‖ pk`. -/
def tagPQ (pk : Bytes) : Bytes := 0x03 :: pk

theorem tagSig_length {pk : Bytes} (h : pk.length = 32) : (tagSig pk).length = 33 := by
  simp [tagSig, h]

theorem tagX_length {role : UInt8} {pk : Bytes} (h : pk.length = 32) :
    (tagX role pk).length = 34 := by simp [tagX, h]

theorem tagPQ_length {pk : Bytes} (h : pk.length = 1184) : (tagPQ pk).length = 1185 := by
  simp [tagPQ, h]

/-- Parse an Ed25519-tagged 32-byte public key. -/
def parseSigTag (b : Bytes) : Option Bytes :=
  match b with
  | (0x01 : UInt8) :: rest => if rest.length = 32 then some rest else none
  | _ => none

/-- Parse an X25519 key tagged with the given role. -/
def parseXTag (role : UInt8) (b : Bytes) : Option Bytes :=
  match b with
  | (0x04 : UInt8) :: r :: rest => if r = role ∧ rest.length = 32 then some rest else none
  | _ => none

/-- Parse an ML-KEM-768 tagged public key. -/
def parsePQTag (b : Bytes) : Option Bytes :=
  match b with
  | (0x03 : UInt8) :: rest => if rest.length = 1184 then some rest else none
  | _ => none

@[simp] theorem parseSigTag_tagSig {pk : Bytes} (h : pk.length = 32) :
    parseSigTag (tagSig pk) = some pk := by simp [parseSigTag, tagSig, h]

@[simp] theorem parseXTag_tagX {role : UInt8} {pk : Bytes} (h : pk.length = 32) :
    parseXTag role (tagX role pk) = some pk := by simp [parseXTag, tagX, h]

@[simp] theorem parsePQTag_tagPQ {pk : Bytes} (h : pk.length = 1184) :
    parsePQTag (tagPQ pk) = some pk := by simp [parsePQTag, tagPQ, h]

/-- A prekey encoding is never accepted as a one-time key encoding: the two X25519
role domains are disjoint (spec §4, §21.3). -/
theorem parseXTag_otk_tagX_pre (pk : Bytes) :
    parseXTag roleOtk (tagX rolePre pk) = none := by
  simp [parseXTag, tagX, rolePre, roleOtk]

/-- Symmetrically, a one-time key encoding is never accepted as a prekey encoding. -/
theorem parseXTag_pre_tagX_otk (pk : Bytes) :
    parseXTag rolePre (tagX roleOtk pk) = none := by
  simp [parseXTag, tagX, rolePre, roleOtk]

/-- The signature-key domain and the X25519 domain are disjoint. -/
theorem tagSig_ne_tagX (pk pk' : Bytes) (role : UInt8) : tagSig pk ≠ tagX role pk' := by
  simp [tagSig, tagX]

/-- The signature-key domain and the ML-KEM domain are disjoint. -/
theorem tagSig_ne_tagPQ (pk pk' : Bytes) : tagSig pk ≠ tagPQ pk' := by
  simp [tagSig, tagPQ]

/-- The X25519 domain and the ML-KEM domain are disjoint. -/
theorem tagX_ne_tagPQ (pk pk' : Bytes) (role : UInt8) : tagX role pk ≠ tagPQ pk' := by
  simp [tagX, tagPQ]

/-- The X25519 encoding determines both the role and the key. -/
theorem tagX_inj {role role' : UInt8} {pk pk' : Bytes} (h : tagX role pk = tagX role' pk') :
    role = role' ∧ pk = pk' := by
  simpa [tagX] using h

/-! ## The cryptographic interface -/

/-- The cryptographic primitives the ideal PQXDH model is parametric in, together with
the ideal assumptions made about them.

`sign` produces libsodium's *attached* signature `signature ‖ message`, and `verify`
returns the message when the attached signature is valid and `none` otherwise.
`xsk`/`xpkConv` are the Ed25519→X25519 secret/public key conversions; the public
conversion may fail, which is modelled by `Option`.  `decap` returns `none` on an
invalid ML-KEM ciphertext, and `aeadOpen` returns `none` on an authentication
failure. -/
structure Crypto where
  /-- Ed25519 public key of a secret key. -/
  edPub : Bytes → Bytes
  /-- Ed25519 attached signature `signature ‖ message`. -/
  sign : Bytes → Bytes → Bytes
  /-- Ed25519 attached-signature verification; returns the signed message. -/
  verify : Bytes → Bytes → Option Bytes
  /-- Ed25519→X25519 secret-key conversion `XSK`. -/
  xsk : Bytes → Bytes
  /-- Ed25519→X25519 public-key conversion `XPK`; may fail. -/
  xpkConv : Bytes → Option Bytes
  /-- X25519 public key of an X25519 secret key. -/
  xpub : Bytes → Bytes
  /-- X25519 scalar multiplication. -/
  x25519 : Bytes → Bytes → Bytes
  /-- ML-KEM-768 public key of a decapsulation key. -/
  kemPub : Bytes → Bytes
  /-- ML-KEM-768 encapsulation from public key and randomness, giving `(ct, ss)`. -/
  encap : Bytes → Bytes → Bytes × Bytes
  /-- ML-KEM-768 decapsulation; `none` on an invalid ciphertext. -/
  decap : Bytes → Bytes → Option Bytes
  /-- `HKDF_512(ikm, info, L)`: extract with an empty salt, then expand to `L` bytes. -/
  hkdf : Bytes → Bytes → ℕ → Bytes
  /-- Detached ChaCha20-Poly1305 sealing: `key`, `nonce`, `ad`, `pt ↦ (ct, tag)`. -/
  aeadSeal : Bytes → Bytes → Bytes → Bytes → Bytes × Bytes
  /-- Detached ChaCha20-Poly1305 opening; `none` on an authentication failure. -/
  aeadOpen : Bytes → Bytes → Bytes → Bytes → Bytes → Option Bytes
  /-- BLAKE2b-512, used for the CTX commitment. -/
  blake2b : Bytes → Bytes
  /-- Signature correctness. -/
  verify_sign : ∀ sk m, verify (edPub sk) (sign sk m) = some m
  /-- The two key conversions agree: converting a public key yields the public key of
  the converted secret key. -/
  conv_agree : ∀ sk, xpkConv (edPub sk) = some (xpub (xsk sk))
  /-- X25519 agreement. -/
  dh_comm : ∀ a b, x25519 a (xpub b) = x25519 b (xpub a)
  /-- ML-KEM correctness. -/
  decap_encap : ∀ sk coins,
    decap sk (encap (kemPub sk) coins).1 = some (encap (kemPub sk) coins).2
  /-- AEAD correctness. -/
  aead_open_seal : ∀ k n ad pt,
    aeadOpen k n ad (aeadSeal k n ad pt).1 (aeadSeal k n ad pt).2 = some pt
  /-- Ed25519 public keys are 32 bytes. -/
  edPub_length : ∀ sk, (edPub sk).length = 32
  /-- X25519 public keys are 32 bytes. -/
  xpub_length : ∀ sk, (xpub sk).length = 32
  /-- X25519 outputs are 32 bytes. -/
  x25519_length : ∀ a b, (x25519 a b).length = 32
  /-- ML-KEM-768 public keys are 1184 bytes. -/
  kemPub_length : ∀ sk, (kemPub sk).length = 1184
  /-- ML-KEM shared secrets are 32 bytes. -/
  encap_ss_length : ∀ pk coins, (encap pk coins).2.length = 32
  /-- Decapsulated shared secrets are 32 bytes. -/
  decap_length : ∀ sk ct ss, decap sk ct = some ss → ss.length = 32
  /-- HKDF returns exactly the requested number of bytes. -/
  hkdf_length : ∀ ikm info L, (hkdf ikm info L).length = L
  /-- Poly1305 tags are 16 bytes. -/
  aeadSeal_tag_length : ∀ k n ad pt, (aeadSeal k n ad pt).2.length = 16
  /-- BLAKE2b-512 digests are 64 bytes. -/
  blake2b_length : ∀ x, (blake2b x).length = 64

end Pqxdh
