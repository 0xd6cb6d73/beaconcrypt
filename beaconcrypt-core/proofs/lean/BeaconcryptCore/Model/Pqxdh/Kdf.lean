import BeaconcryptCore.Model.Pqxdh.Primitives
import BeaconcryptCore.Model.Ratchet

/-!
# BeaconCrypt modified PQXDH — key schedule and committing record layer

Second part of the ideal model of `pqxdh_spec.md`.  It defines

* the PQXDH transcript `IKM_PQ = FF^32 ‖ DH₁ ‖ DH₂ ‖ DH₃ ‖ DH₄ ‖ SS` and the root
  secret `DS = HKDF₅₁₂(IKM_PQ, INFO_PQ, 32)` (spec §8),
* the associated data `AD` — server identity first, beacon identity second
  (spec §9),
* the initial directional chain keys `L ‖ R = HKDF₅₁₂(DS, INFO_R, 64)` (spec §10),
* the BeaconCrypt record layer: the `key ‖ next_chain ‖ nonce` partition of
  `HKDF₅₁₂(CK, INFO_R, 76)`, detached ChaCha20-Poly1305 sealing and the CTX
  commitment `T* = BLAKE2b₅₁₂(K ‖ N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(sid))`, with the
  transmitted ciphertext `CT ‖ T ‖ T*` (spec §13).

The record layer is packaged as an instance `Pqxdh.ratchetCrypto` of the already
verified handwritten symmetric ratchet `Ratchet.Crypto` of
`BeaconcryptCore.Model.Ratchet`, so the initial server record and the beacon's
acceptance of it are exactly one `Ratchet.sendStep` and one `Ratchet.recvStep` of
that model.  This is what makes beacon acceptance "a valid admissible initial
receive-ratchet record" rather than a bespoke `seq = 1` test (spec §16).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Pqxdh

/-! ## PQXDH root derivation (spec §8) -/

/-- The 192-byte PQXDH transcript `FF^32 ‖ DH₁ ‖ DH₂ ‖ DH₃ ‖ DH₄ ‖ SS`. -/
def pqxdhIKM (dh1 dh2 dh3 dh4 ss : Bytes) : Bytes :=
  padFF32 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss

theorem pqxdhIKM_length {dh1 dh2 dh3 dh4 ss : Bytes} (h1 : dh1.length = 32)
    (h2 : dh2.length = 32) (h3 : dh3.length = 32) (h4 : dh4.length = 32)
    (hs : ss.length = 32) : (pqxdhIKM dh1 dh2 dh3 dh4 ss).length = 192 := by
  simp [pqxdhIKM, padFF32, h1, h2, h3, h4, hs]

/-- The session root secret `DS = HKDF₅₁₂(IKM_PQ, INFO_PQ, 32)`. -/
def rootSecret (c : Crypto) (ikm : Bytes) : Bytes := c.hkdf ikm INFO_PQ 32

theorem rootSecret_length (c : Crypto) (ikm : Bytes) : (rootSecret c ikm).length = 32 :=
  c.hkdf_length _ _ _

/-! ## Associated data (spec §9) -/

/-- `AD = Tag_sig(IK_S) ‖ Tag_sig(IK_B) ‖ INFO_PQ ‖ INFO_R`: server identity first,
beacon identity second. -/
def assocData (ikSPub ikBPub : Bytes) : Bytes :=
  tagSig ikSPub ++ tagSig ikBPub ++ INFO_PQ ++ INFO_R

theorem assocData_length {ikSPub ikBPub : Bytes} (hs : ikSPub.length = 32)
    (hb : ikBPub.length = 32) : (assocData ikSPub ikBPub).length = 153 := by
  simp [assocData, tagSig, hs, hb, INFO_PQ, INFO_R]

/-- The associated data determines the ordered identity pair. -/
theorem assocData_inj {a b a' b' : Bytes} (ha : a.length = 32) (hb : b.length = 32)
    (ha' : a'.length = 32) (hb' : b'.length = 32) (h : assocData a b = assocData a' b') :
    a = a' ∧ b = b' := by
  simp only [assocData, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [tagSig, ha, ha'])
  obtain ⟨h3, -⟩ := List.append_inj h2 (by simp [tagSig, hb, hb'])
  exact ⟨by simpa [tagSig] using h1, by simpa [tagSig] using h3⟩

/-! ## Initial directional chain keys (spec §10) -/

/-- `R₀ = HKDF₅₁₂(DS, INFO_R, 64)`, split into the left and right halves
`L = R₀[0..32)` and `R = R₀[32..64)`. -/
def rootChains (c : Crypto) (ds : Bytes) : Bytes × Bytes :=
  ((c.hkdf ds INFO_R 64).take 32, (c.hkdf ds INFO_R 64).drop 32)

theorem rootChains_length (c : Crypto) (ds : Bytes) :
    (rootChains c ds).1.length = 32 ∧ (rootChains c ds).2.length = 32 := by
  constructor <;> simp [rootChains, c.hkdf_length]

/-! ## The BeaconCrypt record layer (spec §13) -/

/-- The associated data of a single BeaconCrypt record: the 153-byte PQXDH
associated data together with the wire sequence number and the sender identifier,
both of which the CTX commitment binds. -/
structure RecordAD where
  /-- The 153-byte associated data of the session. -/
  bytes : Bytes
  /-- The wire sequence number of the record. -/
  seq : ℕ
  /-- The numeric identifier of the sender of the record. -/
  sid : ℕ
deriving DecidableEq

/-- A transmitted record ciphertext, `CT ‖ T ‖ T*`. -/
structure RecordCipher where
  /-- The ChaCha20-Poly1305 ciphertext `CT`. -/
  body : Bytes
  /-- The detached Poly1305 tag `T`. -/
  tag : Bytes
  /-- The BLAKE2b-512 CTX commitment `T*`. -/
  commit : Bytes
deriving DecidableEq

/-- The wire encoding `CT ‖ T ‖ T*`. -/
def RecordCipher.encode (r : RecordCipher) : Bytes := r.body ++ r.tag ++ r.commit

/-- Parsing a transmitted record ciphertext: the trailing 16-byte tag and 64-byte
commitment are split off the end. -/
def decodeRecord (b : Bytes) : Option RecordCipher :=
  if 80 ≤ b.length then
    some ⟨b.take (b.length - 80), (b.drop (b.length - 80)).take 16, b.drop (b.length - 64)⟩
  else none

/-- The wire encoding of a well-formed record is unambiguous. -/
theorem decodeRecord_encode (r : RecordCipher) (ht : r.tag.length = 16)
    (hc : r.commit.length = 64) : decodeRecord r.encode = some r := by
  obtain ⟨body, tag, commit⟩ := r
  simp only [RecordCipher.encode] at *
  have hlen : (body ++ tag ++ commit).length = body.length + 80 := by simp [ht, hc]
  rw [decodeRecord, if_pos (by omega), hlen]
  simp only [show body.length + 80 - 80 = body.length from by omega,
    show body.length + 80 - 64 = body.length + 16 from by omega, List.append_assoc]
  have e1 : List.take body.length (body ++ (tag ++ commit)) = body := by simp
  have e2 : List.take 16 (List.drop body.length (body ++ (tag ++ commit))) = tag := by
    rw [List.drop_left, ← ht, List.take_left]
  have e3 : List.drop (body.length + 16) (body ++ (tag ++ commit)) = commit := by
    rw [← List.drop_drop, List.drop_left, ← ht, List.drop_left]
  rw [e1, e2, e3]

/-- The 76-byte ratchet expansion `HKDF₅₁₂(CK, INFO_R, 76)`, partitioned as
`key ‖ next_chain ‖ nonce`. -/
def ratchetOut (c : Crypto) (ck : Bytes) : Bytes := c.hkdf ck INFO_R 76

/-- The next chain key `O[32..64)`. -/
def nextChain (c : Crypto) (ck : Bytes) : Bytes := ((ratchetOut c ck).drop 32).take 32

/-- The message key and nonce `(O[0..32), O[64..76))`. -/
def msgMaterial (c : Crypto) (ck : Bytes) : Bytes × Bytes :=
  ((ratchetOut c ck).take 32, (ratchetOut c ck).drop 64)

/-- The CTX commitment `T* = BLAKE2b₅₁₂(K ‖ N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(sid))`. -/
def ctxCommit (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD) (tag : Bytes) : Bytes :=
  c.blake2b (mk.1 ++ mk.2 ++ ad.bytes ++ tag ++ LE64 ad.seq ++ LE64 ad.sid)

/-- Seal one record: detached ChaCha20-Poly1305 plus the CTX commitment. -/
def sealRecord (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD) (pt : Bytes) :
    RecordCipher :=
  ⟨(c.aeadSeal mk.1 mk.2 ad.bytes pt).1, (c.aeadSeal mk.1 mk.2 ad.bytes pt).2,
    ctxCommit c mk ad (c.aeadSeal mk.1 mk.2 ad.bytes pt).2⟩

/-- Open one record: parse, check the CTX commitment, then authenticate and decrypt.
Any failure yields `none`. -/
def openRecord (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD) (b : Bytes) :
    Option Bytes :=
  (decodeRecord b).bind fun r =>
    if r.commit = ctxCommit c mk ad r.tag then
      c.aeadOpen mk.1 mk.2 ad.bytes r.body r.tag
    else none

/-- A record sealed with the current material opens to the sealed plaintext. -/
theorem openRecord_sealRecord (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD)
    (pt : Bytes) : openRecord c mk ad (sealRecord c mk ad pt).encode = some pt := by
  have ht : (sealRecord c mk ad pt).tag.length = 16 := c.aeadSeal_tag_length _ _ _ _
  have hc : (sealRecord c mk ad pt).commit.length = 64 := c.blake2b_length _
  simp only [openRecord, decodeRecord_encode _ ht hc, Option.bind_some]
  simp only [sealRecord, if_true]
  exact c.aead_open_seal _ _ _ _

/-- The BeaconCrypt record layer as an instance of the verified handwritten
symmetric ratchet: chain keys are byte strings, a message key is the pair
`(K, N)`, associated data is a `RecordAD`, and a ciphertext is the wire
encoding `CT ‖ T ‖ T*`. -/
def ratchetCrypto (c : Crypto) :
    Ratchet.Crypto Bytes (Bytes × Bytes) RecordAD Bytes Bytes where
  kdfChain ck := nextChain c ck
  kdfMsg ck := msgMaterial c ck
  enc mk ad pt := (sealRecord c mk ad pt).encode
  dec mk ad ct := openRecord c mk ad ct
  dec_enc mk ad pt := openRecord_sealRecord c mk ad pt

@[simp] theorem ratchetCrypto_kdfChain (c : Crypto) (ck : Bytes) :
    (ratchetCrypto c).kdfChain ck = nextChain c ck := rfl

@[simp] theorem ratchetCrypto_kdfMsg (c : Crypto) (ck : Bytes) :
    (ratchetCrypto c).kdfMsg ck = msgMaterial c ck := rfl

@[simp] theorem ratchetCrypto_enc (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD)
    (pt : Bytes) : (ratchetCrypto c).enc mk ad pt = (sealRecord c mk ad pt).encode := rfl

@[simp] theorem ratchetCrypto_dec (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD)
    (ct : Bytes) : (ratchetCrypto c).dec mk ad ct = openRecord c mk ad ct := rfl

/-- A record sealed under one associated data (in particular one sequence number and
one sender identifier) does not open under another, unless the two commitments
collide: the CTX commitment binds the sender and the sequence number. -/
theorem openRecord_seal_ne_ad (c : Crypto) (mk : Bytes × Bytes) (ad ad' : RecordAD)
    (pt : Bytes)
    (h : ctxCommit c mk ad (c.aeadSeal mk.1 mk.2 ad.bytes pt).2
        ≠ ctxCommit c mk ad' (c.aeadSeal mk.1 mk.2 ad.bytes pt).2) :
    openRecord c mk ad' (sealRecord c mk ad pt).encode = none := by
  have ht : (sealRecord c mk ad pt).tag.length = 16 := c.aeadSeal_tag_length _ _ _ _
  have hc : (sealRecord c mk ad pt).commit.length = 64 := c.blake2b_length _
  simp only [openRecord, decodeRecord_encode _ ht hc, Option.bind_some]
  simp only [sealRecord]
  rw [if_neg h]

end Pqxdh
