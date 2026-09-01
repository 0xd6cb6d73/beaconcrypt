import BeaconcryptCore.Model.Pqxdh.Kdf

/-!
# BeaconCrypt modified PQXDH — the committing record layer binds its context

The record layer of spec §13 does not only authenticate: it *commits*.  Besides the
detached ChaCha20-Poly1305 tag `T`, every record carries

`T* = BLAKE2b₅₁₂(K ‖ N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(sid))`,

so the transmitted ciphertext `CT ‖ T ‖ T*` is bound to the message key, the nonce,
the session associated data, the wire sequence number and the *sender identifier*.

This file makes that precise.  Two assumptions about BLAKE2b-512 appear, both stated
about the *particular pair of record contexts at hand* rather than as a global
property of the hash: a global injectivity assumption would be inconsistent with the
fixed 64-byte digest length that the rest of the model relies on, and everything
proved under it would be vacuous.

* `Pqxdh.NoCtxCollision c mk mk' ad ad'` — the two contexts do not produce the same
  commitment from different inputs.  It holds trivially when the two contexts are
  equal, so it is a satisfiable hypothesis.
* `Pqxdh.CtxDistinct c mk mk' ad ad'` — the two contexts produce different
  commitments.  This is what a rejection needs, and
  `BeaconcryptCore.Model.Pqxdh.Instance` exhibits an instance of the primitive
  interface in which it provably holds whenever the sequence numbers differ.

The results are then:

* `Pqxdh.ctxCommit_context_eq` — with the field lengths the protocol fixes, a
  commitment determines the message key, the nonce, the associated data, the
  sequence number and the sender identifier;
* `Pqxdh.openRecord_committing` — one wire ciphertext opens under at most one
  `(message key, record context)` pair, and then to one plaintext: the record layer
  is *key- and context-committing*;
* `Pqxdh.openRecord_relabelled`, `Pqxdh.openRecord_wrong_seq`,
  `Pqxdh.openRecord_wrong_sender` — a record cannot be re-labelled: seal it at one
  sequence number, or under one sender identifier, and it does not open at another.

The length side conditions are exactly the ones the protocol maintains: a 32-byte
key, a 12-byte nonce, 153 bytes of associated data (spec §9), a 16-byte Poly1305 tag
and 64-bit sequence and sender identifiers.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Pqxdh

/-! ## Record contexts -/

/-- The length side conditions the protocol maintains for one record context: a
32-byte message key, a 12-byte nonce, 153 bytes of associated data, and sequence
number and sender identifier both representable in 64 bits. -/
structure RecordWf (mk : Bytes × Bytes) (ad : RecordAD) : Prop where
  /-- The ChaCha20-Poly1305 key is 32 bytes. -/
  key : mk.1.length = 32
  /-- The ChaCha20-Poly1305 nonce is 12 bytes. -/
  nonce : mk.2.length = 12
  /-- The session associated data is 153 bytes (spec §9). -/
  bytes : ad.bytes.length = 153
  /-- The wire sequence number fits in 64 bits. -/
  seq : ad.seq < 2 ^ 64
  /-- The sender identifier fits in 64 bits (spec §2.1). -/
  sid : ad.sid < 2 ^ 64

/-- The material derived from a chain key always has the protocol's shape: a 32-byte
key and a 12-byte nonce. -/
theorem msgMaterial_lengths (c : Crypto) (ck : Bytes) :
    (msgMaterial c ck).1.length = 32 ∧ (msgMaterial c ck).2.length = 12 := by
  refine ⟨?_, ?_⟩ <;>
    simp [msgMaterial, ratchetOut, c.hkdf_length]

/-- The associated data of a record between two 32-byte identity keys is 153 bytes,
so a session record context is well formed as soon as its sequence number and sender
identifier are 64-bit values. -/
theorem recordWf_of (c : Crypto) (ck ikSPub ikBPub : Bytes) (seq sid : ℕ)
    (hs : ikSPub.length = 32) (hb : ikBPub.length = 32)
    (hseq : seq < 2 ^ 64) (hsid : sid < 2 ^ 64) :
    RecordWf (msgMaterial c ck) ⟨assocData ikSPub ikBPub, seq, sid⟩ :=
  ⟨(msgMaterial_lengths c ck).1, (msgMaterial_lengths c ck).2,
    assocData_length hs hb, hseq, hsid⟩

/-- A record context built from a chain-derived key is well formed as soon as its
associated data has the protocol's length and its sequence number and sender
identifier are 64-bit values. -/
theorem recordWf_msgMaterial (c : Crypto) (ck : Bytes) {ad : RecordAD}
    (hb : ad.bytes.length = 153) (hseq : ad.seq < 2 ^ 64) (hsid : ad.sid < 2 ^ 64) :
    RecordWf (msgMaterial c ck) ad :=
  ⟨(msgMaterial_lengths c ck).1, (msgMaterial_lengths c ck).2, hb, hseq, hsid⟩

/-- The same for the key the receive ratchet derives for an arbitrary index. -/
theorem recordWf_msgKeyAt (c : Crypto) (ck : Bytes) (i : ℕ) {ad : RecordAD}
    (hb : ad.bytes.length = 153) (hseq : ad.seq < 2 ^ 64) (hsid : ad.sid < 2 ^ 64) :
    RecordWf (Ratchet.msgKeyAt (ratchetCrypto c) ck i) ad :=
  ⟨(msgMaterial_lengths c _).1, (msgMaterial_lengths c _).2, hb, hseq, hsid⟩

/-- The input of the CTX commitment: `K ‖ N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(sid)`. -/
def ctxPreimage (mk : Bytes × Bytes) (ad : RecordAD) (t : Bytes) : Bytes :=
  mk.1 ++ mk.2 ++ ad.bytes ++ t ++ LE64 ad.seq ++ LE64 ad.sid

theorem ctxCommit_eq (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD) (t : Bytes) :
    ctxCommit c mk ad t = c.blake2b (ctxPreimage mk ad t) := rfl

/-- At the field lengths the protocol fixes, the commitment input determines the
message key, the nonce, the associated data, the sequence number, the sender
identifier and the base AEAD tag. -/
theorem ctxPreimage_inj {mk mk' : Bytes × Bytes} {ad ad' : RecordAD} {t t' : Bytes}
    (hw : RecordWf mk ad) (hw' : RecordWf mk' ad')
    (ht : t.length = 16) (ht' : t'.length = 16)
    (h : ctxPreimage mk ad t = ctxPreimage mk' ad' t') :
    mk = mk' ∧ ad = ad' ∧ t = t' := by
  rw [ctxPreimage, ctxPreimage] at h
  obtain ⟨h1, hsid⟩ := List.append_inj' h (by simp)
  obtain ⟨h2, hseq⟩ := List.append_inj' h1 (by simp)
  obtain ⟨h3, htag⟩ := List.append_inj' h2 (by simp [ht, ht'])
  obtain ⟨h4, hbytes⟩ := List.append_inj' h3 (by simp [hw.bytes, hw'.bytes])
  obtain ⟨hkey, hnonce⟩ := List.append_inj' h4 (by simp [hw.nonce, hw'.nonce])
  refine ⟨Prod.ext hkey hnonce, ?_, htag⟩
  have e1 : ad.seq = ad'.seq := LE64_inj hw.seq hw'.seq hseq
  have e2 : ad.sid = ad'.sid := LE64_inj hw.sid hw'.sid hsid
  obtain ⟨b, s, i⟩ := ad
  obtain ⟨b', s', i'⟩ := ad'
  simp_all

/-! ## The two hypotheses about BLAKE2b-512

Both are statements about the pair of record contexts at hand only.  A *global*
injectivity assumption on `blake2b` would contradict `Crypto.blake2b_length`, and
every consequence drawn from it would be vacuous. -/

/-- BLAKE2b-512 does not collide on the commitment inputs of these two record
contexts.  This holds trivially when the two contexts coincide, and is the local form
of the collision-resistance idealisation. -/
def NoCtxCollision (c : Crypto) (mk mk' : Bytes × Bytes) (ad ad' : RecordAD) : Prop :=
  ∀ t : Bytes, ctxCommit c mk ad t = ctxCommit c mk' ad' t →
    ctxPreimage mk ad t = ctxPreimage mk' ad' t

/-- The two record contexts produce different CTX commitments, for every Poly1305 tag
the protocol can produce.  This is exactly what a rejection argument needs. -/
def CtxDistinct (c : Crypto) (mk mk' : Bytes × Bytes) (ad ad' : RecordAD) : Prop :=
  ∀ t : Bytes, t.length = 16 → ctxCommit c mk ad t ≠ ctxCommit c mk' ad' t

/-- Identical contexts never collide, so `NoCtxCollision` is satisfiable. -/
theorem noCtxCollision_self (c : Crypto) (mk : Bytes × Bytes) (ad : RecordAD) :
    NoCtxCollision c mk mk ad ad := fun _ _ => rfl

/-- **The CTX commitment binds its whole context.**  If the two contexts do not
collide then, at the field lengths the protocol fixes, equal commitments force the
message key, the nonce, the associated data, the sequence number, the sender
identifier and the base AEAD tag to agree. -/
theorem ctxCommit_context_eq (c : Crypto) {mk mk' : Bytes × Bytes} {ad ad' : RecordAD}
    {t : Bytes} (hnc : NoCtxCollision c mk mk' ad ad') (hw : RecordWf mk ad)
    (hw' : RecordWf mk' ad') (ht : t.length = 16)
    (h : ctxCommit c mk ad t = ctxCommit c mk' ad' t) :
    mk = mk' ∧ ad = ad' :=
  let e := ctxPreimage_inj hw hw' ht ht (hnc t h)
  ⟨e.1, e.2.1⟩

/-- Distinct contexts that do not collide produce distinct commitments. -/
theorem ctxDistinct_of_noCtxCollision (c : Crypto) {mk mk' : Bytes × Bytes}
    {ad ad' : RecordAD} (hnc : NoCtxCollision c mk mk' ad ad') (hw : RecordWf mk ad)
    (hw' : RecordWf mk' ad') (hne : ¬ (mk = mk' ∧ ad = ad')) :
    CtxDistinct c mk mk' ad ad' := by
  intro t ht hcol
  exact hne (ctxCommit_context_eq c hnc hw hw' ht hcol)

/-! ## Consequences for the record layer -/

/-- **The record layer is key- and context-committing.**  If the two contexts do not
collide, a wire ciphertext `CT ‖ T ‖ T*` opens under at most one message key and one
record context — and then to a single plaintext.  In particular the sequence number
and the sender identifier the record was created with are determined by it. -/
theorem openRecord_committing (c : Crypto) {mk mk' : Bytes × Bytes} {ad ad' : RecordAD}
    {b pt pt' : Bytes} (hnc : NoCtxCollision c mk mk' ad ad') (hw : RecordWf mk ad)
    (hw' : RecordWf mk' ad') (h : openRecord c mk ad b = some pt)
    (h' : openRecord c mk' ad' b = some pt') :
    mk = mk' ∧ ad = ad' ∧ pt = pt' := by
  rcases hd : decodeRecord b with _ | r
  · rw [openRecord, hd] at h; simp at h
  · rw [openRecord, hd] at h h'
    simp only [Option.bind_some] at h h'
    by_cases hc : r.commit = ctxCommit c mk ad r.tag
    · by_cases hc' : r.commit = ctxCommit c mk' ad' r.tag
      · have htag : r.tag.length = 16 := by
          rw [decodeRecord] at hd
          split at hd
          · cases hd; simp; omega
          · exact absurd hd (by simp)
        obtain ⟨hk, hA⟩ :=
          ctxCommit_context_eq c hnc hw hw' htag (hc ▸ hc' : _)
        refine ⟨hk, hA, ?_⟩
        rw [if_pos hc] at h
        rw [if_pos hc'] at h'
        rw [hk, hA] at h
        rw [h] at h'
        exact Option.some.inj h'
      · rw [if_neg hc'] at h'; simp at h'
    · rw [if_neg hc] at h; simp at h

/-- **A record cannot be re-labelled.**  A wire record sealed under one message key
and one record context does not open under a context whose commitments differ: in
particular not at a different sequence number and not under a different sender
identifier (spec §13, §16). -/
theorem openRecord_relabelled (c : Crypto) {mk mk' : Bytes × Bytes} {ad ad' : RecordAD}
    {pt : Bytes} (hd : CtxDistinct c mk mk' ad ad') :
    openRecord c mk' ad' (sealRecord c mk ad pt).encode = none := by
  have ht : (sealRecord c mk ad pt).tag.length = 16 := c.aeadSeal_tag_length _ _ _ _
  have hc : (sealRecord c mk ad pt).commit.length = 64 := c.blake2b_length _
  simp only [openRecord, decodeRecord_encode _ ht hc, Option.bind_some]
  simp only [sealRecord]
  rw [if_neg (hd _ (c.aeadSeal_tag_length _ _ _ _))]

/-- Specialisation of the previous result to the sender identifier: a record sealed by
one sender does not open when relabelled as coming from another (spec §13). -/
theorem openRecord_wrong_sender (c : Crypto) {mk : Bytes × Bytes} {ad : RecordAD}
    {sid' : ℕ} {pt : Bytes} (hnc : NoCtxCollision c mk mk ad { ad with sid := sid' })
    (hw : RecordWf mk ad) (hsid : sid' < 2 ^ 64) (hne : sid' ≠ ad.sid) :
    openRecord c mk { ad with sid := sid' } (sealRecord c mk ad pt).encode = none := by
  refine openRecord_relabelled c
    (ctxDistinct_of_noCtxCollision c hnc hw ⟨hw.key, hw.nonce, hw.bytes, hw.seq, hsid⟩ ?_)
  rintro ⟨-, hA⟩
  exact hne (congrArg RecordAD.sid hA).symm

/-- Specialisation to the wire sequence number: a record sealed at one sequence number
does not open at another (spec §13). -/
theorem openRecord_wrong_seq (c : Crypto) {mk : Bytes × Bytes} {ad : RecordAD}
    {seq' : ℕ} {pt : Bytes} (hnc : NoCtxCollision c mk mk ad { ad with seq := seq' })
    (hw : RecordWf mk ad) (hseq : seq' < 2 ^ 64) (hne : seq' ≠ ad.seq) :
    openRecord c mk { ad with seq := seq' } (sealRecord c mk ad pt).encode = none := by
  refine openRecord_relabelled c
    (ctxDistinct_of_noCtxCollision c hnc hw ⟨hw.key, hw.nonce, hw.bytes, hseq, hw.sid⟩ ?_)
  rintro ⟨-, hA⟩
  exact hne (congrArg RecordAD.seq hA).symm

end Pqxdh
