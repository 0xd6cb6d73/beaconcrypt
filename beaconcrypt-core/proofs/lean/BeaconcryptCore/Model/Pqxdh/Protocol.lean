import BeaconcryptCore.Model.Pqxdh.Kdf

/-!
# BeaconCrypt modified PQXDH — the two state machines

Third part of the ideal model of `pqxdh_spec.md`: the wire messages, the two
principals' states, and the four transitions of a registration.

* `Pqxdh.beaconInit` — spec §5: the beacon emits its authenticated `InitKex` and
  moves `Fresh → InitSent`; no second bundle can be emitted, which is modelled by
  returning `none` from any other state.
* `Pqxdh.validateInit` — spec §6: parse the tagged identity key, verify the three
  attached signatures under it, and revalidate the type and role encodings.
* `Pqxdh.serverRespond` — spec §6–§14: replay check on
  `RID = IK_B ‖ OT_B`, the four X25519 contributions and the ML-KEM contribution,
  all-zero-DH rejection, root derivation, **consumption of `RID`**, checked key-ID
  allocation, the first committing ratchet record carrying `LE64(kid) ‖ M`, and the
  transactional peer commit.
* `Pqxdh.beaconFinish` — spec §15–§18: decapsulation, the pinned-identity check,
  the role-reversed X25519 contributions, root derivation, initialisation of the
  complementary ratchets, admission of the initial receive record through the
  general receive transition, the authenticated-sender check and the
  `LE64(kid)` binding check; any failure moves the beacon to `Aborted`.

The receive/send side of the record layer is the verified handwritten ratchet of
`BeaconcryptCore.Model.Ratchet`, instantiated by `Pqxdh.ratchetCrypto`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Pqxdh

/-- The largest representable beacon key identifier, `2^64 - 1`. -/
def maxKeyId : ℕ := 2 ^ 64 - 1

/-! ## Wire messages -/

/-- The beacon's registration bundle (spec §5).  The last three fields are attached
signatures. -/
structure InitKex where
  /-- `Tag_sig(IK_B)`. -/
  identityKey : Bytes
  /-- `Sign(Tag_X(role_pre, PK_B))`. -/
  preKey : Bytes
  /-- `Sign(Tag_X(role_otk, OT_B))`. -/
  oneTimeKey : Bytes
  /-- `Sign(Tag_PQ(KEM_B))`. -/
  pqKey : Bytes
deriving DecidableEq

/-- A BeaconCrypt ratchet record on the wire (spec §13). -/
structure CryptoFrame where
  /-- The clear sender identifier. -/
  keyId : ℕ
  /-- The wire sequence number. -/
  seq : ℕ
  /-- `CT ‖ T ‖ T*`. -/
  cipherText : Bytes
deriving DecidableEq

/-- The server's response (spec §14).  Unlike `InitKex.identityKey`, the identity key
here is the raw 32-byte Ed25519 public key. -/
structure KexResponse where
  /-- `IK_S` (raw). -/
  identityKey : Bytes
  /-- `E_S`. -/
  ephemeralKey : Bytes
  /-- `CT_KEM`. -/
  kemCipherText : Bytes
  /-- The serialized first server record. -/
  appFrame : CryptoFrame
  /-- The clear assigned key identifier. -/
  keyId : ℕ

/-- The out-of-band pinned server binding held by a beacon (spec §2.2). -/
structure ServerBinding where
  /-- The pinned Ed25519 server identity key. -/
  ikPub : Bytes
  /-- The fixed numeric server sender identifier. -/
  sid : ℕ
deriving DecidableEq

/-! ## The four X25519 contributions (spec §7 and §15) -/

/-- The server's four contributions, in the order used by the production adapter:
`DH₁ = X25519(XSK(IK_S), PK_B)`, `DH₂ = X25519(E_S, XPK(IK_B))`,
`DH₃ = X25519(E_S, PK_B)`, `DH₄ = X25519(E_S, OT_B)`. -/
def serverDHs (c : Crypto) (ikSkS eSk ikBX preKey otKey : Bytes) :
    Bytes × Bytes × Bytes × Bytes :=
  (c.x25519 (c.xsk ikSkS) preKey, c.x25519 eSk ikBX, c.x25519 eSk preKey,
    c.x25519 eSk otKey)

/-- The beacon's role-reversed contributions:
`DH₁' = X25519(PK_B^sk, XPK(IK_S))`, `DH₂' = X25519(XSK(IK_B), E_S)`,
`DH₃' = X25519(PK_B^sk, E_S)`, `DH₄' = X25519(OT_B^sk, E_S)`. -/
def beaconDHs (c : Crypto) (ikSkB preSk otSk ikSX ePub : Bytes) :
    Bytes × Bytes × Bytes × Bytes :=
  (c.x25519 preSk ikSX, c.x25519 (c.xsk ikSkB) ePub, c.x25519 preSk ePub,
    c.x25519 otSk ePub)

/-- No contribution may be the all-zero value (spec §7). -/
def dhNonZero (d : Bytes × Bytes × Bytes × Bytes) : Prop :=
  d.1 ≠ zero32 ∧ d.2.1 ≠ zero32 ∧ d.2.2.1 ≠ zero32 ∧ d.2.2.2 ≠ zero32

instance (d : Bytes × Bytes × Bytes × Bytes) : Decidable (dhNonZero d) := by
  unfold dhNonZero; infer_instance

/-- The transcript of the four contributions and the ML-KEM shared secret. -/
def ikmOf (d : Bytes × Bytes × Bytes × Bytes) (ss : Bytes) : Bytes :=
  pqxdhIKM d.1 d.2.1 d.2.2.1 d.2.2.2 ss

/-! ## The beacon -/

/-- The runtime state of a beacon (spec §2.2, §20).  Note that `established` retains
neither the X25519 prekey, nor the one-time key, nor the ML-KEM key: the
registration-local key material is not representable in an established state
(spec §17). -/
inductive BeaconState where
  /-- Provisioned, registration not yet started. -/
  | fresh (binding : ServerBinding) (ikSk preSk kemSk : Bytes)
  /-- Provisioned with a pregenerated one-time X25519 key, through the compatibility
  API; registration not yet started (spec §2.2). -/
  | freshWithCoins (binding : ServerBinding) (ikSk preSk otSk kemSk : Bytes)
  /-- The registration bundle has been emitted. -/
  | initSent (binding : ServerBinding) (ikSk preSk otSk kemSk : Bytes)
  /-- Registration completed: identifier, associated data and both ratchets. -/
  | established (binding : ServerBinding) (ikSk : Bytes) (kid : ℕ) (ad : Bytes)
      (send : Ratchet.SendState Bytes)
      (recv : Ratchet.RecvState Bytes (Bytes × Bytes))
  /-- Registration failed; no restart is possible. -/
  | aborted

/-- The registration-local secrets still held by a beacon state.  They exist only
while registration is pending (spec §17). -/
def BeaconState.regSecrets : BeaconState → Option (Bytes × Bytes × Bytes)
  | .fresh _ _ _ _ => none
  | .freshWithCoins _ _ preSk otSk kemSk => some (preSk, otSk, kemSk)
  | .initSent _ _ preSk otSk kemSk => some (preSk, otSk, kemSk)
  | .established .. => none
  | .aborted => none

/-- The unsigned/signed registration bundle built by a beacon (spec §5). -/
def initKexOf (c : Crypto) (ikSk preSk otSk kemSk : Bytes) : InitKex where
  identityKey := tagSig (c.edPub ikSk)
  preKey := c.sign ikSk (tagX rolePre (c.xpub preSk))
  oneTimeKey := c.sign ikSk (tagX roleOtk (c.xpub otSk))
  pqKey := c.sign ikSk (tagPQ (c.kemPub kemSk))

/-- Registration initiation (spec §5).  It is possible only from `Fresh` — where the
one-time X25519 key is generated now — or from `FreshWithCoins`, where the one-time
key was pregenerated through the compatibility API and the freshly offered one is
ignored.  From any other state no bundle is emitted, which makes registration
one-shot. -/
def beaconInit (c : Crypto) (s : BeaconState) (otSk : Bytes) :
    Option (InitKex × BeaconState) :=
  match s with
  | .fresh b ikSk preSk kemSk =>
      some (initKexOf c ikSk preSk otSk kemSk, .initSent b ikSk preSk otSk kemSk)
  | .freshWithCoins b ikSk preSk otSk' kemSk =>
      some (initKexOf c ikSk preSk otSk' kemSk, .initSent b ikSk preSk otSk' kemSk)
  | _ => none

/-! ## The server -/

/-- A published peer of the server. -/
structure Peer where
  /-- The beacon's Ed25519 identity key. -/
  ikPub : Bytes
  /-- The session associated data. -/
  ad : Bytes
  /-- The server-to-beacon sending ratchet. -/
  send : Ratchet.SendState Bytes
  /-- The beacon-to-server receiving ratchet. -/
  recv : Ratchet.RecvState Bytes (Bytes × Bytes)

/-- The server's long-term state (spec §2.1). -/
structure ServerState where
  /-- The Ed25519 identity secret key. -/
  ikSk : Bytes
  /-- The fixed numeric sender identifier `sid_S`. -/
  sid : ℕ
  /-- The last allocated beacon key identifier `n_S`. -/
  n : ℕ
  /-- The published peers. -/
  peers : List (ℕ × Peer)
  /-- The persistent consumed-registration set. -/
  consumed : List Bytes

/-- Why the server rejected a registration. -/
inductive ServerError where
  /-- A type tag, role tag, length or key parse failed. -/
  | badEncoding
  /-- An attached signature failed to verify. -/
  | badSignature
  /-- `RID` has already been consumed. -/
  | registrationReplay
  /-- Some X25519 contribution was all zero. -/
  | zeroDH
  /-- An application message was explicitly supplied but empty. -/
  | emptyAppMessage
  /-- The allocation counter is exhausted. -/
  | keyIdExhausted
  /-- The proposed identifier is already in use. -/
  | keyIdCollision
deriving DecidableEq, Repr

/-- The validated content of an `InitKex`. -/
structure ValidInit where
  /-- `IK_B`. -/
  ikB : Bytes
  /-- `PK_B`. -/
  preKey : Bytes
  /-- `OT_B`. -/
  otKey : Bytes
  /-- `KEM_B`. -/
  kemPub : Bytes
deriving DecidableEq

/-- The semantic registration identifier `RID = IK_B ‖ OT_B` (spec §6). -/
def ValidInit.rid (v : ValidInit) : Bytes := v.ikB ++ v.otKey

/-- Server validation of an `InitKex` (spec §6): parse the tagged identity key,
verify the three attached signatures under it, and revalidate the type and role
encodings of the signed payloads. -/
def validateInit (c : Crypto) (m : InitKex) : Option ValidInit := do
  let ikB ← parseSigTag m.identityKey
  let p ← c.verify ikB m.preKey
  let o ← c.verify ikB m.oneTimeKey
  let q ← c.verify ikB m.pqKey
  let pk ← parseXTag rolePre p
  let ot ← parseXTag roleOtk o
  let kem ← parsePQTag q
  some ⟨ikB, pk, ot, kem⟩

/-- The server's first send-ratchet step: the initial record sealed under the left
chain key, with plaintext `LE64(kid) ‖ M` and the session associated data at wire
sequence `1` under the server's own sender identifier (spec §12, §13). -/
def serverRecord (c : Crypto) (S1 : ServerState) (ikB ds app : Bytes) :
    Ratchet.Msg Bytes × Ratchet.SendState Bytes :=
  Ratchet.sendStep (ratchetCrypto c) ⟨(rootChains c ds).1, 0⟩
    ⟨assocData (c.edPub S1.ikSk) ikB, 1, S1.sid⟩ (LE64 (S1.n + 1) ++ app)

/-- Response construction and transactional peer publication (spec §11–§14).  The
replay token has already been consumed in `S1`; a failure here leaves the peer map
and the allocation counter unchanged. -/
def serverEmit (c : Crypto) (S1 : ServerState) (ikB ds kemCt ePub app : Bytes) :
    Except ServerError KexResponse × ServerState :=
  if S1.n = maxKeyId then (.error .keyIdExhausted, S1)
  else if (S1.peers.lookup (S1.n + 1)).isSome then (.error .keyIdCollision, S1)
  else
    (.ok ⟨c.edPub S1.ikSk, ePub, kemCt,
        ⟨S1.sid, (serverRecord c S1 ikB ds app).1.idx + 1,
          (serverRecord c S1 ikB ds app).1.ct⟩, S1.n + 1⟩,
      { S1 with
        n := S1.n + 1
        peers := (S1.n + 1,
          ⟨ikB, assocData (c.edPub S1.ikSk) ikB, (serverRecord c S1 ikB ds app).2,
            ⟨(rootChains c ds).2, 0, []⟩⟩) :: S1.peers })

/-- The server's handling of a registration (spec §6–§14).

The ordering is the one the specification insists on: replay classification, then
the PQXDH computation, then **consumption of `RID`**, and only afterwards response
construction and the transactional peer commit.  Both components of the result are
returned in every case, so a rejection after consumption still reports the state in
which `RID` is consumed. -/
def serverRespond (c : Crypto) (S : ServerState) (m : InitKex) (eSk coins : Bytes)
    (app : Option Bytes) : Except ServerError KexResponse × ServerState :=
  match validateInit c m with
  | none => (.error .badEncoding, S)
  | some v =>
      if v.rid ∈ S.consumed then (.error .registrationReplay, S)
      else
        match c.xpkConv v.ikB with
        | none => (.error .badEncoding, S)
        | some ikBX =>
            if ¬ dhNonZero (serverDHs c S.ikSk eSk ikBX v.preKey v.otKey) then
              (.error .zeroDH, S)
            else if app = some [] then
              (.error .emptyAppMessage, { S with consumed := v.rid :: S.consumed })
            else
              serverEmit c { S with consumed := v.rid :: S.consumed } v.ikB
                (rootSecret c (ikmOf (serverDHs c S.ikSk eSk ikBX v.preKey v.otKey)
                  (c.encap v.kemPub coins).2))
                (c.encap v.kemPub coins).1 (c.xpub eSk) (app.getD [0xFF])

/-! ## Beacon processing of the response -/

/-- Why the beacon aborted a registration (spec §18). -/
inductive BeaconError where
  /-- The beacon was not in `InitSent`. -/
  | notInitSent
  /-- A malformed response or a failed identity-key conversion. -/
  | badResponse
  /-- Invalid ML-KEM ciphertext. -/
  | kemFailure
  /-- The response identity key is not the pinned one. -/
  | identityMismatch
  /-- Some X25519 contribution was all zero. -/
  | zeroDH
  /-- The initial ratchet record was not admissible (sequence, CTX or AEAD). -/
  | badRecord
  /-- The authenticated sender is not the pinned server identifier. -/
  | badSender
  /-- The authenticated plaintext is malformed. -/
  | badPlaintext
  /-- The assigned key identifier is not the one bound inside the record. -/
  | keyIdMismatch
deriving DecidableEq, Repr

/-- The root secret the beacon derives from its role-reversed contributions and the
decapsulated shared secret (spec §15). -/
def beaconRoot (c : Crypto) (ikSk preSk otSk ikSX ePub ss : Bytes) : Bytes :=
  rootSecret c (ikmOf (beaconDHs c ikSk preSk otSk ikSX ePub) ss)

/-- Beacon processing of `KexResponse` (spec §15–§18).  Every failure from
`InitSent` moves the beacon to `Aborted`; from any other state the beacon state is
returned unchanged, so neither `Established` nor `Aborted` can re-enter
registration. -/
def beaconFinish (c : Crypto) (s : BeaconState) (resp : KexResponse) :
    Except BeaconError ℕ × BeaconState :=
  match s with
  | .initSent b ikSk preSk otSk kemSk =>
      match c.decap kemSk resp.kemCipherText with
      | none => (.error .kemFailure, .aborted)
      | some ss =>
          if resp.identityKey ≠ b.ikPub then (.error .identityMismatch, .aborted)
          else
            match c.xpkConv resp.identityKey with
            | none => (.error .badResponse, .aborted)
            | some ikSX =>
                if ¬ dhNonZero (beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey) then
                  (.error .zeroDH, .aborted)
                else if resp.appFrame.keyId ≠ b.sid then (.error .badSender, .aborted)
                else if resp.appFrame.seq = 0 then (.error .badRecord, .aborted)
                else
                  match Ratchet.recvStep (ratchetCrypto c)
                      ⟨(rootChains c
                        (beaconRoot c ikSk preSk otSk ikSX resp.ephemeralKey ss)).1, 0, []⟩
                      ⟨assocData b.ikPub (c.edPub ikSk), resp.appFrame.seq,
                        resp.appFrame.keyId⟩
                      ⟨resp.appFrame.seq - 1, resp.appFrame.cipherText⟩ with
                  | (.error _, _) => (.error .badRecord, .aborted)
                  | (.ok pt, recv') =>
                      if pt.length ≤ 8 then (.error .badPlaintext, .aborted)
                      else if pt.take 8 ≠ LE64 resp.keyId then
                        (.error .keyIdMismatch, .aborted)
                      else
                        (.ok resp.keyId,
                          .established b ikSk resp.keyId
                            (assocData b.ikPub (c.edPub ikSk))
                            ⟨(rootChains c (beaconRoot c ikSk preSk otSk ikSX
                              resp.ephemeralKey ss)).2, 0⟩ recv')
  | _ => (.error .notInitSent, s)

end Pqxdh
