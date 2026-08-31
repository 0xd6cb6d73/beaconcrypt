import BeaconcryptCore.Model.Pqxdh.Protocol
import Mathlib.Tactic.SplitIfs

/-!
# BeaconCrypt modified PQXDH — properties of the ideal model

Fourth and last part of the ideal model of `pqxdh_spec.md`.  It proves the
behavioural properties the specification states:

* one-shot registration (§5, §20) and the absorbing `Established`/`Aborted`
  states (§17, §18, §20);
* validation of a well-formed bundle, and rejection of a bundle whose X25519 role
  tags have been swapped (§4, §6, §21.3);
* replay classification by exact equality of `RID = IK_B ‖ OT_B` (§6), the fact
  that `RID` is consumed *before* the response is constructed and stays consumed
  when response construction fails (§8, §14, §18, §20), and the transactional peer
  commit (§14);
* the drop of the registration-local key material on leaving `InitSent` (§17,
  §18);
* the honest agreement relation (§19): the two parties derive the same root
  secret, the same associated data and complementary directional chain keys, the
  beacon accepts the server's first committing record, recovers the application
  message, and both sides agree on the assigned identifier and the ordered
  identity pair.

A concrete (toy) instance of `Pqxdh.Crypto` at the end shows that the assumptions
on the primitives are jointly satisfiable, so none of the results is vacuous.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Pqxdh

/-! ## Registration is one-shot (spec §5, §20) -/

theorem beaconInit_fresh (c : Crypto) (b : ServerBinding) (ikSk preSk kemSk otSk : Bytes) :
    beaconInit c (.fresh b ikSk preSk kemSk) otSk
      = some (initKexOf c ikSk preSk otSk kemSk, .initSent b ikSk preSk otSk kemSk) := rfl

/-- No second registration bundle can be emitted from `InitSent`. -/
theorem beaconInit_initSent (c : Crypto) (b : ServerBinding)
    (ikSk preSk otSk kemSk otSk' : Bytes) :
    beaconInit c (.initSent b ikSk preSk otSk kemSk) otSk' = none := rfl

/-- A beacon provisioned with a pregenerated one-time key emits its bundle with that
key, and the freshly offered one is ignored (spec §2.2, §5). -/
theorem beaconInit_freshWithCoins (c : Crypto) (b : ServerBinding)
    (ikSk preSk otSk kemSk otSk' : Bytes) :
    beaconInit c (.freshWithCoins b ikSk preSk otSk kemSk) otSk'
      = some (initKexOf c ikSk preSk otSk kemSk, .initSent b ikSk preSk otSk kemSk) := rfl

/-- An established beacon cannot restart registration. -/
theorem beaconInit_established (c : Crypto) (b : ServerBinding) (ikSk : Bytes) (kid : ℕ)
    (ad : Bytes) (send : Ratchet.SendState Bytes)
    (recv : Ratchet.RecvState Bytes (Bytes × Bytes)) (otSk : Bytes) :
    beaconInit c (.established b ikSk kid ad send recv) otSk = none := rfl

/-- An aborted beacon cannot restart registration. -/
theorem beaconInit_aborted (c : Crypto) (otSk : Bytes) :
    beaconInit c .aborted otSk = none := rfl

/-! ## Validation of the registration bundle (spec §4, §6) -/

/-- An honestly generated bundle validates, and validation recovers exactly the four
public values. -/
theorem validateInit_initKexOf (c : Crypto) (ikSk preSk otSk kemSk : Bytes) :
    validateInit c (initKexOf c ikSk preSk otSk kemSk)
      = some ⟨c.edPub ikSk, c.xpub preSk, c.xpub otSk, c.kemPub kemSk⟩ := by
  simp [validateInit, initKexOf, parseSigTag_tagSig (c.edPub_length ikSk),
    c.verify_sign, parseXTag_tagX (c.xpub_length preSk),
    parseXTag_tagX (c.xpub_length otSk), parsePQTag_tagPQ (c.kemPub_length kemSk)]

/-- The X25519 role tags are not interchangeable: a bundle in which the prekey and
the one-time key carry each other's role tags is rejected, even though both
signatures are valid. -/
theorem validateInit_swapped_roles (c : Crypto) (ikSk preSk otSk kemSk : Bytes) :
    validateInit c
        { identityKey := tagSig (c.edPub ikSk)
          preKey := c.sign ikSk (tagX roleOtk (c.xpub preSk))
          oneTimeKey := c.sign ikSk (tagX rolePre (c.xpub otSk))
          pqKey := c.sign ikSk (tagPQ (c.kemPub kemSk)) } = none := by
  simp [validateInit, parseSigTag_tagSig (c.edPub_length ikSk), c.verify_sign,
    parseXTag_pre_tagX_otk]

/-! ## Server replay classification and the consumption order (spec §6, §8, §14) -/

/-- A registration whose `RID` has already been consumed is rejected as a replay, and
the server state is untouched. -/
theorem serverRespond_replay (c : Crypto) (S : ServerState) (m : InitKex)
    (eSk coins : Bytes) (app : Option Bytes) (v : ValidInit)
    (hv : validateInit c m = some v) (hr : v.rid ∈ S.consumed) :
    serverRespond c S m eSk coins app = (.error .registrationReplay, S) := by
  simp only [serverRespond, hv]
  rw [if_pos hr]

/-- Response construction never touches the consumed set. -/
theorem serverEmit_consumed (c : Crypto) (S1 : ServerState) (ikB ds kemCt ePub app : Bytes) :
    (serverEmit c S1 ikB ds kemCt ePub app).2.consumed = S1.consumed := by
  unfold serverEmit
  split_ifs <;> rfl

/-- Response construction is transactional: if it fails, the allocation counter and
the peer map are unchanged. -/
theorem serverEmit_failure_state (c : Crypto) (S1 : ServerState)
    (ikB ds kemCt ePub app : Bytes) (e : ServerError)
    (h : (serverEmit c S1 ikB ds kemCt ePub app).1 = .error e) :
    (serverEmit c S1 ikB ds kemCt ePub app).2 = S1 := by
  unfold serverEmit at h ⊢
  split_ifs at h ⊢ <;> rfl

/-- On success the server commits transactionally: the allocation counter advances to
the freshly assigned identifier, which is also the one carried in the response, and
the peer is published under it. -/
theorem serverEmit_ok (c : Crypto) (S1 : ServerState) (ikB ds kemCt ePub app : Bytes)
    (r : KexResponse) (h : (serverEmit c S1 ikB ds kemCt ePub app).1 = .ok r) :
    r.keyId = S1.n + 1 ∧ (serverEmit c S1 ikB ds kemCt ePub app).2.n = S1.n + 1 ∧
      ∃ p : Peer, (serverEmit c S1 ikB ds kemCt ePub app).2.peers
        = (S1.n + 1, p) :: S1.peers ∧ p.ikPub = ikB := by
  unfold serverEmit at h ⊢
  split_ifs at h ⊢
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, _, rfl, rfl⟩

/-- Counter exhaustion is reported and nothing is published; no wrapping occurs
(spec §11). -/
theorem serverEmit_exhausted (c : Crypto) (S1 : ServerState) (ikB ds kemCt ePub app : Bytes)
    (h : S1.n = maxKeyId) :
    serverEmit c S1 ikB ds kemCt ePub app = (.error .keyIdExhausted, S1) := by
  rw [serverEmit, if_pos h]

/-- An occupied proposed identifier is reported and nothing is published
(spec §11). -/
theorem serverEmit_collision (c : Crypto) (S1 : ServerState) (ikB ds kemCt ePub app : Bytes)
    (h : S1.n ≠ maxKeyId) (hc : (S1.peers.lookup (S1.n + 1)).isSome) :
    serverEmit c S1 ikB ds kemCt ePub app = (.error .keyIdCollision, S1) := by
  rw [serverEmit, if_neg h, if_pos hc]

/-- An explicitly supplied empty application message is rejected — but only after the
replay token has been consumed (spec §12). -/
theorem serverRespond_empty_app (c : Crypto) (S : ServerState) (m : InitKex)
    (eSk coins ikBX : Bytes) (v : ValidInit) (hv : validateInit c m = some v)
    (hr : v.rid ∉ S.consumed) (hx : c.xpkConv v.ikB = some ikBX)
    (hnz : dhNonZero (serverDHs c S.ikSk eSk ikBX v.preKey v.otKey)) :
    serverRespond c S m eSk coins (some []) =
      (.error .emptyAppMessage, { S with consumed := v.rid :: S.consumed }) := by
  simp only [serverRespond, hv, hx, if_neg hr, if_neg (not_not_intro hnz), if_true]

/-- Whatever the outcome, the consumed set only ever grows. -/
theorem serverRespond_consumed_mono (c : Crypto) (S : ServerState) (m : InitKex)
    (eSk coins : Bytes) (app : Option Bytes) :
    S.consumed ⊆ (serverRespond c S m eSk coins app).2.consumed := by
  unfold serverRespond
  split
  · exact List.Subset.refl _
  · split
    · exact List.Subset.refl _
    · split
      · exact List.Subset.refl _
      · split
        · exact List.Subset.refl _
        · split
          · exact List.subset_cons_self _ _
          · rw [serverEmit_consumed]
            exact List.subset_cons_self _ _

/-- Once the server has got past validation, replay classification and the PQXDH
computation, `RID` is consumed — whether or not the response is then successfully
constructed.  This is the ordering
`consume replay token ≺ response construction ≺ peer commit` of spec §20. -/
theorem serverRespond_consumes (c : Crypto) (S : ServerState) (m : InitKex)
    (eSk coins : Bytes) (app : Option Bytes) (v : ValidInit)
    (hv : validateInit c m = some v) (hr : v.rid ∉ S.consumed)
    (h : (serverRespond c S m eSk coins app).1 ≠ .error .badEncoding)
    (h' : (serverRespond c S m eSk coins app).1 ≠ .error .zeroDH) :
    v.rid ∈ (serverRespond c S m eSk coins app).2.consumed := by
  rcases hx : c.xpkConv v.ikB with _ | ikBX
  · simp only [serverRespond, hv, hx, if_neg hr] at h
    simp at h
  · simp only [serverRespond, hv, hx, if_neg hr] at h' ⊢
    by_cases hz : ¬ dhNonZero (serverDHs c S.ikSk eSk ikBX v.preKey v.otKey)
    · simp only [if_pos hz] at h'
      simp at h'
    · simp only [if_neg hz]
      by_cases he : app = some []
      · simp only [if_pos he]
        simp
      · simp only [if_neg he, serverEmit_consumed]
        simp

/-- Consequently a replayed bundle is always rejected the second time round, whether
the first attempt succeeded or failed during response construction. -/
theorem serverRespond_replay_after (c : Crypto) (S : ServerState) (m : InitKex)
    (eSk coins eSk' coins' : Bytes) (app app' : Option Bytes) (v : ValidInit)
    (hv : validateInit c m = some v) (hr : v.rid ∉ S.consumed)
    (h : (serverRespond c S m eSk coins app).1 ≠ .error .badEncoding)
    (h' : (serverRespond c S m eSk coins app).1 ≠ .error .zeroDH) :
    serverRespond c (serverRespond c S m eSk coins app).2 m eSk' coins' app'
      = (.error .registrationReplay, (serverRespond c S m eSk coins app).2) :=
  serverRespond_replay c _ m eSk' coins' app' v hv
    (serverRespond_consumes c S m eSk coins app v hv hr h h')

/-! ## Beacon failure semantics (spec §17, §18) -/

/-- From any state other than `InitSent` the beacon rejects a response and its state
is unchanged: neither `Established` nor `Aborted` re-enters registration. -/
theorem beaconFinish_not_initSent (c : Crypto) (s : BeaconState) (resp : KexResponse)
    (h : ∀ b ikSk preSk otSk kemSk, s ≠ .initSent b ikSk preSk otSk kemSk) :
    beaconFinish c s resp = (.error .notInitSent, s) := by
  cases s with
  | initSent b ikSk preSk otSk kemSk => exact absurd rfl (h b ikSk preSk otSk kemSk)
  | fresh => rfl
  | freshWithCoins => rfl
  | established => rfl
  | aborted => rfl

/-- Any failure while processing the response moves the beacon from `InitSent` to
`Aborted`. -/
theorem beaconFinish_aborted_of_error (c : Crypto) (b : ServerBinding)
    (ikSk preSk otSk kemSk : Bytes) (resp : KexResponse) (e : BeaconError)
    (h : (beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp).1 = .error e) :
    (beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp).2 = .aborted := by
  revert h
  unfold beaconFinish
  repeat' split
  all_goals simp

/-- Leaving `InitSent` — successfully or not — drops the registration prekey, the
one-time key and the ML-KEM key from the beacon state. -/
theorem beaconFinish_drops_registration_keys (c : Crypto) (b : ServerBinding)
    (ikSk preSk otSk kemSk : Bytes) (resp : KexResponse) :
    (beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp).2.regSecrets = none := by
  unfold beaconFinish
  repeat' split
  all_goals rfl

/-- The pinned server identity is enforced: a response carrying a different Ed25519
identity key aborts the registration (spec §15). -/
theorem beaconFinish_identity_mismatch (c : Crypto) (b : ServerBinding)
    (ikSk preSk otSk kemSk ss : Bytes) (resp : KexResponse)
    (hdec : c.decap kemSk resp.kemCipherText = some ss)
    (hne : resp.identityKey ≠ b.ikPub) :
    beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp
      = (.error .identityMismatch, .aborted) := by
  simp only [beaconFinish, hdec, if_pos hne]

/-- The authenticated sender is enforced: a first record whose sender identifier is
not the pinned one aborts the registration (spec §16). -/
theorem beaconFinish_bad_sender (c : Crypto) (b : ServerBinding)
    (ikSk preSk otSk kemSk ss ikSX : Bytes) (resp : KexResponse)
    (hdec : c.decap kemSk resp.kemCipherText = some ss)
    (hid : resp.identityKey = b.ikPub)
    (hconv : c.xpkConv resp.identityKey = some ikSX)
    (hnz : dhNonZero (beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey))
    (hsid : resp.appFrame.keyId ≠ b.sid) :
    beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp
      = (.error .badSender, .aborted) := by
  simp only [beaconFinish, hdec, if_neg (not_not_intro hid), hconv,
    if_neg (not_not_intro hnz), if_pos hsid]

/-! ## X25519 agreement of the two role-reversed computations (spec §19) -/

/-- The beacon's four contributions are exactly the server's four contributions. -/
theorem beaconDHs_eq_serverDHs (c : Crypto) (ikSkS ikSkB preSk otSk eSk : Bytes) :
    beaconDHs c ikSkB preSk otSk (c.xpub (c.xsk ikSkS)) (c.xpub eSk)
      = serverDHs c ikSkS eSk (c.xpub (c.xsk ikSkB)) (c.xpub preSk) (c.xpub otSk) := by
  simp only [beaconDHs, serverDHs, Prod.mk.injEq]
  exact ⟨c.dh_comm _ _, c.dh_comm _ _, c.dh_comm _ _, c.dh_comm _ _⟩

/-! ## An honest run (spec §19)

The data of a single honest registration: the two parties' long-term keys, the
server's ephemeral and ML-KEM randomness, and the initial application message. -/

/-- All the inputs of one honest registration. -/
structure HonestRun where
  /-- The cryptographic primitives. -/
  c : Crypto
  /-- The server's Ed25519 identity secret key. -/
  ikSkS : Bytes
  /-- The server's numeric identifier. -/
  sid : ℕ
  /-- The server's allocation counter. -/
  n : ℕ
  /-- The server's published peers. -/
  peers : List (ℕ × Peer)
  /-- The server's consumed-registration set. -/
  consumed : List Bytes
  /-- The beacon's Ed25519 identity secret key. -/
  ikSkB : Bytes
  /-- The beacon's X25519 prekey secret. -/
  preSkB : Bytes
  /-- The beacon's X25519 one-time key secret. -/
  otSkB : Bytes
  /-- The beacon's ML-KEM decapsulation key. -/
  kemSkB : Bytes
  /-- The server's X25519 ephemeral secret. -/
  eSk : Bytes
  /-- The server's ML-KEM encapsulation randomness. -/
  coins : Bytes
  /-- The server's initial application message. -/
  app : Bytes

namespace HonestRun

variable (h : HonestRun)

/-- The server state before the registration. -/
def server : ServerState := ⟨h.ikSkS, h.sid, h.n, h.peers, h.consumed⟩

/-- The binding pinned in the beacon. -/
def binding : ServerBinding := ⟨h.c.edPub h.ikSkS, h.sid⟩

/-- The beacon's Ed25519 identity public key. -/
def ikBPub : Bytes := h.c.edPub h.ikSkB

/-- The bundle the beacon emits. -/
def initMsg : InitKex := initKexOf h.c h.ikSkB h.preSkB h.otSkB h.kemSkB

/-- The validated content of that bundle. -/
def valid : ValidInit :=
  ⟨h.ikBPub, h.c.xpub h.preSkB, h.c.xpub h.otSkB, h.c.kemPub h.kemSkB⟩

/-- The registration identifier of the run. -/
def rid : Bytes := h.valid.rid

/-- The beacon before registration. -/
def beaconFresh : BeaconState := .fresh h.binding h.ikSkB h.preSkB h.kemSkB

/-- The beacon after emitting its bundle. -/
def beaconInitSent : BeaconState :=
  .initSent h.binding h.ikSkB h.preSkB h.otSkB h.kemSkB

/-- The server's ML-KEM encapsulation. -/
def kem : Bytes × Bytes := h.c.encap (h.c.kemPub h.kemSkB) h.coins

/-- The four X25519 contributions. -/
def dhs : Bytes × Bytes × Bytes × Bytes :=
  serverDHs h.c h.ikSkS h.eSk (h.c.xpub (h.c.xsk h.ikSkB)) (h.c.xpub h.preSkB)
    (h.c.xpub h.otSkB)

/-- The shared root secret. -/
def ds : Bytes := rootSecret h.c (ikmOf h.dhs h.kem.2)

/-- The shared associated data. -/
def ad : Bytes := assocData (h.c.edPub h.ikSkS) h.ikBPub

/-- The initial pair of directional chain keys `(L, R)`. -/
def chains : Bytes × Bytes := rootChains h.c h.ds

/-- The identifier assigned to the beacon. -/
def kid : ℕ := h.n + 1

/-- The associated data of the first record. -/
def recordAD : RecordAD := ⟨h.ad, 1, h.sid⟩

/-- The plaintext of the first record, `LE64(kid) ‖ M`. -/
def plaintext : Bytes := LE64 h.kid ++ h.app

/-- The first send-ratchet step of the server. -/
def sent : Ratchet.Msg Bytes × Ratchet.SendState Bytes :=
  Ratchet.sendStep (ratchetCrypto h.c) ⟨h.chains.1, 0⟩ h.recordAD h.plaintext

/-- The first record on the wire. -/
def frame : CryptoFrame := ⟨h.sid, 1, h.sent.1.ct⟩

/-- The server's response. -/
def response : KexResponse :=
  ⟨h.c.edPub h.ikSkS, h.c.xpub h.eSk, h.kem.1, h.frame, h.kid⟩

/-- The peer the server publishes. -/
def peer : Peer := ⟨h.ikBPub, h.ad, h.sent.2, ⟨h.chains.2, 0, []⟩⟩

/-- The server state after the registration. -/
def server' : ServerState :=
  ⟨h.ikSkS, h.sid, h.kid, (h.kid, h.peer) :: h.peers, h.rid :: h.consumed⟩

/-- The beacon's receive ratchet after admitting the first record. -/
def beaconRecv : Ratchet.RecvState Bytes (Bytes × Bytes) :=
  ⟨nextChain h.c h.chains.1, 1, []⟩

/-- The established beacon. -/
def beaconEstablished : BeaconState :=
  .established h.binding h.ikSkB h.kid h.ad ⟨h.chains.2, 0⟩ h.beaconRecv

/-- The side conditions of an honest run: the registration is fresh, no contribution
degenerates, the allocation counter is not exhausted, the proposed identifier is
free, and the application message is non-empty. -/
structure Ok (h : HonestRun) : Prop where
  /-- The registration identifier has not been consumed. -/
  freshRid : h.rid ∉ h.consumed
  /-- No X25519 contribution is all zero. -/
  nonzero : dhNonZero h.dhs
  /-- The allocation counter is not exhausted. -/
  notExhausted : h.n ≠ maxKeyId
  /-- The proposed identifier is free. -/
  free : h.peers.lookup h.kid = none
  /-- The application message is non-empty. -/
  appNonempty : h.app ≠ []

/-- The beacon emits its bundle and moves to `InitSent`. -/
theorem initiation : beaconInit h.c h.beaconFresh h.otSkB = some (h.initMsg, h.beaconInitSent) :=
  rfl

/-- The server validates the honest bundle. -/
theorem validate : validateInit h.c h.initMsg = some h.valid :=
  validateInit_initKexOf h.c h.ikSkB h.preSkB h.otSkB h.kemSkB

/-- The server accepts the honest bundle, emits the response and commits the peer. -/
theorem serverStep (hok : h.Ok) :
    serverRespond h.c h.server h.initMsg h.eSk h.coins (some h.app)
      = (.ok h.response, h.server') := by
  have hrid : h.valid.rid ∉ h.consumed := hok.freshRid
  have hconv : h.c.xpkConv h.valid.ikB = some (h.c.xpub (h.c.xsk h.ikSkB)) :=
    h.c.conv_agree h.ikSkB
  have hnz : ¬ ¬ dhNonZero
      (serverDHs h.c h.ikSkS h.eSk (h.c.xpub (h.c.xsk h.ikSkB)) h.valid.preKey
        h.valid.otKey) := not_not_intro hok.nonzero
  have happ : ¬ (some h.app = some ([] : Bytes)) := by
    simpa using hok.appNonempty
  have hfree : ¬ ((h.peers.lookup (h.n + 1)).isSome = true) := by
    have := hok.free
    simp only [HonestRun.kid] at this
    simp [this]
  simp only [serverRespond, h.validate, hconv, Option.getD_some, serverEmit,
    HonestRun.server, if_neg hrid, if_neg hnz, if_neg happ, if_neg hok.notExhausted,
    if_neg hfree]
  rfl

/-- The beacon accepts the honest response and becomes established with the assigned
identifier. -/
theorem beaconStep (hok : h.Ok) :
    beaconFinish h.c h.beaconInitSent h.response = (.ok h.kid, h.beaconEstablished) := by
  have hdec : h.c.decap h.kemSkB h.response.kemCipherText = some h.kem.2 :=
    h.c.decap_encap h.kemSkB h.coins
  have hid : ¬ (h.response.identityKey ≠ h.binding.ikPub) := not_not_intro rfl
  have hconv : h.c.xpkConv h.response.identityKey = some (h.c.xpub (h.c.xsk h.ikSkS)) :=
    h.c.conv_agree h.ikSkS
  have hdhs : beaconDHs h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      h.response.ephemeralKey = h.dhs :=
    beaconDHs_eq_serverDHs h.c h.ikSkS h.ikSkB h.preSkB h.otSkB h.eSk
  have hnz : ¬ ¬ dhNonZero (beaconDHs h.c h.ikSkB h.preSkB h.otSkB
      (h.c.xpub (h.c.xsk h.ikSkS)) h.response.ephemeralKey) := by
    rw [hdhs]; exact not_not_intro hok.nonzero
  have hsid : ¬ (h.response.appFrame.keyId ≠ h.binding.sid) := not_not_intro rfl
  have hseq : ¬ (h.response.appFrame.seq = 0) := by
    simp [HonestRun.response, HonestRun.frame]
  have hroot : beaconRoot h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      h.response.ephemeralKey h.kem.2 = h.ds := by
    rw [beaconRoot, hdhs]; rfl
  have hwf : Ratchet.RecvWf
      (⟨h.chains.1, 0, []⟩ : Ratchet.RecvState Bytes (Bytes × Bytes)) :=
    ⟨by simp [Ratchet.maxSkip], by simp, by simp⟩
  have hrecv : Ratchet.recvStep (ratchetCrypto h.c)
      ⟨(rootChains h.c h.ds).1, 0, []⟩
      ⟨assocData h.binding.ikPub (h.c.edPub h.ikSkB), h.response.appFrame.seq,
        h.response.appFrame.keyId⟩
      ⟨h.response.appFrame.seq - 1, h.response.appFrame.cipherText⟩
      = (.ok h.plaintext, h.beaconRecv) :=
    Ratchet.recvStep_of_sendStep_inOrder (ratchetCrypto h.c) h.chains.1 0 [] hwf
      h.recordAD h.plaintext
  have hlen : ¬ (h.plaintext.length ≤ 8) := by
    have : h.app ≠ [] := hok.appNonempty
    simp only [HonestRun.plaintext, List.length_append, LE64_length]
    have : 0 < h.app.length := List.length_pos_iff.2 this
    omega
  have htake : ¬ (h.plaintext.take 8 ≠ LE64 h.response.keyId) := by
    simp only [ne_eq, not_not, HonestRun.plaintext]
    rw [← LE64_length h.kid, List.take_left]
    rfl
  simp only [beaconFinish, HonestRun.beaconInitSent, hdec, if_neg hid, hconv, if_neg hnz,
    if_neg hsid, if_neg hseq, hroot, hrecv, if_neg hlen, if_neg htake]
  rfl

/-! ### The agreement relation (spec §19) -/

/-- Both parties agree on the assigned numeric identifier: it is the clear
`KexResponse.keyId`, the identifier the server published the peer under, and the
identifier the beacon authenticated inside the first record. -/
theorem keyId_agreement (hok : h.Ok) :
    h.response.keyId = h.kid ∧ (h.server'.peers.lookup h.kid) = some h.peer ∧
      (beaconFinish h.c h.beaconInitSent h.response).1 = .ok h.kid := by
  refine ⟨rfl, by simp [server'], ?_⟩
  rw [h.beaconStep hok]

/-- Both parties compute the same associated data, hence agree on the ordered
identity pair `(IK_S, IK_B)`. -/
theorem ad_agreement : h.peer.ad = h.ad ∧
    h.ad = assocData h.binding.ikPub (h.c.edPub h.ikSkB) := ⟨rfl, rfl⟩

/-- The directional chains are complementary: the server's sending chain is the
beacon's receiving chain and vice versa. -/
theorem chain_agreement :
    h.peer.recv.ck = h.chains.2 ∧
      (match h.beaconEstablished with
        | .established _ _ _ _ send _ => send.ck = h.chains.2
        | _ => False) ∧
      h.peer.send.ck = nextChain h.c h.chains.1 ∧
      h.beaconRecv.ck = nextChain h.c h.chains.1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The beacon recovers the server's initial application message from the first
record. -/
theorem app_delivered :
    (Ratchet.recvStep (ratchetCrypto h.c) ⟨h.chains.1, 0, []⟩ h.recordAD h.sent.1).1
      = .ok h.plaintext ∧ h.plaintext.drop 8 = h.app := by
  have hwf : Ratchet.RecvWf
      (⟨h.chains.1, 0, []⟩ : Ratchet.RecvState Bytes (Bytes × Bytes)) :=
    ⟨by simp [Ratchet.maxSkip], by simp, by simp⟩
  refine ⟨?_, ?_⟩
  · show (Ratchet.recvStep (ratchetCrypto h.c) ⟨h.chains.1, 0, []⟩ h.recordAD
      (Ratchet.sendStep (ratchetCrypto h.c) ⟨h.chains.1, 0⟩ h.recordAD h.plaintext).1).1
        = .ok h.plaintext
    rw [Ratchet.recvStep_of_sendStep_inOrder (ratchetCrypto h.c) h.chains.1 0 [] hwf
      h.recordAD h.plaintext]
  · simp only [HonestRun.plaintext]
    rw [← LE64_length h.kid, List.drop_left]

end HonestRun

end Pqxdh
