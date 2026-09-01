import BeaconcryptCore.Model.Pqxdh.Theorems
import BeaconcryptCore.Model.Pqxdh.Commit

/-!
# BeaconCrypt modified PQXDH — what the beacon's acceptance test rules out

Spec §16 requires the beacon to accept the server's first record through the *general*
receive-ratchet transition, including the CTX commitment check, and to insist that
the authenticated sender be the pinned `sid_S`.  This file draws the two
consequences of the committing record layer of
`BeaconcryptCore.Model.Pqxdh.Commit` at the level of the beacon transition:

* `Pqxdh.HonestRun.beacon_rejects_reordered_record` — an honest first record
  presented at any wire sequence number other than the one it was sealed at is
  rejected: the beacon aborts with `BadRecord`.  Together with the sender check
  (`Pqxdh.beaconFinish_bad_sender`) this is the statement that the record's position
  in the stream and its sender are authenticated, not merely transported.
* `Pqxdh.HonestRun.beacon_rejects_foreign_record` — a record sealed for a different
  session (a different associated data, i.e. a different ordered identity pair) is
  rejected as well.

Both results assume only that the CTX commitments of the two record contexts
involved differ (`Pqxdh.CtxDistinct`), the local and satisfiable form of collision
resistance used in `Commit.lean`; no global injectivity of BLAKE2b-512 — which would
contradict its fixed digest length — is assumed anywhere.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Pqxdh

/-- If the incoming index is not in the skipped store and the chain-derived key does
not authenticate the ciphertext, the receive transition rejects it and the receiving
state is unchanged. -/
theorem recvStep_error_of_dec_none {CK MK AD PT CT : Type}
    (c : Ratchet.Crypto CK MK AD PT CT) (s : Ratchet.RecvState CK MK) (ad : AD)
    (m : Ratchet.Msg CT) (hl : List.lookup m.idx s.skipped = none)
    (hd : c.dec (Ratchet.msgKeyAt c s.ck (m.idx - s.n)) ad m.ct = none) :
    ∃ e, Ratchet.recvStep c s ad m = (.error e, s) := by
  rw [Ratchet.recvStep, hl]
  split_ifs with h1 h2
  · exact ⟨.replay, rfl⟩
  · exact ⟨.tooManySkipped, rfl⟩
  · rw [hd]
    exact ⟨.authFail, rfl⟩

namespace HonestRun

variable (h : HonestRun)

/-- **The wire position of the first record is authenticated.**  Replaying the honest
first record at any sequence number other than the one it was sealed at makes the
beacon abort with `BadRecord`: the CTX commitment binds the sequence number, so the
record does not open at another position even though the beacon accepts *any*
admissible receive-ratchet record (spec §13, §16). -/
theorem beacon_rejects_reordered_record (hok : h.Ok) {seq' : ℕ}
    (hdist : CtxDistinct h.c (msgMaterial h.c h.chains.1)
      (Ratchet.msgKeyAt (ratchetCrypto h.c) h.chains.1 (seq' - 1))
      h.recordAD ⟨h.ad, seq', h.sid⟩)
    (hseq0 : seq' ≠ 0) :
    beaconFinish h.c h.beaconInitSent
        { h.response with appFrame := { h.response.appFrame with seq := seq' } }
      = (.error .badRecord, .aborted) := by
  have hdec : h.c.decap h.kemSkB h.kem.1 = some h.kem.2 := h.c.decap_encap h.kemSkB h.coins
  have hid : ¬ (h.c.edPub h.ikSkS ≠ h.binding.ikPub) := not_not_intro rfl
  have hconv : h.c.xpkConv (h.c.edPub h.ikSkS) = some (h.c.xpub (h.c.xsk h.ikSkS)) :=
    h.c.conv_agree h.ikSkS
  have hdhs : beaconDHs h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      (h.c.xpub h.eSk) = h.dhs :=
    beaconDHs_eq_serverDHs h.c h.ikSkS h.ikSkB h.preSkB h.otSkB h.eSk
  have hnz : ¬ ¬ dhNonZero (beaconDHs h.c h.ikSkB h.preSkB h.otSkB
      (h.c.xpub (h.c.xsk h.ikSkS)) (h.c.xpub h.eSk)) := by
    rw [hdhs]; exact not_not_intro hok.nonzero
  have hroot : beaconRoot h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      (h.c.xpub h.eSk) h.kem.2 = h.ds := by
    rw [beaconRoot, hdhs]; rfl
  -- the honest ciphertext does not open under the relabelled context
  have hct : h.sent.1.ct
      = (sealRecord h.c (msgMaterial h.c h.chains.1) h.recordAD h.plaintext).encode := rfl
  have hd : (ratchetCrypto h.c).dec
      (Ratchet.msgKeyAt (ratchetCrypto h.c) h.chains.1 (seq' - 1))
      (⟨h.ad, seq', h.sid⟩ : RecordAD) h.sent.1.ct = none := by
    rw [ratchetCrypto_dec, hct]
    exact openRecord_relabelled h.c hdist
  obtain ⟨e, herr⟩ :=
    recvStep_error_of_dec_none (ratchetCrypto h.c)
      (⟨h.chains.1, 0, []⟩ : Ratchet.RecvState Bytes (Bytes × Bytes))
      (⟨h.ad, seq', h.sid⟩ : RecordAD) ⟨seq' - 1, h.sent.1.ct⟩ rfl (by simpa using hd)
  simp only [beaconFinish, HonestRun.beaconInitSent, HonestRun.response, HonestRun.frame,
    hdec, if_neg hid, hconv, if_neg hnz, if_neg hseq0, hroot]
  rw [show (rootChains h.c h.ds).1 = h.chains.1 from rfl,
    show assocData h.binding.ikPub (h.c.edPub h.ikSkB) = h.ad from rfl, herr]
  split_ifs with hx
  · exact absurd rfl hx
  · rfl

/-- **A record from another session is not accepted.**  If the associated data the
record was sealed under differs from the one the beacon derives — a different ordered
identity pair (spec §9) — the beacon aborts with `BadRecord`. -/
theorem beacon_rejects_foreign_record (hok : h.Ok)
    {ikSPub' ikBPub' : Bytes} (mk' : Bytes × Bytes) (pt' : Bytes)
    (hdist : CtxDistinct h.c mk' (Ratchet.msgKeyAt (ratchetCrypto h.c) h.chains.1 0)
      ⟨assocData ikSPub' ikBPub', 1, h.sid⟩ ⟨h.ad, 1, h.sid⟩) :
    beaconFinish h.c h.beaconInitSent
        { h.response with
          appFrame := { h.response.appFrame with
            cipherText :=
              (sealRecord h.c mk' ⟨assocData ikSPub' ikBPub', 1, h.sid⟩ pt').encode } }
      = (.error .badRecord, .aborted) := by
  have hdec : h.c.decap h.kemSkB h.kem.1 = some h.kem.2 := h.c.decap_encap h.kemSkB h.coins
  have hid : ¬ (h.c.edPub h.ikSkS ≠ h.binding.ikPub) := not_not_intro rfl
  have hconv : h.c.xpkConv (h.c.edPub h.ikSkS) = some (h.c.xpub (h.c.xsk h.ikSkS)) :=
    h.c.conv_agree h.ikSkS
  have hdhs : beaconDHs h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      (h.c.xpub h.eSk) = h.dhs :=
    beaconDHs_eq_serverDHs h.c h.ikSkS h.ikSkB h.preSkB h.otSkB h.eSk
  have hnz : ¬ ¬ dhNonZero (beaconDHs h.c h.ikSkB h.preSkB h.otSkB
      (h.c.xpub (h.c.xsk h.ikSkS)) (h.c.xpub h.eSk)) := by
    rw [hdhs]; exact not_not_intro hok.nonzero
  have hroot : beaconRoot h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      (h.c.xpub h.eSk) h.kem.2 = h.ds := by
    rw [beaconRoot, hdhs]; rfl
  have hd : (ratchetCrypto h.c).dec (Ratchet.msgKeyAt (ratchetCrypto h.c) h.chains.1 0)
      (⟨h.ad, 1, h.sid⟩ : RecordAD)
      (sealRecord h.c mk' ⟨assocData ikSPub' ikBPub', 1, h.sid⟩ pt').encode = none := by
    rw [ratchetCrypto_dec]
    exact openRecord_relabelled h.c hdist
  obtain ⟨e, herr⟩ :=
    recvStep_error_of_dec_none (ratchetCrypto h.c)
      (⟨h.chains.1, 0, []⟩ : Ratchet.RecvState Bytes (Bytes × Bytes))
      (⟨h.ad, 1, h.sid⟩ : RecordAD)
      ⟨0, (sealRecord h.c mk' ⟨assocData ikSPub' ikBPub', 1, h.sid⟩ pt').encode⟩ rfl
      (by simpa using hd)
  simp only [beaconFinish, HonestRun.beaconInitSent, HonestRun.response, HonestRun.frame,
    hdec, if_neg hid, hconv, if_neg hnz, hroot]
  rw [if_neg (by decide : ¬ (1 : ℕ) = 0),
    show (rootChains h.c h.ds).1 = h.chains.1 from rfl,
    show assocData h.binding.ikPub (h.c.edPub h.ikSkB) = h.ad from rfl,
    show (1 : ℕ) - 1 = 0 from rfl, herr]
  split_ifs with hx
  · exact absurd rfl hx
  · rfl

end HonestRun

end Pqxdh
