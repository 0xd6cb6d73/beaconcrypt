import BeaconcryptCore.Refinement.PqxdhProtocol
import BeaconcryptCore.Model.Pqxdh.Theorems

/-!
# The generated code reproduces a whole honest PQXDH registration

`BeaconcryptCore/Refinement/PqxdhProtocol.lean` proves the four generated PQXDH
transitions correct against the handwritten ideal model, one transition at a time.
This file composes them into a single end-to-end statement about the honest run
`Pqxdh.HonestRun` of `BeaconcryptCore/Model/Pqxdh/Theorems.lean`.

The extracted core is cryptography free, so an honest run has to be told which
generated values the primitives produced.  `GenHonestRun h` bundles exactly that
data: the generated provisioning inputs, the generated server state and the
generated inputs of the beacon's completion step, together with the (only)
assumption that they abstract to the values of the ideal run `h`.

`honest_run_refines` then says: on this data the generated pipeline
`beacon_start` → `validate_init_kex` → `serverRegister` → `beaconFinishDriver`
runs to completion without a single rejection and produces, on both sides, the
identifier, the peer entry, the associated data and the pinned binding of the ideal
run — while the ideal run itself takes the two steps `Pqxdh.HonestRun.serverStep`
and `Pqxdh.HonestRun.beaconStep`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open beaconcrypt_core

namespace PqxdhRefinement

/-- The generated data of one honest registration: everything the extracted,
cryptography-free core has to be handed, together with the assumption that it
abstracts to the corresponding value of the ideal honest run `h`. -/
structure GenHonestRun (h : Pqxdh.HonestRun) where
  /-- The provisioned beacon. -/
  fresh : pqxdh.BeaconFresh
  /-- The beacon's long-term public keys. -/
  startInputs : pqxdh.BeaconStartInputs
  /-- The beacon's one-time public key. -/
  startCoins : pqxdh.BeaconCoins
  /-- The server state before the registration. -/
  serverState : pqxdh.ServerState
  /-- The server's identity binding. -/
  serverBinding : pqxdh.ServerBinding
  /-- The server's ephemeral public key and ML-KEM ciphertext. -/
  serverCoins : pqxdh.ServerCoins
  /-- The PQXDH transcript as the server's primitives computed it. -/
  serverSecrets : pqxdh.PqxdhSharedSecrets
  /-- The inputs of the beacon's completion step. -/
  finishInputs : pqxdh.BeaconFinishInputs
  /-- The sender identifier authenticated by the first record. -/
  authSenderId : Std.U64
  /-- The key-identifier binding authenticated by the first record. -/
  authBinding : Std.Array Std.U8 8#usize
  /-- The beacon pins the server binding of the run. -/
  pinned : absBinding fresh.expected_server_binding = h.binding
  /-- The beacon's identity key. -/
  beaconIk : absBytes startInputs.identity_public_key = h.c.edPub h.ikSkB
  /-- The beacon's prekey. -/
  beaconPre : absBytes startInputs.prekey_public_key = h.c.xpub h.preSkB
  /-- The beacon's one-time key. -/
  beaconOt : absBytes startCoins.one_time_public_key = h.c.xpub h.otSkB
  /-- The beacon's ML-KEM encapsulation key. -/
  beaconKem : absBytes startInputs.pq_public_key = h.c.kemPub h.kemSkB
  /-- The server's allocation counter. -/
  counter : serverState.last_key_id.val = h.n
  /-- The server's identity key. -/
  serverIk : absBytes serverBinding.identity_public_key = h.c.edPub h.ikSkS
  /-- The server's PQXDH transcript. -/
  serverDh : absDHs serverSecrets = h.dhs
  /-- The server's ML-KEM shared secret. -/
  serverSs : absBytes serverSecrets.kem_shared_secret = h.kem.2
  /-- The server identity the beacon reads off the response. -/
  respIk : absBytes finishInputs.response_server_identity = h.c.edPub h.ikSkS
  /-- The identifier the response assigns. -/
  respKid : finishInputs.assigned_key_id.val = h.kid
  /-- The beacon's PQXDH transcript. -/
  beaconDh : absDHs finishInputs.shared_secrets = h.dhs
  /-- The authenticated sender of the first record. -/
  authSender : authSenderId.val = h.sid
  /-- The identifier bound by the first record. -/
  authBound : absBytes authBinding = Pqxdh.LE64 h.kid

/-- **End-to-end refinement of an honest registration.**  On the values the
primitives produce in the honest run `h`, the generated pipeline runs to completion:
the generated bundle is accepted by the generated parser with the ideal validated
content, the generated server allocates the ideal identifier and publishes the ideal
peer (identity key and associated data), and the generated beacon completes with the
ideal identifier and keeps the pinned binding — exactly the outcome of the two ideal
transitions `Pqxdh.serverRespond` and `Pqxdh.beaconFinish`. -/
theorem honest_run_refines (h : Pqxdh.HonestRun) (hok : h.Ok) (g : GenHonestRun h) :
    ∃ (out : pqxdh.BeaconStart) (v : pqxdh.VerifiedInitKex) (st : pqxdh.ServerState)
      (peer : pqxdh.EstablishedPeer) (est : pqxdh.BeaconEstablished),
      -- the beacon emits its bundle
      pqxdh.beacon_start g.fresh g.startInputs g.startCoins = ok out ∧
      -- the server validates it, to the ideal validated bundle
      pqxdh.validate_init_kex out.message = ok (core.result.Result.Ok v) ∧
      absVerified v = h.valid ∧
      -- the server registers the beacon
      serverRegister g.serverState v pqxdh.RegistrationStatus.Fresh g.serverBinding
          g.serverCoins g.serverSecrets pqxdh.KeyIdAvailability.Available
        = ok (core.result.Result.Ok (st, peer)) ∧
      st.last_key_id.val = h.kid ∧
      peer.key_id.val = h.kid ∧
      absBytes peer.identity_public_key = h.ikBPub ∧
      absBytes peer.associated_data = h.ad ∧
      -- the beacon completes the registration
      beaconFinishDriver out.state g.finishInputs g.authSenderId g.authBinding
        = ok (core.result.Result.Ok est) ∧
      est.assigned_key_id.val = h.kid ∧
      absBinding est.server_binding = h.binding ∧
      -- and this is exactly the ideal run
      Pqxdh.serverRespond h.c h.server h.initMsg h.eSk h.coins (some h.app)
        = (Except.ok h.response, h.server') ∧
      Pqxdh.beaconFinish h.c h.beaconInitSent h.response
        = (Except.ok h.kid, h.beaconEstablished) := by
  -- the bundle
  obtain ⟨out, v, hout, hv, hvabs, -⟩ :=
    honest_bundle_validates h.c g.fresh g.startInputs g.startCoins h.ikSkB h.preSkB h.otSkB
      h.kemSkB g.beaconIk g.beaconPre g.beaconOt g.beaconKem
  have hvalid : absVerified v = h.valid := hvabs
  obtain ⟨out2, hout2, -, hkeeps, -, -, -, -, -⟩ :=
    beacon_start_refines h.c g.fresh g.startInputs g.startCoins h.ikSkB h.preSkB h.otSkB
      h.kemSkB g.beaconIk g.beaconPre g.beaconOt g.beaconKem
  have houteq : out = out2 := by
    rw [hout] at hout2
    simpa using hout2
  rw [← houteq] at hkeeps
  have hpin : absBinding out.state.expected_server_binding = h.binding := by
    rw [hkeeps]; exact g.pinned
  have hephem : h.response.ephemeralKey = h.c.xpub h.eSk := rfl
  -- the server
  have hconvB : h.c.xpkConv (absVerified v).ikB = some (h.c.xpub (h.c.xsk h.ikSkB)) := by
    rw [hvalid]; exact h.c.conv_agree h.ikSkB
  have hvalideal : Pqxdh.validateInit h.c h.initMsg = some (absVerified v) := by
    rw [hvalid]; exact h.validate
  have hfresh : (absVerified v).rid ∉ h.server.consumed := by
    rw [hvalid]; exact hok.freshRid
  have hdhs : Pqxdh.serverDHs h.c h.server.ikSk h.eSk (h.c.xpub (h.c.xsk h.ikSkB))
      (absVerified v).preKey (absVerified v).otKey = h.dhs := by
    rw [hvalid]; rfl
  have hfree : ¬ (h.server.peers.lookup (h.server.n + 1)).isSome := by
    have := hok.free
    simp only [Pqxdh.HonestRun.kid] at this
    simp [Pqxdh.HonestRun.server, this]
  obtain ⟨-, -, -, -, hsucc⟩ :=
    serverRegister_refines h.c h.server h.initMsg g.serverState v
      pqxdh.RegistrationStatus.Fresh g.serverBinding g.serverCoins g.serverSecrets
      pqxdh.KeyIdAvailability.Available h.eSk h.coins (h.c.xpub (h.c.xsk h.ikSkB))
      (some h.app) hvalideal hconvB (by simpa using hok.appNonempty) g.counter g.serverIk
      (by simp only [iff_false_intro (by simp : pqxdh.RegistrationStatus.Fresh ≠
            pqxdh.RegistrationStatus.Consumed)]
          simp [hfresh])
      (by rw [hdhs]; exact g.serverDh)
      (by rw [hvalid]; exact g.serverSs)
      (by simp only [iff_false_intro (by simp : pqxdh.KeyIdAvailability.Available ≠
            pqxdh.KeyIdAvailability.Occupied)]
          simp [hfree])
  obtain ⟨st, peer, resp, S', pr, hreg, -, hrespkid, hSn, hstn, hpeerkid, hpeerik, hpeerad,
      -, -, -, -⟩ :=
    hsucc hfresh (by rw [hdhs]; exact hok.nonzero) hok.notExhausted hfree
  -- the beacon
  have hbdhs : Pqxdh.beaconDHs h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      h.response.ephemeralKey = h.dhs := by
    rw [hephem, Pqxdh.beaconDHs_eq_serverDHs h.c h.ikSkS h.ikSkB h.preSkB h.otSkB h.eSk]
    rfl
  have hroot : Pqxdh.beaconRoot h.c h.ikSkB h.preSkB h.otSkB (h.c.xpub (h.c.xsk h.ikSkS))
      h.response.ephemeralKey h.kem.2 = h.ds := by
    rw [Pqxdh.beaconRoot, hbdhs]
    rfl
  have hwf : Ratchet.RecvWf
      (⟨h.chains.1, 0, []⟩ : Ratchet.RecvState Pqxdh.Bytes (Pqxdh.Bytes × Pqxdh.Bytes)) :=
    ⟨by simp [Ratchet.maxSkip], by simp, by simp⟩
  have hrecv : Ratchet.recvStep (Pqxdh.ratchetCrypto h.c)
      ⟨(Pqxdh.rootChains h.c (Pqxdh.beaconRoot h.c h.ikSkB h.preSkB h.otSkB
        (h.c.xpub (h.c.xsk h.ikSkS)) h.response.ephemeralKey h.kem.2)).1, 0, []⟩
      ⟨Pqxdh.assocData h.binding.ikPub (h.c.edPub h.ikSkB), h.response.appFrame.seq,
        h.response.appFrame.keyId⟩
      ⟨h.response.appFrame.seq - 1, h.response.appFrame.cipherText⟩
      = (Except.ok h.plaintext, h.beaconRecv) := by
    rw [hroot]
    exact Ratchet.recvStep_of_sendStep_inOrder (Pqxdh.ratchetCrypto h.c) h.chains.1 0 []
      hwf h.recordAD h.plaintext
  have hptlen : 8 < h.plaintext.length := by
    have hne : h.app ≠ [] := hok.appNonempty
    have : 0 < h.app.length := List.length_pos_iff.2 hne
    simp only [Pqxdh.HonestRun.plaintext, List.length_append, Pqxdh.LE64_length]
    omega
  have htake : h.plaintext.take 8 = Pqxdh.LE64 h.kid := by
    simp only [Pqxdh.HonestRun.plaintext]
    rw [← Pqxdh.LE64_length h.kid, List.take_left]
  have hbindpk : absBytes out.state.expected_server_binding.identity_public_key
      = h.binding.ikPub := congrArg Pqxdh.ServerBinding.ikPub hpin
  have hbindid : out.state.expected_server_binding.identity_key_id.val = h.binding.sid :=
    congrArg Pqxdh.ServerBinding.sid hpin
  obtain ⟨-, -, -, -, hbsucc⟩ :=
    beaconFinishDriver_refines h.c h.binding h.ikSkB h.preSkB h.otSkB h.kemSkB
      (h.c.xpub (h.c.xsk h.ikSkS)) h.kem.2 h.response h.plaintext h.beaconRecv out.state
      g.finishInputs g.authSenderId g.authBinding
      (h.c.decap_encap h.kemSkB h.coins) (h.c.conv_agree h.ikSkS) hbindpk hbindid g.respIk
      (by rw [hbdhs]; exact g.beaconDh)
      g.respKid g.authSender (by simp [Pqxdh.HonestRun.response, Pqxdh.HonestRun.frame])
      hrecv hptlen (by rw [g.authBound, htake])
  obtain ⟨est, hest, hestkid, hestbind, -⟩ :=
    hbsucc rfl (by rw [hbdhs]; exact hok.nonzero) rfl htake
  refine ⟨out, v, st, peer, est, hout, hv, hvalid, hreg, ?_, ?_, ?_, ?_, hest, ?_, hestbind,
    h.serverStep hok, h.beaconStep hok⟩
  · rw [hstn, hSn]; rfl
  · rw [hpeerkid, hrespkid]; rfl
  · rw [hpeerik, hvalid]; rfl
  · rw [hpeerad, hvalid]; rfl
  · exact hestkid

end PqxdhRefinement
