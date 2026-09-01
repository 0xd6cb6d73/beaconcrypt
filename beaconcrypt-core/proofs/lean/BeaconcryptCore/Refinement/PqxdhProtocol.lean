import BeaconcryptCore.Refinement.PqxdhCore

/-!
# The generated PQXDH state machines refine the handwritten ideal model

`BeaconcryptCore/Model/Pqxdh/Protocol.lean` contains the handwritten ideal model of
the BeaconCrypt modified PQXDH registration: the two state machines
`Pqxdh.beaconInit`, `Pqxdh.validateInit`, `Pqxdh.serverRespond` and
`Pqxdh.beaconFinish`, with all cryptography given by the abstract interface
`Pqxdh.Crypto`.

`BeaconcryptCore/Extraction/Funs.lean` contains the corresponding registration logic
extracted from the Rust source.  That logic is *cryptography free*: the primitives
live outside the extracted core, so the generated transitions are driven by the
caller with the values the primitives produced —
the four X25519 contributions and the ML-KEM shared secret
(`pqxdh.PqxdhSharedSecrets`), the replay verdict (`pqxdh.RegistrationStatus`), the
key-identifier availability verdict (`pqxdh.KeyIdAvailability`), the authenticated
sender identifier and the authenticated key-identifier binding recovered from the
first record.

This file connects the two.  It

* abstracts the generated protocol data to the ideal model (`absBinding`,
  `absVerified`, `absDHs`);
* proves that the generated registration bundle builder `pqxdh.beacon_start`
  emits exactly the payloads the ideal `Pqxdh.beaconInit` signs
  (`beacon_start_refines`), and that the generated parser
  `pqxdh.validate_init_kex` agrees with the ideal `Pqxdh.validateInit`
  (`validate_init_kex_refines`, `honest_bundle_validates`);
* packages the generated server steps into the driver `serverRegister` and proves
  `serverRegister_refines`: on the inputs the ideal model computes, the generated
  server pipeline returns the outcome of `Pqxdh.serverRespond`, with the same
  allocated identifier, the same published peer and the same rejection;
* packages the generated beacon steps into the driver `beaconFinishDriver` and
  proves `beaconFinishDriver_refines` against `Pqxdh.beaconFinish`;
* proves the transactional rollback of both principals
  (`server_abort_candidate_refines`, `beacon_abort_init_refines`).

The record layer itself (the sealing of the first server record and its admission by
the beacon) is not part of the extracted PQXDH module: it is the symmetric ratchet,
whose refinement is `BeaconcryptCore/Refinement/RatchetRefinement.lean`.  Here it
appears through the values the caller feeds back into the beacon transition.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open beaconcrypt_core

namespace PqxdhRefinement

/-! ## Abstraction of the generated protocol data -/

/-- Abstraction of a generated pinned server binding. -/
def absBinding (b : pqxdh.ServerBinding) : Pqxdh.ServerBinding :=
  ⟨absBytes b.identity_public_key, b.identity_key_id.val⟩

/-- Abstraction of a generated validated registration bundle. -/
def absVerified (v : pqxdh.VerifiedInitKex) : Pqxdh.ValidInit :=
  ⟨absBytes v.beacon_identity_public_key, absBytes v.beacon_prekey_public_key,
    absBytes v.beacon_one_time_public_key, absBytes v.beacon_pq_public_key⟩

/-- The four X25519 contributions carried by the generated shared-secret record. -/
def absDHs (s : pqxdh.PqxdhSharedSecrets) :
    Pqxdh.Bytes × Pqxdh.Bytes × Pqxdh.Bytes × Pqxdh.Bytes :=
  (absBytes s.dh1, absBytes s.dh2, absBytes s.dh3, absBytes s.dh4)

@[simp] theorem absByte_role_pre : absByte pqxdh.KEY_ROLE_PREKEY = Pqxdh.rolePre := by
  simp [absByte, pqxdh.KEY_ROLE_PREKEY, Pqxdh.rolePre]

@[simp] theorem absByte_role_otk : absByte pqxdh.KEY_ROLE_ONE_TIME = Pqxdh.roleOtk := by
  simp [absByte, pqxdh.KEY_ROLE_ONE_TIME, Pqxdh.roleOtk]

/-! ## Registration initiation (spec §5) -/

/-- **The generated bundle builder refines `Pqxdh.beaconInit`.**  Given the public
keys of a provisioned beacon, `pqxdh.beacon_start` succeeds, moves the beacon from
`Fresh` to `InitSent` keeping the pinned binding, and emits exactly the four byte
strings the ideal beacon puts on the wire: the tagged identity key, and the three
payloads carried by the ideal attached signatures. -/
theorem beacon_start_refines (c : Pqxdh.Crypto) (st : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (ikSk preSk otSk kemSk : Pqxdh.Bytes)
    (hik : absBytes inputs.identity_public_key = c.edPub ikSk)
    (hpre : absBytes inputs.prekey_public_key = c.xpub preSk)
    (hot : absBytes coins.one_time_public_key = c.xpub otSk)
    (hkem : absBytes inputs.pq_public_key = c.kemPub kemSk) :
    ∃ out : pqxdh.BeaconStart,
      pqxdh.beacon_start st inputs coins = ok out ∧
      -- the ideal transition, from either provisioned state
      Pqxdh.beaconInit c (.fresh (absBinding st.expected_server_binding) ikSk preSk kemSk)
          otSk
        = some (Pqxdh.initKexOf c ikSk preSk otSk kemSk,
            .initSent (absBinding st.expected_server_binding) ikSk preSk otSk kemSk) ∧
      -- the generated state keeps the pinned binding and records the identity key
      absBinding out.state.expected_server_binding = absBinding st.expected_server_binding ∧
      absBytes out.state.beacon_identity_public_key = c.edPub ikSk ∧
      -- the emitted bundle is the ideal one, field by field
      absBytes out.message.identity_key = (Pqxdh.initKexOf c ikSk preSk otSk kemSk).identityKey ∧
      c.verify (c.edPub ikSk) (Pqxdh.initKexOf c ikSk preSk otSk kemSk).preKey
        = some (absBytes out.message.prekey) ∧
      c.verify (c.edPub ikSk) (Pqxdh.initKexOf c ikSk preSk otSk kemSk).oneTimeKey
        = some (absBytes out.message.one_time_key) ∧
      c.verify (c.edPub ikSk) (Pqxdh.initKexOf c ikSk preSk otSk kemSk).pqKey
        = some (absBytes out.message.pq_key) := by
  obtain ⟨a, ha, haabs⟩ := tag_sign_key_abs inputs.identity_public_key
  obtain ⟨a1, ha1, ha1abs⟩ := tag_x25519_key_abs pqxdh.KEY_ROLE_PREKEY inputs.prekey_public_key
  obtain ⟨a2, ha2, ha2abs⟩ :=
    tag_x25519_key_abs pqxdh.KEY_ROLE_ONE_TIME coins.one_time_public_key
  obtain ⟨a3, ha3, ha3abs⟩ := tag_mlkem768_key_abs inputs.pq_public_key
  refine ⟨_, by rw [pqxdh.beacon_start, ha, ha1, ha2, ha3]; rfl, rfl, rfl, hik, ?_, ?_, ?_, ?_⟩
  · rw [Pqxdh.initKexOf, haabs, hik]
  · rw [Pqxdh.initKexOf, c.verify_sign, ha1abs, hpre, absByte_role_pre]
  · rw [Pqxdh.initKexOf, c.verify_sign, ha2abs, hot, absByte_role_otk]
  · rw [Pqxdh.initKexOf, c.verify_sign, ha3abs, hkem]

/-! ## Server validation of the bundle (spec §6) -/

/-- **The generated bundle parser refines `Pqxdh.validateInit`.**  The extracted core
is handed the payloads that signature verification recovered, so the hypothesis
`hver` says exactly that: under the identity key parsed from the bundle, the ideal
attached signatures verify to the byte strings the generated code is given.  Then
the generated parser accepts exactly when the ideal server does, and on acceptance
the validated bundles agree. -/
theorem validate_init_kex_refines (c : Pqxdh.Crypto) (g : pqxdh.InitKex)
    (im : Pqxdh.InitKex) (hid : im.identityKey = absBytes g.identity_key)
    (hver : ∀ ikB, Pqxdh.parseSigTag im.identityKey = some ikB →
      c.verify ikB im.preKey = some (absBytes g.prekey) ∧
      c.verify ikB im.oneTimeKey = some (absBytes g.one_time_key) ∧
      c.verify ikB im.pqKey = some (absBytes g.pq_key)) :
    (∃ v : pqxdh.VerifiedInitKex,
        pqxdh.validate_init_kex g = ok (core.result.Result.Ok v) ∧
        Pqxdh.validateInit c im = some (absVerified v)) ∨
      (pqxdh.validate_init_kex g
          = ok (core.result.Result.Err pqxdh.RegistrationError.InvalidKeyEncoding) ∧
        Pqxdh.validateInit c im = none) := by
  unfold pqxdh.validate_init_kex
  rcases untag_sign_key_abs g.identity_key with ⟨k, hk, hkabs⟩ | ⟨hk, hkabs⟩
  · obtain ⟨hp, ho, hq⟩ := hver (absBytes k) (by rw [hid]; exact hkabs)
    have hpre := untag_x25519_key_abs g.prekey pqxdh.KEY_ROLE_PREKEY
    have hotk := untag_x25519_key_abs g.one_time_key pqxdh.KEY_ROLE_ONE_TIME
    have hpq := untag_mlkem768_key_abs g.pq_key
    rw [absByte_role_pre] at hpre
    rw [absByte_role_otk] at hotk
    have hstart : Pqxdh.validateInit c im =
        (Pqxdh.parseXTag Pqxdh.rolePre (absBytes g.prekey)).bind fun pk =>
          (Pqxdh.parseXTag Pqxdh.roleOtk (absBytes g.one_time_key)).bind fun ot =>
            (Pqxdh.parsePQTag (absBytes g.pq_key)).bind fun kem =>
              some (⟨absBytes k, pk, ot, kem⟩ : Pqxdh.ValidInit) := by
      have hkabs' : Pqxdh.parseSigTag im.identityKey = some (absBytes k) := by
        rw [hid]; exact hkabs
      simp [Pqxdh.validateInit, hkabs', hp, ho, hq]
    rcases hpre with ⟨pk, hpk, hpkabs⟩ | ⟨hpk, hpkabs⟩
    · rcases hotk with ⟨otk, hotk1, hotkabs⟩ | ⟨hotk1, hotkabs⟩
      · rcases hpq with ⟨q, hq1, hqabs⟩ | ⟨hq1, hqabs⟩
        · exact Or.inl ⟨⟨k, pk, otk, q⟩, by simp [hk, hpk, hotk1, hq1],
            by rw [hstart, hpkabs, hotkabs, hqabs]; rfl⟩
        · exact Or.inr ⟨by simp [hk, hpk, hotk1, hq1],
            by rw [hstart, hpkabs, hotkabs, hqabs]; rfl⟩
      · exact Or.inr ⟨by simp [hk, hpk, hotk1], by rw [hstart, hpkabs, hotkabs]; rfl⟩
    · exact Or.inr ⟨by simp [hk, hpk], by rw [hstart, hpkabs]; rfl⟩
  · exact Or.inr ⟨by simp [hk], by simp [Pqxdh.validateInit, hid, hkabs]⟩

/-- **An honest registration bundle is validated identically on both sides.**  The
bundle the generated beacon emits is accepted by the generated server parser, the
ideal bundle is accepted by the ideal server, and the validated content is the
beacon's four public keys. -/
theorem honest_bundle_validates (c : Pqxdh.Crypto) (st : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (ikSk preSk otSk kemSk : Pqxdh.Bytes)
    (hik : absBytes inputs.identity_public_key = c.edPub ikSk)
    (hpre : absBytes inputs.prekey_public_key = c.xpub preSk)
    (hot : absBytes coins.one_time_public_key = c.xpub otSk)
    (hkem : absBytes inputs.pq_public_key = c.kemPub kemSk) :
    ∃ (out : pqxdh.BeaconStart) (v : pqxdh.VerifiedInitKex),
      pqxdh.beacon_start st inputs coins = ok out ∧
      pqxdh.validate_init_kex out.message = ok (core.result.Result.Ok v) ∧
      absVerified v = ⟨c.edPub ikSk, c.xpub preSk, c.xpub otSk, c.kemPub kemSk⟩ ∧
      Pqxdh.validateInit c (Pqxdh.initKexOf c ikSk preSk otSk kemSk)
        = some ⟨c.edPub ikSk, c.xpub preSk, c.xpub otSk, c.kemPub kemSk⟩ := by
  obtain ⟨out, hout, -, -, -, hmid, hmpre, hmot, hmpq⟩ :=
    beacon_start_refines c st inputs coins ikSk preSk otSk kemSk hik hpre hot hkem
  have hideal : Pqxdh.validateInit c (Pqxdh.initKexOf c ikSk preSk otSk kemSk)
      = some ⟨c.edPub ikSk, c.xpub preSk, c.xpub otSk, c.kemPub kemSk⟩ := by
    simp [Pqxdh.validateInit, Pqxdh.initKexOf, c.verify_sign, c.edPub_length, c.xpub_length,
      c.kemPub_length]
  rcases validate_init_kex_refines c out.message (Pqxdh.initKexOf c ikSk preSk otSk kemSk)
      hmid.symm (by
        intro ikB hikB
        rw [Pqxdh.initKexOf] at hikB
        rw [Pqxdh.parseSigTag_tagSig (c.edPub_length ikSk)] at hikB
        have hikB' : ikB = c.edPub ikSk := (Option.some_inj.mp hikB).symm
        subst hikB'
        exact ⟨hmpre, hmot, hmpq⟩) with
    ⟨v, hv, hvabs⟩ | ⟨-, hnone⟩
  · refine ⟨out, v, hout, hv, ?_, hideal⟩
    rw [hideal] at hvabs
    exact (Option.some_inj.mp hvabs).symm
  · rw [hideal] at hnone
    exact absurd hnone (by simp)

/-! ## The server (spec §6–§14) -/

/-- The rejection of the extracted core that corresponds to an ideal rejection.  The
two rejections the extracted core cannot express are the ones its callers handle:
a failed signature verification and an empty application message. -/
def genServerError : Pqxdh.ServerError → Option pqxdh.RegistrationError
  | .badEncoding => some pqxdh.RegistrationError.InvalidKeyEncoding
  | .badSignature => none
  | .registrationReplay => some pqxdh.RegistrationError.RegistrationReplay
  | .zeroDH => some pqxdh.RegistrationError.InvalidDhOutput
  | .emptyAppMessage => none
  | .keyIdExhausted => some pqxdh.RegistrationError.KeyIdExhausted
  | .keyIdCollision => some pqxdh.RegistrationError.KeyIdCollision

/-- An addition of one that does not overflow a `u64`. -/
theorem u64_add_one (x : Std.U64) (h : x.val + 1 < 2 ^ 64) :
    ∃ z : Std.U64, x + 1#u64 = ok z ∧ z.val = x.val + 1 := by
  have h' := Std.UScalar.add_equiv x 1#u64
  cases hxy : x + 1#u64 with
  | ok z => rw [hxy] at h'; exact ⟨z, rfl, by simpa using h'.2.1⟩
  | fail e =>
    rw [hxy] at h'
    simp [Std.UScalar.inBounds] at h'
    omega
  | div => rw [hxy] at h'; exact h'.elim

theorem u64_max_val : (core.num.U64.MAX).val = 2 ^ 64 - 1 := by
  simp [core.num.U64.MAX, Std.U64.rMax]

/-- **The generated acceptance step refines the first half of `Pqxdh.serverRespond`.**
The replay verdict is honoured before anything else, an all-zero contribution is
rejected exactly as in the ideal model, and otherwise the pending registration
carries the ideal registration identifier `RID = IK_B ‖ OT_B` and the ideal PQXDH
transcript `IKM_PQ`. -/
theorem server_accept_refines (c : Pqxdh.Crypto) (S : Pqxdh.ServerState)
    (state : pqxdh.ServerState) (reg : pqxdh.VerifiedInitKex)
    (status : pqxdh.RegistrationStatus) (binding : pqxdh.ServerBinding)
    (gcoins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (eSk coins ikBX : Pqxdh.Bytes)
    (hstatus : status = pqxdh.RegistrationStatus.Consumed ↔
      (absVerified reg).rid ∈ S.consumed)
    (hdh : absDHs secrets = Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
      (absVerified reg).otKey)
    (hss : absBytes secrets.kem_shared_secret
      = (c.encap (absVerified reg).kemPub coins).2) :
    ((absVerified reg).rid ∈ S.consumed →
        pqxdh.server_accept state reg status binding gcoins secrets
          = ok (core.result.Result.Err pqxdh.RegistrationError.RegistrationReplay)) ∧
    ((absVerified reg).rid ∉ S.consumed →
      ¬ Pqxdh.dhNonZero (Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
          (absVerified reg).otKey) →
        pqxdh.server_accept state reg status binding gcoins secrets
          = ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput)) ∧
    ((absVerified reg).rid ∉ S.consumed →
      Pqxdh.dhNonZero (Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
          (absVerified reg).otKey) →
        ∃ pending : pqxdh.PendingServerRegistration,
          pqxdh.server_accept state reg status binding gcoins secrets
            = ok (core.result.Result.Ok (state, pending)) ∧
          pending.server_binding = binding ∧
          absBytes pending.registration_id.bytes = (absVerified reg).rid ∧
          absBytes pending.beacon_identity_public_key = (absVerified reg).ikB ∧
          pending.ephemeral_public_key = gcoins.ephemeral_public_key ∧
          pending.kem_ciphertext = gcoins.kem_ciphertext ∧
          absBytes pending.root_key_input.bytes =
            Pqxdh.ikmOf (Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
              (absVerified reg).otKey) (c.encap (absVerified reg).kemPub coins).2) := by
  have hzero := (build_root_key_input_abs secrets).2
  have hok := (build_root_key_input_abs secrets).1
  have habs : (absBytes secrets.dh1, absBytes secrets.dh2, absBytes secrets.dh3,
      absBytes secrets.dh4) = Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
        (absVerified reg).otKey := hdh
  rw [habs] at hzero hok
  refine ⟨?_, ?_, ?_⟩
  · intro hrid
    have : status = pqxdh.RegistrationStatus.Consumed := hstatus.mpr hrid
    subst this
    simp [pqxdh.server_accept, pqxdh.validate_registration_status]
  · intro hrid hz
    have hfresh : status = pqxdh.RegistrationStatus.Fresh := by
      cases status with
      | Fresh => rfl
      | Consumed => exact absurd (hstatus.mp rfl) hrid
    subst hfresh
    simp [pqxdh.server_accept, pqxdh.validate_registration_status, hzero hz]
  · intro hrid hnz
    have hfresh : status = pqxdh.RegistrationStatus.Fresh := by
      cases status with
      | Fresh => rfl
      | Consumed => exact absurd (hstatus.mp rfl) hrid
    subst hfresh
    obtain ⟨v, hv, hvabs⟩ := hok hnz
    obtain ⟨ri, hri, hriabs⟩ := registration_id_abs reg
    have heq : pqxdh.server_accept state reg pqxdh.RegistrationStatus.Fresh binding gcoins
          secrets
        = ok (core.result.Result.Ok (state,
            ({ server_binding := binding, registration_id := ri,
               beacon_identity_public_key := reg.beacon_identity_public_key,
               ephemeral_public_key := gcoins.ephemeral_public_key,
               kem_ciphertext := gcoins.kem_ciphertext,
               root_key_input := v } : pqxdh.PendingServerRegistration))) := by
      simp [pqxdh.server_accept, pqxdh.validate_registration_status, hv, hri]
    refine ⟨_, heq, rfl, hriabs, rfl, rfl, rfl, ?_⟩
    rw [hvabs, hss, ← hdh]
    rfl

/-- **The generated allocation step refines the ideal counter.**  The generated
server refuses to allocate exactly when the ideal counter is exhausted, and
otherwise hands out the ideal successor. -/
theorem server_next_key_id_refines (S : Pqxdh.ServerState) (state : pqxdh.ServerState)
    (hn : state.last_key_id.val = S.n) :
    (S.n = Pqxdh.maxKeyId →
      pqxdh.server_next_key_id state
        = ok (core.result.Result.Err pqxdh.RegistrationError.KeyIdExhausted)) ∧
    (S.n ≠ Pqxdh.maxKeyId →
      ∃ kid : Std.U64,
        pqxdh.server_next_key_id state = ok (core.result.Result.Ok kid) ∧
        kid.val = S.n + 1) := by
  have hlt : state.last_key_id.val < 2 ^ 64 := state.last_key_id.bv.isLt
  constructor
  · intro hmax
    have : state.last_key_id = core.num.U64.MAX := by
      apply Std.UScalar.eq_of_val_eq
      rw [hn, u64_max_val, hmax, Pqxdh.maxKeyId]
    simp [pqxdh.server_next_key_id, this]
  · intro hmax
    have hne : state.last_key_id ≠ core.num.U64.MAX := by
      intro hc
      apply hmax
      rw [← hn, hc, u64_max_val, Pqxdh.maxKeyId]
    obtain ⟨z, hz, hzval⟩ := u64_add_one state.last_key_id (by
      rcases Nat.lt_or_ge (state.last_key_id.val + 1) (2 ^ 64) with h | h
      · exact h
      · exact absurd (Std.UScalar.eq_of_val_eq (by rw [u64_max_val]; omega)) hne)
    exact ⟨z, by simp [pqxdh.server_next_key_id, hne, hz], by rw [hzval, hn]⟩

/-- **The generated commit preparation refines `Pqxdh.serverEmit`.**  It allocates the
ideal identifier, refuses the ideal collision, and computes the ideal associated
data of spec §9. -/
theorem server_prepare_commit_refines (c : Pqxdh.Crypto) (S : Pqxdh.ServerState)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (hn : state.last_key_id.val = S.n) (hbind : pending.server_binding = binding)
    (hikS : absBytes binding.identity_public_key = c.edPub S.ikSk)
    (havail : availability = pqxdh.KeyIdAvailability.Occupied ↔
      (S.peers.lookup (S.n + 1)).isSome) :
    (S.n = Pqxdh.maxKeyId →
      pqxdh.server_prepare_commit state pending binding availability
        = ok (core.result.Result.Err pqxdh.RegistrationError.KeyIdExhausted)) ∧
    (S.n ≠ Pqxdh.maxKeyId → (S.peers.lookup (S.n + 1)).isSome →
      pqxdh.server_prepare_commit state pending binding availability
        = ok (core.result.Result.Err pqxdh.RegistrationError.KeyIdCollision)) ∧
    (S.n ≠ Pqxdh.maxKeyId → ¬ (S.peers.lookup (S.n + 1)).isSome →
      ∃ cand : pqxdh.ServerRegistrationCandidate,
        pqxdh.server_prepare_commit state pending binding availability
          = ok (core.result.Result.Ok cand) ∧
        cand.previous_state = state ∧
        cand.next_state.last_key_id.val = S.n + 1 ∧
        cand.key_id.val = S.n + 1 ∧
        cand.beacon_identity_public_key = pending.beacon_identity_public_key ∧
        cand.ephemeral_public_key = pending.ephemeral_public_key ∧
        cand.kem_ciphertext = pending.kem_ciphertext ∧
        absBytes cand.associated_data =
          Pqxdh.assocData (c.edPub S.ikSk) (absBytes pending.beacon_identity_public_key)) := by
  subst hbind
  have hself : core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8
      pending.server_binding.identity_public_key pending.server_binding.identity_public_key
      = ok true := by
    rw [array_eq_abs]; simp
  obtain ⟨hmax, hnext⟩ := server_next_key_id_refines S state hn
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [pqxdh.server_prepare_commit, hself, hmax h]
  · intro h hocc
    obtain ⟨kid, hkid, -⟩ := hnext h
    have : availability = pqxdh.KeyIdAvailability.Occupied := havail.mpr hocc
    subst this
    simp [pqxdh.server_prepare_commit, hself, hkid]
  · intro h hocc
    obtain ⟨kid, hkid, hkidval⟩ := hnext h
    have hfree : availability = pqxdh.KeyIdAvailability.Available := by
      cases availability with
      | Available => rfl
      | Occupied => exact absurd (havail.mp rfl) hocc
    subst hfree
    obtain ⟨a, ha, haabs⟩ :=
      build_associated_data_abs pending.server_binding.identity_public_key
        pending.beacon_identity_public_key
    have heq : pqxdh.server_prepare_commit state pending pending.server_binding
          pqxdh.KeyIdAvailability.Available
        = ok (core.result.Result.Ok
            ({ previous_state := state, next_state := { last_key_id := kid },
               key_id := kid,
               beacon_identity_public_key := pending.beacon_identity_public_key,
               server_identity_public_key := pending.server_binding.identity_public_key,
               server_identity_key_id := pending.server_binding.identity_key_id,
               ephemeral_public_key := pending.ephemeral_public_key,
               kem_ciphertext := pending.kem_ciphertext,
               associated_data := a } : pqxdh.ServerRegistrationCandidate)) := by
      simp [pqxdh.server_prepare_commit, hself, hkid, ha]
    refine ⟨_, heq, rfl, hkidval, hkidval, rfl, rfl, rfl, ?_⟩
    rw [haabs, hikS]

/-- The generated publication step publishes the ideal peer entry. -/
theorem server_commit_refines (cand : pqxdh.ServerRegistrationCandidate) :
    pqxdh.server_commit cand = ok (cand.next_state,
      { key_id := cand.key_id, identity_public_key := cand.beacon_identity_public_key,
        associated_data := cand.associated_data }) := rfl

/-! ### Ideal-side facts about response construction -/

theorem serverEmit_exhausted (c : Pqxdh.Crypto) (S1 : Pqxdh.ServerState)
    (ikB ds kemCt ePub app : Pqxdh.Bytes) (hmax : S1.n = Pqxdh.maxKeyId) :
    Pqxdh.serverEmit c S1 ikB ds kemCt ePub app =
      (Except.error Pqxdh.ServerError.keyIdExhausted, S1) := by
  rw [Pqxdh.serverEmit, if_pos hmax]

theorem serverEmit_collision (c : Pqxdh.Crypto) (S1 : Pqxdh.ServerState)
    (ikB ds kemCt ePub app : Pqxdh.Bytes) (hmax : S1.n ≠ Pqxdh.maxKeyId)
    (hocc : (S1.peers.lookup (S1.n + 1)).isSome) :
    Pqxdh.serverEmit c S1 ikB ds kemCt ePub app =
      (Except.error Pqxdh.ServerError.keyIdCollision, S1) := by
  rw [Pqxdh.serverEmit, if_neg hmax, if_pos hocc]

theorem serverEmit_ok (c : Pqxdh.Crypto) (S1 : Pqxdh.ServerState)
    (ikB ds kemCt ePub app : Pqxdh.Bytes) (hmax : S1.n ≠ Pqxdh.maxKeyId)
    (hfree : ¬ (S1.peers.lookup (S1.n + 1)).isSome) :
    ∃ (resp : Pqxdh.KexResponse) (S' : Pqxdh.ServerState) (pr : Pqxdh.Peer),
      Pqxdh.serverEmit c S1 ikB ds kemCt ePub app = (Except.ok resp, S') ∧
      resp.keyId = S1.n + 1 ∧ S'.n = S1.n + 1 ∧ S'.consumed = S1.consumed ∧
      S'.peers = (S1.n + 1, pr) :: S1.peers ∧ pr.ikPub = ikB ∧
      pr.ad = Pqxdh.assocData (c.edPub S1.ikSk) ikB := by
  rw [Pqxdh.serverEmit, if_neg hmax, if_neg hfree]
  exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The ideal server reaches response construction exactly when the bundle is valid,
the registration identifier is fresh, the identity conversion succeeds, no
contribution is zero and the application message is not explicitly empty — and it
does so with `RID` already consumed. -/
theorem serverRespond_eq_emit (c : Pqxdh.Crypto) (S : Pqxdh.ServerState)
    (m : Pqxdh.InitKex) (eSk coins ikBX : Pqxdh.Bytes) (app : Option Pqxdh.Bytes)
    (v : Pqxdh.ValidInit) (hval : Pqxdh.validateInit c m = some v)
    (hrid : v.rid ∉ S.consumed) (hconv : c.xpkConv v.ikB = some ikBX)
    (hnz : Pqxdh.dhNonZero (Pqxdh.serverDHs c S.ikSk eSk ikBX v.preKey v.otKey))
    (happ : app ≠ some []) :
    Pqxdh.serverRespond c S m eSk coins app = Pqxdh.serverEmit c
      { S with consumed := v.rid :: S.consumed } v.ikB
      (Pqxdh.rootSecret c (Pqxdh.ikmOf (Pqxdh.serverDHs c S.ikSk eSk ikBX v.preKey v.otKey)
        (c.encap v.kemPub coins).2))
      (c.encap v.kemPub coins).1 (c.xpub eSk) (app.getD [0xFF]) := by
  simp [Pqxdh.serverRespond, hval, hrid, hconv, hnz, happ]

/-! ### The whole generated server transition -/

/-- The generated server registration, assembled from the extracted steps: accept the
bundle (replay verdict, PQXDH transcript, registration identifier), prepare the
commit (pinned binding, identifier allocation, collision verdict, associated data)
and publish the peer. -/
def serverRegister (state : pqxdh.ServerState) (reg : pqxdh.VerifiedInitKex)
    (status : pqxdh.RegistrationStatus) (binding : pqxdh.ServerBinding)
    (gcoins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (availability : pqxdh.KeyIdAvailability) :
    Result (core.result.Result (pqxdh.ServerState × pqxdh.EstablishedPeer)
      pqxdh.RegistrationError) := do
  let r ← pqxdh.server_accept state reg status binding gcoins secrets
  match r with
  | core.result.Result.Err e => ok (core.result.Result.Err e)
  | core.result.Result.Ok (state1, pending) =>
    let r1 ← pqxdh.server_prepare_commit state1 pending binding availability
    match r1 with
    | core.result.Result.Err e => ok (core.result.Result.Err e)
    | core.result.Result.Ok cand =>
      let p ← pqxdh.server_commit cand
      ok (core.result.Result.Ok p)

/-- **Main server refinement.**  On the inputs the ideal model computes — the four
X25519 contributions, the ML-KEM shared secret, the replay verdict and the
key-identifier availability verdict — the generated server pipeline returns exactly
the outcome of the handwritten `Pqxdh.serverRespond`: the same rejection in each of
the four rejection cases the extracted core can express, and on success the ideal
assigned identifier, the ideal published peer and the ideal associated data, with
`RID` consumed. -/
theorem serverRegister_refines (c : Pqxdh.Crypto) (S : Pqxdh.ServerState)
    (m : Pqxdh.InitKex) (state : pqxdh.ServerState) (reg : pqxdh.VerifiedInitKex)
    (status : pqxdh.RegistrationStatus) (binding : pqxdh.ServerBinding)
    (gcoins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (availability : pqxdh.KeyIdAvailability) (eSk coins ikBX : Pqxdh.Bytes)
    (app : Option Pqxdh.Bytes)
    (hval : Pqxdh.validateInit c m = some (absVerified reg))
    (hconv : c.xpkConv (absVerified reg).ikB = some ikBX)
    (happ : app ≠ some [])
    (hn : state.last_key_id.val = S.n)
    (hikS : absBytes binding.identity_public_key = c.edPub S.ikSk)
    (hstatus : status = pqxdh.RegistrationStatus.Consumed ↔
      (absVerified reg).rid ∈ S.consumed)
    (hdh : absDHs secrets = Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
      (absVerified reg).otKey)
    (hss : absBytes secrets.kem_shared_secret
      = (c.encap (absVerified reg).kemPub coins).2)
    (havail : availability = pqxdh.KeyIdAvailability.Occupied ↔
      (S.peers.lookup (S.n + 1)).isSome) :
    -- replayed registration
    ((absVerified reg).rid ∈ S.consumed →
      serverRegister state reg status binding gcoins secrets availability
          = ok (core.result.Result.Err pqxdh.RegistrationError.RegistrationReplay) ∧
      Pqxdh.serverRespond c S m eSk coins app =
        (Except.error Pqxdh.ServerError.registrationReplay, S)) ∧
    -- an all-zero X25519 contribution
    ((absVerified reg).rid ∉ S.consumed →
      ¬ Pqxdh.dhNonZero (Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
          (absVerified reg).otKey) →
      serverRegister state reg status binding gcoins secrets availability
          = ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput) ∧
      Pqxdh.serverRespond c S m eSk coins app =
        (Except.error Pqxdh.ServerError.zeroDH, S)) ∧
    -- the allocation counter is exhausted
    ((absVerified reg).rid ∉ S.consumed →
      Pqxdh.dhNonZero (Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
          (absVerified reg).otKey) →
      S.n = Pqxdh.maxKeyId →
      serverRegister state reg status binding gcoins secrets availability
          = ok (core.result.Result.Err pqxdh.RegistrationError.KeyIdExhausted) ∧
      Pqxdh.serverRespond c S m eSk coins app =
        (Except.error Pqxdh.ServerError.keyIdExhausted,
          { S with consumed := (absVerified reg).rid :: S.consumed })) ∧
    -- the proposed identifier is already in use
    ((absVerified reg).rid ∉ S.consumed →
      Pqxdh.dhNonZero (Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
          (absVerified reg).otKey) →
      S.n ≠ Pqxdh.maxKeyId → (S.peers.lookup (S.n + 1)).isSome →
      serverRegister state reg status binding gcoins secrets availability
          = ok (core.result.Result.Err pqxdh.RegistrationError.KeyIdCollision) ∧
      Pqxdh.serverRespond c S m eSk coins app =
        (Except.error Pqxdh.ServerError.keyIdCollision,
          { S with consumed := (absVerified reg).rid :: S.consumed })) ∧
    -- the registration succeeds
    ((absVerified reg).rid ∉ S.consumed →
      Pqxdh.dhNonZero (Pqxdh.serverDHs c S.ikSk eSk ikBX (absVerified reg).preKey
          (absVerified reg).otKey) →
      S.n ≠ Pqxdh.maxKeyId → ¬ (S.peers.lookup (S.n + 1)).isSome →
      ∃ (st : pqxdh.ServerState) (peer : pqxdh.EstablishedPeer)
        (resp : Pqxdh.KexResponse) (S' : Pqxdh.ServerState) (pr : Pqxdh.Peer),
        serverRegister state reg status binding gcoins secrets availability
            = ok (core.result.Result.Ok (st, peer)) ∧
        Pqxdh.serverRespond c S m eSk coins app = (Except.ok resp, S') ∧
        resp.keyId = S.n + 1 ∧ S'.n = S.n + 1 ∧ st.last_key_id.val = S'.n ∧
        peer.key_id.val = resp.keyId ∧
        absBytes peer.identity_public_key = (absVerified reg).ikB ∧
        absBytes peer.associated_data =
          Pqxdh.assocData (c.edPub S.ikSk) (absVerified reg).ikB ∧
        S'.consumed = (absVerified reg).rid :: S.consumed ∧
        S'.peers = (S.n + 1, pr) :: S.peers ∧
        pr.ikPub = (absVerified reg).ikB ∧
        pr.ad = Pqxdh.assocData (c.edPub S.ikSk) (absVerified reg).ikB) := by
  obtain ⟨hreplay, hzero, haccept⟩ :=
    server_accept_refines c S state reg status binding gcoins secrets eSk coins ikBX
      hstatus hdh hss
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hrid
    exact ⟨by simp [serverRegister, hreplay hrid],
      by simp [Pqxdh.serverRespond, hval, hrid]⟩
  · intro hrid hz
    exact ⟨by simp [serverRegister, hzero hrid hz],
      by simp [Pqxdh.serverRespond, hval, hrid, hconv, hz]⟩
  · intro hrid hnz hmax
    obtain ⟨pending, hacc, hbind, -, -, -, -, -⟩ := haccept hrid hnz
    obtain ⟨hpmax, -, -⟩ :=
      server_prepare_commit_refines c S state pending binding availability hn hbind hikS havail
    refine ⟨by simp [serverRegister, hacc, hpmax hmax], ?_⟩
    rw [serverRespond_eq_emit c S m eSk coins ikBX app _ hval hrid hconv hnz happ]
    exact serverEmit_exhausted _ _ _ _ _ _ _ hmax
  · intro hrid hnz hmax hocc
    obtain ⟨pending, hacc, hbind, -, -, -, -, -⟩ := haccept hrid hnz
    obtain ⟨-, hpocc, -⟩ :=
      server_prepare_commit_refines c S state pending binding availability hn hbind hikS havail
    refine ⟨by simp [serverRegister, hacc, hpocc hmax hocc], ?_⟩
    rw [serverRespond_eq_emit c S m eSk coins ikBX app _ hval hrid hconv hnz happ]
    exact serverEmit_collision _ _ _ _ _ _ _ hmax hocc
  · intro hrid hnz hmax hfree
    obtain ⟨pending, hacc, hbind, -, hpik, -, -, -⟩ := haccept hrid hnz
    obtain ⟨-, -, hpok⟩ :=
      server_prepare_commit_refines c S state pending binding availability hn hbind hikS havail
    obtain ⟨cand, hcand, -, hnext, hkid, hcik, -, -, hcad⟩ := hpok hmax hfree
    obtain ⟨resp, S', pr, hemit, hrespkid, hSn, hScons, hSpeers, hprik, hprad⟩ :=
      serverEmit_ok c { S with consumed := (absVerified reg).rid :: S.consumed }
        (absVerified reg).ikB
        (Pqxdh.rootSecret c (Pqxdh.ikmOf (Pqxdh.serverDHs c S.ikSk eSk ikBX
          (absVerified reg).preKey (absVerified reg).otKey)
          (c.encap (absVerified reg).kemPub coins).2))
        (c.encap (absVerified reg).kemPub coins).1 (c.xpub eSk) (app.getD [0xFF])
        hmax hfree
    refine ⟨cand.next_state,
      { key_id := cand.key_id, identity_public_key := cand.beacon_identity_public_key,
        associated_data := cand.associated_data }, resp, S', pr,
      by simp [serverRegister, hacc, hcand, pqxdh.server_commit], ?_, hrespkid, hSn, ?_, ?_, ?_, ?_, hScons, hSpeers, ?_, ?_⟩
    · rw [serverRespond_eq_emit c S m eSk coins ikBX app _ hval hrid hconv hnz happ]
      exact hemit
    · rw [hnext, hSn]
    · rw [hkid, hrespkid]
    · rw [hcik, hpik]
    · rw [hcad, hpik]
    · rw [hprik]
    · rw [hprad]

/-- **The generated rollback is the ideal transactional rollback**: a candidate that
is not committed leaves the allocation counter exactly as it was. -/
theorem server_abort_candidate_refines (S : Pqxdh.ServerState)
    (state : pqxdh.ServerState) (cand : pqxdh.ServerRegistrationCandidate)
    (hprev : cand.previous_state = state) (hn : state.last_key_id.val = S.n) :
    ∃ st, pqxdh.server_abort_candidate cand = ok st ∧ st.last_key_id.val = S.n := by
  exact ⟨cand.previous_state, rfl, by rw [hprev, hn]⟩

/-! ## The beacon's processing of the response (spec §15–§18) -/

/-- The rejection of the extracted core that corresponds to an ideal beacon abort.
The aborts the extracted core cannot express are the ones its callers detect: a
failed decapsulation, a failed identity-key conversion, an inadmissible record and a
malformed plaintext. -/
def genBeaconError : Pqxdh.BeaconError → Option pqxdh.RegistrationError
  | .notInitSent => none
  | .badResponse => none
  | .kemFailure => none
  | .identityMismatch => some pqxdh.RegistrationError.IdentityMismatch
  | .zeroDH => some pqxdh.RegistrationError.InvalidDhOutput
  | .badRecord => none
  | .badSender => some pqxdh.RegistrationError.IdentityMismatch
  | .badPlaintext => none
  | .keyIdMismatch => some pqxdh.RegistrationError.KeyIdMismatch

/-- The generated beacon completion, assembled from the extracted steps: check the
pinned identity and derive the PQXDH transcript and the associated data, then check
the authenticated sender and the authenticated key-identifier binding, then commit. -/
def beaconFinishDriver (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (authSenderId : Std.U64) (authBinding : Std.Array Std.U8 8#usize) :
    Result (core.result.Result pqxdh.BeaconEstablished pqxdh.RegistrationError) := do
  let r ← pqxdh.beacon_prepare_finish state inputs
  match r with
  | core.result.Result.Err e => ok (core.result.Result.Err e)
  | core.result.Result.Ok cand =>
    let r1 ← pqxdh.authenticate_registration_key_id_binding cand authSenderId authBinding
    match r1 with
    | core.result.Result.Err e => ok (core.result.Result.Err e)
    | core.result.Result.Ok auth =>
      let est ← pqxdh.beacon_commit auth
      ok (core.result.Result.Ok est)

/-- **Main beacon refinement.**  With the values the primitives and the record layer
return — the decapsulated shared secret, the role-reversed X25519 contributions, the
authenticated sender identifier and the authenticated key-identifier binding — the
generated beacon pipeline returns exactly the outcome of the handwritten
`Pqxdh.beaconFinish`: the same abort in each of the three abort cases the extracted
core can express, and on success the ideal assigned identifier with the pinned
binding retained. -/
theorem beaconFinishDriver_refines (c : Pqxdh.Crypto) (b : Pqxdh.ServerBinding)
    (ikSk preSk otSk kemSk ikSX ss : Pqxdh.Bytes) (resp : Pqxdh.KexResponse)
    (pt : Pqxdh.Bytes) (recv' : Ratchet.RecvState Pqxdh.Bytes (Pqxdh.Bytes × Pqxdh.Bytes))
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (authSenderId : Std.U64) (authBinding : Std.Array Std.U8 8#usize)
    (hdecap : c.decap kemSk resp.kemCipherText = some ss)
    (hconv : c.xpkConv resp.identityKey = some ikSX)
    (hbindpk : absBytes state.expected_server_binding.identity_public_key = b.ikPub)
    (hbindid : state.expected_server_binding.identity_key_id.val = b.sid)
    (hrespid : absBytes inputs.response_server_identity = resp.identityKey)
    (hdh : absDHs inputs.shared_secrets
      = Pqxdh.beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey)
    (hkid : inputs.assigned_key_id.val = resp.keyId)
    (hsender : authSenderId.val = resp.appFrame.keyId)
    (hseq : resp.appFrame.seq ≠ 0)
    (hrecv : Ratchet.recvStep (Pqxdh.ratchetCrypto c)
        ⟨(Pqxdh.rootChains c
          (Pqxdh.beaconRoot c ikSk preSk otSk ikSX resp.ephemeralKey ss)).1, 0, []⟩
        ⟨Pqxdh.assocData b.ikPub (c.edPub ikSk), resp.appFrame.seq, resp.appFrame.keyId⟩
        ⟨resp.appFrame.seq - 1, resp.appFrame.cipherText⟩ = (Except.ok pt, recv'))
    (hptlen : 8 < pt.length)
    (hauthbind : absBytes authBinding = pt.take 8) :
    -- the response does not carry the pinned server identity
    (resp.identityKey ≠ b.ikPub →
      beaconFinishDriver state inputs authSenderId authBinding
          = ok (core.result.Result.Err pqxdh.RegistrationError.IdentityMismatch) ∧
      Pqxdh.beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp =
        (Except.error Pqxdh.BeaconError.identityMismatch, .aborted)) ∧
    -- an all-zero X25519 contribution
    (resp.identityKey = b.ikPub →
      ¬ Pqxdh.dhNonZero (Pqxdh.beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey) →
      beaconFinishDriver state inputs authSenderId authBinding
          = ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput) ∧
      Pqxdh.beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp =
        (Except.error Pqxdh.BeaconError.zeroDH, .aborted)) ∧
    -- the record was authenticated under another sender
    (resp.identityKey = b.ikPub →
      Pqxdh.dhNonZero (Pqxdh.beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey) →
      resp.appFrame.keyId ≠ b.sid →
      beaconFinishDriver state inputs authSenderId authBinding
          = ok (core.result.Result.Err pqxdh.RegistrationError.IdentityMismatch) ∧
      Pqxdh.beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp =
        (Except.error Pqxdh.BeaconError.badSender, .aborted)) ∧
    -- the record does not bind the assigned identifier
    (resp.identityKey = b.ikPub →
      Pqxdh.dhNonZero (Pqxdh.beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey) →
      resp.appFrame.keyId = b.sid → pt.take 8 ≠ Pqxdh.LE64 resp.keyId →
      beaconFinishDriver state inputs authSenderId authBinding
          = ok (core.result.Result.Err pqxdh.RegistrationError.KeyIdMismatch) ∧
      Pqxdh.beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp =
        (Except.error Pqxdh.BeaconError.keyIdMismatch, .aborted)) ∧
    -- the registration completes
    (resp.identityKey = b.ikPub →
      Pqxdh.dhNonZero (Pqxdh.beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey) →
      resp.appFrame.keyId = b.sid → pt.take 8 = Pqxdh.LE64 resp.keyId →
      ∃ est : pqxdh.BeaconEstablished,
        beaconFinishDriver state inputs authSenderId authBinding
            = ok (core.result.Result.Ok est) ∧
        est.assigned_key_id.val = resp.keyId ∧
        absBinding est.server_binding = b ∧
        Pqxdh.beaconFinish c (.initSent b ikSk preSk otSk kemSk) resp =
          (Except.ok resp.keyId,
            .established b ikSk resp.keyId (Pqxdh.assocData b.ikPub (c.edPub ikSk))
              ⟨(Pqxdh.rootChains c (Pqxdh.beaconRoot c ikSk preSk otSk ikSX
                resp.ephemeralKey ss)).2, 0⟩ recv')) := by
  -- the generated identity comparison decides the ideal pinned-identity test
  have hidcmp : core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8
      state.expected_server_binding.identity_public_key inputs.response_server_identity
      = ok (decide (b.ikPub = resp.identityKey)) := by
    rw [array_eq_abs, hbindpk, hrespid]
  have hzero := (build_root_key_input_abs inputs.shared_secrets).2
  have hok := (build_root_key_input_abs inputs.shared_secrets).1
  have habs : (absBytes inputs.shared_secrets.dh1, absBytes inputs.shared_secrets.dh2,
      absBytes inputs.shared_secrets.dh3, absBytes inputs.shared_secrets.dh4)
      = Pqxdh.beaconDHs c ikSk preSk otSk ikSX resp.ephemeralKey := hdh
  rw [habs] at hzero hok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hne
    refine ⟨?_, ?_⟩
    · simp [beaconFinishDriver, pqxdh.beacon_prepare_finish, hidcmp, Ne.symm hne]
    · simp [Pqxdh.beaconFinish, hdecap, hne]
  · intro heq hz
    rw [heq] at hconv
    refine ⟨?_, ?_⟩
    · simp [beaconFinishDriver, pqxdh.beacon_prepare_finish, hidcmp, heq, hzero hz]
    · simp [Pqxdh.beaconFinish, hdecap, heq, hconv, hz]
  · intro heq hnz hsid
    obtain ⟨v, hv, -⟩ := hok hnz
    obtain ⟨a, ha, -⟩ := build_associated_data_abs
      state.expected_server_binding.identity_public_key state.beacon_identity_public_key
    have hsidne : ¬ (authSenderId = state.expected_server_binding.identity_key_id) := by
      intro hc
      exact hsid (by rw [← hsender, hc, hbindid])
    refine ⟨?_, ?_⟩
    · simp [beaconFinishDriver, pqxdh.beacon_prepare_finish, hidcmp, heq, hv, ha,
        pqxdh.authenticate_registration_key_id_binding, hsidne]
    · rw [heq] at hconv
      simp [Pqxdh.beaconFinish, hdecap, heq, hconv, hnz, hsid]
  · intro heq hnz hsid hbind
    obtain ⟨v, hv, -⟩ := hok hnz
    obtain ⟨a, ha, -⟩ := build_associated_data_abs
      state.expected_server_binding.identity_public_key state.beacon_identity_public_key
    have hsideq : authSenderId = state.expected_server_binding.identity_key_id :=
      Std.UScalar.eq_of_val_eq (by rw [hsender, hbindid, hsid])
    obtain ⟨rk, hrk, hrkabs⟩ := registration_key_id_binding_abs inputs.assigned_key_id
    have hbindcmp : core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8
        authBinding rk.bytes = ok (decide (pt.take 8 = Pqxdh.LE64 resp.keyId)) := by
      rw [array_eq_abs, hauthbind, hrkabs, hkid]
    refine ⟨?_, ?_⟩
    · simp [beaconFinishDriver, pqxdh.beacon_prepare_finish, hidcmp, heq, hv, ha,
        pqxdh.authenticate_registration_key_id_binding, hsideq,
        pqxdh.BeaconRegistrationCandidate.key_id_binding, hrk, hbindcmp, hbind]
    · rw [heq] at hconv
      rw [hsid] at hrecv
      simp [Pqxdh.beaconFinish, hdecap, heq, hconv, hnz, hsid, hseq, hrecv,
        Nat.not_le.mpr hptlen, hbind]
  · intro heq hnz hsid hbind
    obtain ⟨v, hv, -⟩ := hok hnz
    obtain ⟨a, ha, -⟩ := build_associated_data_abs
      state.expected_server_binding.identity_public_key state.beacon_identity_public_key
    have hsideq : authSenderId = state.expected_server_binding.identity_key_id :=
      Std.UScalar.eq_of_val_eq (by rw [hsender, hbindid, hsid])
    obtain ⟨rk, hrk, hrkabs⟩ := registration_key_id_binding_abs inputs.assigned_key_id
    have hbindcmp : core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8
        authBinding rk.bytes = ok (decide (pt.take 8 = Pqxdh.LE64 resp.keyId)) := by
      rw [array_eq_abs, hauthbind, hrkabs, hkid]
    refine ⟨⟨state.expected_server_binding, inputs.assigned_key_id⟩, ?_, hkid, ?_, ?_⟩
    · simp [beaconFinishDriver, pqxdh.beacon_prepare_finish, hidcmp, heq, hv, ha,
        pqxdh.authenticate_registration_key_id_binding, hsideq,
        pqxdh.BeaconRegistrationCandidate.key_id_binding, hrk, hbindcmp, hbind,
        pqxdh.beacon_commit]
    · rw [absBinding, hbindpk, hbindid]
    · rw [heq] at hconv
      rw [hsid] at hrecv
      simp [Pqxdh.beaconFinish, hdecap, heq, hconv, hnz, hsid, hseq, hrecv,
        Nat.not_le.mpr hptlen, hbind]

/-- **The generated beacon abort is the ideal abort**: leaving `InitSent` without
completing keeps only the pinned server identifier, which is exactly the ideal
`Aborted` state (spec §17: no registration-local key material survives). -/
theorem beacon_abort_init_refines (b : Pqxdh.ServerBinding)
    (state : pqxdh.BeaconInitSent)
    (hbindid : state.expected_server_binding.identity_key_id.val = b.sid) :
    ∃ ab, pqxdh.beacon_abort_init state = ok ab ∧ ab.server_key_id.val = b.sid :=
  ⟨_, rfl, hbindid⟩

end PqxdhRefinement
