-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileStep
import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-! Footprints of the source14 registration commands used to keep the public reconstruction of the CE-3 trial valid. A raw accept never changes the Server peer map, identity or key ID, advances the session counter by one and, on success, stores at the returned handle a token whose Beacon identity is the identity key read from the accept bytes by the codec reader and the Server's identity parser. A build never changes the Server identity or key ID; on success it installs exactly one new peer, at the previously unoccupied key ID returned in the response, with the Beacon identity of the consumed token, and its response bytes are the Phase 2 writer output of fields whose Server identity is the Server's own. These are facts of the native code; no codec law is used here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhJointDhExtractRoot (RootSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The Server peer map, Server identity and key ID, pending tokens and session counter. -/
def ServerFixed (before after : GameState KemSK) : Prop :=
  after.server.server = before.server.server ∧ after.server.identityKeyId = before.server.identityKeyId ∧
    after.pending = before.pending ∧ after.sessions = before.sessions

/-- The public HMAC changes only the ghost and the Extract family. -/
theorem hmac_fixed (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (game : GameState KemSK)
    (result : PqxdhSecretInputKdf.HmacBlock × GameState KemSK)
    (supported : result ∈ support ((hmacOracle key message).run game)) : ServerFixed game result.2 := by
  unfold hmacOracle at supported
  split at supported
  · rw [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨_, middle⟩, touched, forwarded⟩ := supported
    have touchedRun : (recordTouch (KemSK := KemSK) (.adversary message)).run game =
        pure ((), { game with ghost := { game.ghost with touches := game.ghost.touches ++ [.adversary message] } }) := rfl
    rw [touchedRun, support_pure, Set.mem_singleton_iff] at touched
    cases touched
    dsimp only at forwarded
    have same : result.2 = _ := forward_support (KemSK := KemSK) (.inr (.publicHmac key message)) _ result forwarded
    rw [same]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · dsimp only at supported
    have same : result.2 = _ := forward_support (KemSK := KemSK) (.inr (.publicHmac key message)) _ result supported
    rw [same]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The public BLAKE2b oracle changes only the shared cache. -/
theorem hash_fixed (bytes : Pqxdh.Bytes) (game : GameState KemSK) (result : CtxRomAuth.CtxDigest × GameState KemSK)
    (supported : result ∈ support ((hashOracle bytes).run game)) : ServerFixed game result.2 := by
  simp only [hashOracle, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The identity key read from accepted Phase 1 bytes is the identity the Server's attached verification accepted. -/
theorem identityOf_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (verified : PqxdhServerRootPreparation.Verified Reader)
    (decoded : PqxdhServerAuthPhase1Receipt.Decoded codec raw verified)
    (accepted : PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
      verified.candidate = some (verified.identity, verified.keys)) :
    PqxdhDeploymentCompile.identityOf codec raw = some (PqxdhRootTableInitialization.rootArray verified.identity) := by
  have parsed := PqxdhServerAuthPhase1Identity.accepted_identity _ _ _ _ accepted
  simp only [PqxdhDeploymentCompile.identityOf, decoded.1, decoded.2.1, parsed, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

/-- `get_shared_secret` never changes the Server peer map, identity or key ID and advances the session counter by one; a rejected accept keeps every pending token, and a successful accept returns the current handle and stores there a token whose Beacon identity is the identity key read from the accept bytes. -/
theorem accept_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (game : GameState KemSK) (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run game)) :
    result.2.server.server = game.server.server ∧ result.2.server.identityKeyId = game.server.identityKeyId ∧
      result.2.sessions = game.sessions + 1 ∧
      (∀ session, session ≠ game.sessions → result.2.pending session = game.pending session) ∧
      (result.1 = none → result.2.pending = game.pending) ∧
      (∀ session, result.1 = some session → session = game.sessions ∧ ∃ token,
        result.2.pending session = some token ∧
        PqxdhDeploymentCompile.identityOf codec raw = some token.pending.beacon_identity_public_key) := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨prefixMember, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ found => by cases found⟩
  | some input =>
      have member : (some input, collected.1.2) ∈ support ((serverPrefix setup codec checks raw).run
          game.server.consumed) := by
        rw [← hc]
        exact prefixMember
      obtain ⟨decoded, accepted⟩ := PqxdhServerAuthPhase1Receipt.prefix_receipt setup codec checks raw _ _ input member
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, _, tokens⟩ := client_run game.sessions (binding setup publicValue) input _
        returned derived
      rcases returned with ⟨outcome, after⟩
      dsimp only at eq tokens
      rcases outcome with (_ | token) | error | _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rw [eq]
        exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ found => by cases found⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        obtain ⟨_, _, pendingEq⟩ := tokens token rfl
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [eq]
        · rw [eq]
        · rw [eq]
        · intro other different
          simp only [Function.update_of_ne different]
          rw [eq]
        · intro found
          cases found
        · intro session found
          simp only [Option.some.injEq] at found
          subst found
          refine ⟨rfl, token, Function.update_self .., ?_⟩
          rw [pendingEq]
          exact identityOf_receipt setup codec raw input.verified decoded accepted
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rw [eq]
        exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ found => by cases found⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rw [eq]
        exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ found => by cases found⟩

/-- `build_registration_response` never changes the Server identity, key ID or session counter and always removes the session's token; a rejected build keeps the peer map, and a successful build installs exactly one new peer, at the previously unoccupied key ID returned in the response, with the Beacon identity of the consumed token, and returns the Phase 2 writer output of fields carrying the Server's own identity. -/
theorem build_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (game : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run game)) :
    result.2.server.server.identity = game.server.server.identity ∧
      result.2.server.identityKeyId = game.server.identityKeyId ∧ result.2.sessions = game.sessions ∧
      (∀ other, other ≠ session → result.2.pending other = game.pending other) ∧
      result.2.pending session = none ∧
      (result.1 = none → result.2.server.server.peers = game.server.server.peers) ∧
      (∀ response, result.1 = some response → ∃ token kernel fields,
        game.pending session = some token ∧ game.server.server.peers response.keyId = none ∧
        result.2.server.server.peers = Function.update game.server.server.peers response.keyId
          (some ⟨token.pending.beacon_identity_public_key, kernel, ()⟩) ∧
        codec.write2 fields = some response.serialized ∧ fields.identity = game.server.server.identity) := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : game.pending session with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl, found, fun _ => rfl, fun _ reply => by cases reply⟩
  | some token =>
      simp only [found, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨built, lifted, supported⟩ := supported
      obtain ⟨member, same⟩ := liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      have identity : (settle game.server built.1.1).2.server.identity = game.server.server.identity ∧
          (settle game.server built.1.1).2.identityKeyId = game.server.identityKeyId ∧
          ((settle game.server built.1.1).1 = none →
            (settle game.server built.1.1).2.server.peers = game.server.server.peers) := by
        rcases PqxdhRegistrationResponse.build_publication (tailImpl setup codec checks) setup.source token.pending
            token.root payload () game.server _ built.1 member with unchanged | ⟨next, candidate, kernel, bytes, _, _, published⟩
        · simp only [unchanged, settle, and_self, implies_true]
        · simp only [published, settle, PqxdhServerRegistrationPublication.publish, reduceCtorEq, false_implies,
            and_self]
      refine ⟨identity.1, identity.2.1, rfl, fun other different => Function.update_of_ne different _ _,
        Function.update_self .., identity.2.2, fun response reply => ?_⟩
      obtain ⟨candidateWritten, kernelWritten, _, frameBytes, beacon, server, _, _, _, _, _, _, _, _, written, _⟩ :=
        PqxdhServerAuthNegativeControl.build_published setup codec checks token.pending token.root payload game.server
          game.ctx built.1 member response reply
      rcases PqxdhRegistrationResponse.build_publication (tailImpl setup codec checks) setup.source token.pending
          token.root payload () game.server _ built.1 member with unchanged | ⟨next, candidate, kernel, bytes, hnext, prepared, published⟩
      · simp only [unchanged, settle, reduceCtorEq] at reply
      · simp only [published, settle, Option.some.injEq] at reply
        subst reply
        obtain ⟨available, key⟩ := PqxdhDeploymentCompileRegistration.prepare_key _ _ _ _ candidate prepared
        rw [hnext] at key
        have sameKey : next = candidate.key_id := by
          cases key
          rfl
        subst sameKey
        have free : game.server.server.peers candidate.key_id = none := by
          by_contra occupied
          rw [Option.isSome_iff_ne_none.mpr occupied] at available
          simp at available
        have fields := PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ candidate prepared
        refine ⟨token, kernel, _, rfl, free, ?_, written, ?_⟩
        · simp only [published, settle, PqxdhServerRegistrationPublication.publish, fields.1]
        · exact server

/-- The three Phase 1 signatures of an owner always succeed under the bundle callbacks, with the owner's own seed. -/
theorem signing_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (seed : IdentitySeed)
    (index : Nat) (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : PqxdhEd25519EufCma.Phase1KeyTuple) :
    simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec seed)
      (PqxdhLivePhase1Bundle.signing (D := ScalarBytes) index identity keys) =
      pure (some (PqxdhJointPhase1SourceWriter.candidate identity keys
        (setup.joint.sign seed (PqxdhEd25519EufCma.prekeyMessage keys.prekey))
        (setup.joint.sign seed (PqxdhEd25519EufCma.oneTimeMessage keys.oneTime))
        (setup.joint.sign seed (PqxdhEd25519EufCma.pqMessage keys.pqKey)))) := by
  rfl

/-- The Phase 1 writer continuation under the bundle callbacks is the codec writer on the signed candidate. -/
theorem writing_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (seed : IdentitySeed)
    (identity : Std.Array Std.U8 32#usize) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (generated : Option ScalarBytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec seed)
      (PqxdhLivePhase1Bundle.writing identity candidate generated owner) =
      pure (match PqxdhBeaconPhase1Publication.prepare owner generated with
        | none => (none, owner)
        | some prepared => match codec.write1 candidate with
          | none => (none, owner)
          | some bytes => (some bytes, PqxdhBeaconPhase1Publication.publish identity prepared owner)) := by
  unfold PqxdhLivePhase1Bundle.writing PqxdhBeaconPhase1Publication.afterSigning
  cases PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => rfl
  | some prepared =>
      cases written : codec.write1 candidate with
      | none =>
          simp only [simulateQ_bind, simulateQ_spec_query]
          change (pure (codec.write1 candidate) >>= _ : ProbComp _) = _
          rw [written, pure_bind]
          rfl
      | some bytes =>
          simp only [simulateQ_bind, simulateQ_spec_query]
          change (pure (codec.write1 candidate) >>= _ : ProbComp _) = _
          rw [written, pure_bind]
          rfl

/-- A Beacon bundle keeps the owner on every rejection; a published bundle came from a Fresh owner, installs InitSent with the same expected binding and the owner's own identity key, and is the Phase 1 writer output of a candidate carrying that identity key. -/
theorem bundle_owner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK)
    (supported : result ∈ support (simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
      (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup index) owner))) :
    (result.1 = none → result.2 = owner) ∧
      (∀ bytes, result.1 = some bytes → ∃ fresh prekey oneTime kem candidate,
        (owner.beacon.phase = .fresh fresh prekey kem ∨ owner.beacon.phase = .freshWithCoins fresh prekey oneTime kem) ∧
        result.2 = { owner with beacon := { owner.beacon with phase := (.initSent
          ⟨fresh.expected_server_binding, PqxdhLivePhase1Bundle.identityArray
            (setup.joint.publicKeys owner.beacon.identity).ed25519⟩ prekey oneTime kem) } } ∧
        codec.write1 candidate = some bytes ∧
        candidate.identityKey = PqxdhEd25519EufCma.encodedIdentity (setup.joint.publicKeys owner.beacon.identity).ed25519) := by
  unfold PqxdhLivePhase1Bundle.bundle at supported
  cases phase : owner.beacon.phase with
  | fresh fresh prekey kem =>
      simp only [phase, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨generated, gen, rest⟩ := supported
      simp only [PqxdhRegistrationSchedule.bundleCallbacks, support_map, Set.mem_image] at gen
      obtain ⟨oneTime, _, rfl⟩ := gen
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, phase, Option.map_some,
        simulateQ_bind, signing_run, pure_bind, writing_run] at rest
      rw [support_pure, Set.mem_singleton_iff] at rest
      subst rest
      split
      · exact ⟨fun _ => rfl, fun bytes found => by simp at found⟩
      · rename_i bytes written
        refine ⟨fun found => by simp at found, fun other found => ?_⟩
        simp only [Option.some.injEq] at found
        subst found
        exact ⟨fresh, prekey, oneTime, kem, _, Or.inl rfl, rfl, written, rfl⟩
  | freshWithCoins fresh prekey oneTime kem =>
      simp only [phase, PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare,
        simulateQ_bind, signing_run, pure_bind, writing_run] at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      split
      · exact ⟨fun _ => rfl, fun bytes found => by simp at found⟩
      · rename_i bytes written
        refine ⟨fun found => by simp at found, fun other found => ?_⟩
        simp only [Option.some.injEq] at found
        subst found
        exact ⟨fresh, prekey, oneTime, kem, _, Or.inr rfl, rfl, written, rfl⟩
  | _ =>
      simp only [phase, simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun _ => rfl, fun bytes found => by simp at found⟩

set_option maxRecDepth 100000 in
/-- A prepared Beacon finish candidate keeps the expected Server binding of the InitSent control, takes the assigned key ID from the finish inputs, and carries the associated data of the control's Server and Beacon identity keys. -/
theorem prepare_finish_fields (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (inputs : beaconcrypt_core.pqxdh.BeaconFinishInputs) (candidate : beaconcrypt_core.pqxdh.BeaconRegistrationCandidate)
    (prepared : beaconcrypt_core.pqxdh.beacon_prepare_finish control inputs = .ok (.Ok candidate)) :
    candidate.server_binding = control.expected_server_binding ∧ candidate.assigned_key_id = inputs.assigned_key_id ∧
      candidate.associated_data = PqxdhBeaconPhase2Shared.associatedData control := by
  obtain ⟨root, hroot⟩ := BeaconcryptCore.PanicFreedom.build_root_key_input_ok inputs.shared_secrets
  obtain ⟨ad, had⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok control.expected_server_binding.identity_public_key
    control.beacon_identity_public_key
  have chosen : ad = PqxdhBeaconPhase2Shared.associatedData control := by
    have spec := (BeaconcryptCore.PanicFreedom.build_associated_data_ok control.expected_server_binding.identity_public_key
      control.beacon_identity_public_key).choose_spec
    exact RustM.ok.inj (had.symm.trans spec)
  by_cases hid : PqxdhRefinement.absBytes control.expected_server_binding.identity_public_key =
      PqxdhRefinement.absBytes inputs.response_server_identity
  · cases root <;>
      simp [beaconcrypt_core.pqxdh.beacon_prepare_finish, PqxdhRefinement.array_eq_abs, hid, hroot, had] at prepared
    subst prepared
    exact ⟨rfl, rfl, chosen⟩
  · simp [beaconcrypt_core.pqxdh.beacon_prepare_finish, PqxdhRefinement.array_eq_abs, hid] at prepared

set_option maxRecDepth 100000 in
/-- A successful binding authentication returns exactly the given candidate. -/
theorem authenticate_candidate (candidate : beaconcrypt_core.pqxdh.BeaconRegistrationCandidate) (sender : Std.U64)
    (binding : Std.Array Std.U8 8#usize) (authenticated : beaconcrypt_core.pqxdh.AuthenticatedBeaconRegistration)
    (accepted : beaconcrypt_core.pqxdh.authenticate_registration_key_id_binding candidate sender binding =
      .ok (.Ok authenticated)) :
    authenticated.candidate = candidate := by
  obtain ⟨expected, hexpected⟩ := BeaconcryptCore.PanicFreedom.registration_key_id_binding_ok candidate.assigned_key_id
  by_cases hid : sender = candidate.server_binding.identity_key_id <;>
    by_cases hbinding : PqxdhRefinement.absBytes binding = PqxdhRefinement.absBytes expected.bytes <;>
    simp [beaconcrypt_core.pqxdh.authenticate_registration_key_id_binding,
      beaconcrypt_core.pqxdh.BeaconRegistrationCandidate.key_id_binding, hid, hexpected, PqxdhRefinement.array_eq_abs,
      hbinding] at accepted
  subst accepted
  rfl

/-- The source14 Beacon preparation callbacks: every callback is a local computation on the shared native state. -/
noncomputable def preparationHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) (NativeGame KemSK) :=
  fun query => nativeCoins (PqxdhRegistrationSchedule.preparation setup codec query)

/-- Collected Beacon finish inputs carry the response read from the finish bytes by the codec Phase 2 reader, and the assigned key ID read from that response. -/
theorem collect_inputs (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identity : IdentitySeed)
    (prekey oneTime : ScalarBytes) (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (shared : NativeState KemSK) (inputs : PqxdhBeaconPhase2Preparation.Inputs Response) (after : NativeState KemSK)
    (supported : (some inputs, after) ∈ support ((simulateQ (preparationHandler setup codec)
      (PqxdhBeaconPhase2Preparation.collect identity prekey oneTime kem raw)).run shared)) :
    codec.read2 raw = some inputs.response ∧ inputs.finishInputs.assigned_key_id = codec.assignedId inputs.response := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query] at supported
  have decodeRun : (preparationHandler setup codec (.decode raw)).run shared = pure (codec.read2 raw, shared) := rfl
  rw [StateT.run_bind, decodeRun, pure_bind] at supported
  cases decoded : codec.read2 raw with
  | none => simp [decoded] at supported
  | some response =>
      simp only [decoded, Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply1, state1⟩, member1, supported⟩ := supported
      rcases reply1 with _ | reply1
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply2, state2⟩, member2, supported⟩ := supported
      rcases reply2 with _ | reply2
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply3, state3⟩, member3, supported⟩ := supported
      rcases reply3 with _ | reply3
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply4, state4⟩, member4, supported⟩ := supported
      rcases reply4 with _ | reply4
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply5, state5⟩, member5, supported⟩ := supported
      rcases reply5 with _ | reply5
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply6, state6⟩, member6, supported⟩ := supported
      rcases reply6 with _ | reply6
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply7, state7⟩, member7, supported⟩ := supported
      rcases reply7 with _ | reply7
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply8, state8⟩, member8, supported⟩ := supported
      rcases reply8 with _ | reply8
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply9, state9⟩, member9, supported⟩ := supported
      rcases reply9 with _ | reply9
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply10, state10⟩, member10, supported⟩ := supported
      rcases reply10 with _ | reply10
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨assigned, final⟩, assignedMember, supported⟩ := supported
      change (assigned, final) ∈ support (pure (codec.assignedId response, state10) : ProbComp _) at assignedMember
      rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at assignedMember
      obtain ⟨rfl, rfl⟩ := assignedMember
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at supported
      obtain ⟨rfl, rfl⟩ := supported
      exact ⟨rfl, rfl⟩

/-- A Beacon finish: a rejection keeps the owner or aborts an InitSent owner; a success comes from an InitSent owner and installs Established with the expected Server binding, the assigned key ID read from the finish bytes by the codec Phase 2 reader as both the control's assigned key ID and the outer key ID, and the associated data of the InitSent control. -/
theorem finish_owner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run shared)) :
    (result.1.1 = none → result.1.2 = owner ∨ ∃ control prekey oneTime kem,
        owner.beacon.phase = .initSent control prekey oneTime kem ∧
        result.1.2 = PqxdhBeaconPhase2Preparation.abort control owner) ∧
      (∀ plaintext, result.1.1 = some plaintext → ∃ control prekey oneTime kem response kernel,
        owner.beacon.phase = .initSent control prekey oneTime kem ∧ codec.read2 raw = some response ∧
        result.1.2 = { owner with beacon := { owner.beacon with
          identityKeyId := codec.assignedId response
          phase := (.established ⟨control.expected_server_binding, codec.assignedId response⟩
            (PqxdhBeaconPhase2Shared.associatedData control) kernel) } }) := by
  rw [PqxdhBeaconPhase2Publication.nativeOwner, ← QueryImpl.simulateQ_compose] at supported
  rcases result with ⟨⟨reply, next⟩, final⟩
  constructor
  · intro failed
    simp only at failed
    subst failed
    have shape := PqxdhBeaconPhase2Publication.owner_failure _ codec.frameRead raw owner next shared final supported
    revert shape
    cases phase : owner.beacon.phase with
    | initSent control prekey oneTime kem =>
        intro shape
        exact Or.inr ⟨control, prekey, oneTime, kem, rfl, shape⟩
    | _ =>
        intro shape
        exact Or.inl shape.1
  · intro plaintext succeeded
    simp only at succeeded
    subst succeeded
    obtain ⟨control, prekey, oneTime, kem, prepared, intermediate, staged, phase, prepareSupport, tailSupport,
      _, _, _, published⟩ := PqxdhBeaconPhase2Publication.owner_success _ codec.frameRead raw plaintext owner next
        shared final supported
    have handlerEq : (fun query => (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ
        PqxdhBeaconPhase2Publication.nativeAdapter) (.inl query)) = preparationHandler setup codec := by
      funext query
      simp only [QueryImpl.compose, PqxdhBeaconPhase2Publication.nativeAdapter, simulateQ_spec_query]
      rfl
    rw [handlerEq] at prepareSupport
    obtain ⟨inputs, middle, collected, _, finished, _, _, _⟩ :=
      PqxdhBeaconPhase2Preparation.prepare_origin _ control owner.beacon.identity prekey oneTime kem raw shared
        intermediate prepared prepareSupport
    obtain ⟨decoded, assignedEq⟩ := collect_inputs setup codec owner.beacon.identity prekey oneTime kem raw shared
      inputs middle collected
    obtain ⟨binding, assigned, associated⟩ := prepare_finish_fields control inputs.finishInputs prepared.candidate finished
    obtain ⟨root, rootState, _, rooted⟩ := PqxdhBeaconPhase2Publication.tail_supported _ codec.frameRead prepared
      intermediate final staged tailSupport
    obtain ⟨_, _, _, _, received, _, _, _, _, opened⟩ := PqxdhBeaconPhase2Publication.afterRoot_supported _
      codec.frameRead prepared root rootState final staged rooted
    obtain ⟨_, _, kernelEq, adEq, _, authenticated⟩ := PqxdhBeaconPhase2Publication.afterOpening_success _ _ _ staged opened
    have candidateEq := authenticate_candidate _ _ _ _ authenticated
    refine ⟨control, prekey, oneTime, kem, inputs.response, staged.kernel, phase, ?_, ?_⟩
    · exact decoded
    · have nextEq := congrArg Prod.snd published
      simp only at nextEq
      rw [← nextEq]
      simp only [PqxdhBeaconPhase2Publication.publish, candidateEq, adEq,
        PqxdhBeaconPhase2Publication.clearedCandidate_fields, binding, assigned, assignedEq, associated]

end BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.hmac_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.hmac_fixed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.hash_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.hash_fixed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.identityOf_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.identityOf_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.accept_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.accept_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.build_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.build_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.signing_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.signing_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.writing_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.writing_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.bundle_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.bundle_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.prepare_finish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.prepare_finish_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.authenticate_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.authenticate_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.collect_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.collect_inputs

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.finish_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint.finish_owner
