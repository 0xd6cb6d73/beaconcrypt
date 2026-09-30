import BeaconcryptCore.Computational.PqxdhServerAuthExperiment
import BeaconcryptCore.Computational.PqxdhServerAuthAssumptions
import BeaconcryptCore.Computational.PqxdhKemCorrectnessError
import BeaconcryptCore.Computational.RawCtxSourcePublication
import BeaconcryptCore.Refinement.RatchetReceiveIdeal
import BeaconcryptCore.Refinement.PqxdhConcreteSession

/-!
# Server authentication: the negative controls (gate B5a)

This module is stage B5a of the Server-authentication proof (Milestone B). It is the gate for the experiment of stage B4a (`PqxdhServerAuthExperiment`): before any bound is proved about that experiment, it runs explicit adversaries through it exactly and checks three things. With the Server seed revealed, the event `W1` (the Beacon accepts without a partner session) is reachable. An honest relay does not win. An honest relay does reach the Beacon's acceptance, so the second check is not passed vacuously. All three checks succeed, so no B4a definition had to change.

The negative control. `negative_control` states that, when the Server's Ed25519 identity seed is revealed at the start, the adversary `controlAdversary` makes the Beacon accept without any partner session, the event `W1`, with probability at least one minus the KEM correctness error `kemError`; `negative_control_win` restates this for the experiment's success probability, since `W1` implies `Win`. The adversary never queries the Server (`control_no_server`), and it makes at most one random-oracle HMAC query and at most one BLAKE2b query (`control_budget`). It parses the target Beacon's published Phase 1 with the codec, without verifying the signatures, draws an ephemeral X25519 scalar and an ML-KEM encapsulation to the Beacon's ML-KEM key from its own coins, and forms the 192-byte root input that an honest Server with the revealed seed would derive (`controlBytes`). It obtains the Extract block of that input from the public zero-key HMAC oracle, expands it locally into the root and the Beacon's sequence-one material, seals the key-ID binding and a nonempty payload under the Beacon's associated data, obtains the commitment from the public BLAKE2b oracle, writes the frame and the Phase 2, and sends the Phase 2 to the Beacon's finish. Whenever the Beacon's decapsulation recovers the encapsulated secret, the Beacon derives the same root through the same table entry (`beacon_input_eq`), opens the record and accepts, and since no Server session exists the acceptance has no partner, so `W1` holds. The revealed seed is therefore enough to break the claim before the finish, which is why the headline game of B4a does not reveal it.

The relay control. `relay_not_win` states that the honest relay `relayAdversary`, which passes the target Beacon's Phase 1 to the Server's accept, builds the accepted session with a payload of its choice and passes the Server's Phase 2 to the Beacon's finish, wins with probability at most the KEM correctness error, for every `Checks`. It makes at most one accept and no random-oracle query (`relay_budget`). Whenever decapsulation is correct, either the Beacon never accepts, or the Server's session 0 derives its root from the same 192-byte input as the Beacon (`server_input_eq`), the Server's sequence-one send material equals the Beacon's sequence-one receive material (`material_agree`), the Beacon accepts exactly the key ID, payload and associated data that session 0 sealed, and session 0 is the only partner, so none of the winning disjuncts `W1`, `W2` and `W3` holds (`relay_after_accept`). The bound cannot be zero from these premises alone, because with a wrong decapsulation the Beacon derives another root and the abstract AEAD has no law that stops a wrong key from opening.

Relay liveness. `relay_live` states that, with the checks `acceptAll` that accept everything, a nonempty payload short enough for the writers and the Server's allocation, and a Server key ID below the maximum, the honest relay makes the Beacon accept with probability at least one minus the KEM correctness error. Its main new ingredient is `build_publishes`, the converse of `build_published`: under these conditions every run of the Server's build publishes a Phase 2, because the key-ID counter advances, the commit preparation sees the Server's own binding and an available key ID, the sequence-one seal produces a frame (`seal_written`, `tail_seal_written`, `send_written`) and the Phase 2 writer succeeds. `relay_after_accept` then shows that the Beacon accepts whenever the build publishes and decapsulation is correct. Without this lemma, a B4a regression in which the accept or the build never publishes would pass both earlier controls.

Proof method. All results evaluate the experiment exactly along the honest path. `body_run` unfolds `gameState` under the Extract random oracle into the sampled Beacon identity seed and one-time scalar, the ML-KEM key generation, the deterministic Phase 1 (`phase1Run_eq`) and the adversary's run (`runAdversary`), for every Server seed and prekey scalar. The only probabilistic failure is the KEM: `kem_split` bounds an event by the per-key-pair decapsulation error `keyPairError` at the point of the encapsulation, `keyPairError_average` shows that averaging this error over key generation gives `kemError`, through `PqxdhKemCorrectnessError.error_probability`, and `kem_lower` turns such a bound on a missed event into the lower bound of the negative control and of the liveness statement. On the Beacon's side, `beacon_prepare` evaluates the Phase 2 prefix on honest fields, `beacon_receive`, `beacon_open` and `beacon_raw` show through the ratchet refinement that the extracted ratchet's sequence-one receive opens an honestly sealed record whose commitment is cached, `beacon_afterRoot` stages the payload through `PqxdhPhase2LocalMatching.afterOpening_of_binding` of stage B9a, and `beacon_finish` evaluates the whole finish oracle to an acceptance once the table and the commitment cache hold the honest values. On the Server's side, `serverPrefix_eq` evaluates the Phase 1 prefix for every outcome of the admission checks, `acceptAfter_honest` the rest of the accept, `tail_seal` and `tail_send` the sequence-one seal, and `build_published` and `build_publishes` the build.

Premises. All three results assume `PqxdhChallengeSecretRouting.FunctionalDecapsulation` of the ML-KEM scheme, the existing functional contract that decapsulation is a deterministic function, so that the Beacon's decapsulation in the game is the one that the KEM correctness error measures and the KEM error is the only failure. `RelayLaws` collects the other premises of the relay control. `PqxdhServerAuthAssumptions.NonzeroHonestDh` is the approved functional contract that honest X25519 outputs are never all-zero; it makes the Beacon's and the Server's local nonzero tests pass on honest keys. `RawCtxSourcePublication.BodyLength` is the existing ChaCha20-Poly1305 functional contract that a sealed body has the plaintext's length; it is needed because the Beacon's frame validation requires a record longer than the 80 bytes of tag and commitment, that is a nonempty body, and `Pqxdh.Crypto` alone does not guarantee this. `Phase1ReadBack`, `Phase2ReadBack` and `FrameReadBack` state that what the writers produce, the readers parse back. `ControlLaws setup codec limit` adds writer success on bounded messages: the Phase 1 writer succeeds on every candidate, whose fields all have fixed sizes, so that the Beacon always publishes; the frame writer succeeds on every frame whose protected payload is shorter than `limit`; and the Phase 2 writer succeeds on every Phase 2 whose application ciphertext is the frame writer's output on such a frame. A size-bounded writer, such as one that respects the Data limit `RawCtxSourcePublication.dataLimit`, satisfies these laws for a small enough `limit`. The negative control also needs a nonempty payload with `payload.length + 88 < limit`, so that its sealed body is nonempty and its record, 88 bytes longer than the payload, can be written; the relay control needs no condition on the payload, because a published build already carries a nonempty plaintext. The liveness statement needs the accepting checks, the payload conditions `8 + length ≤ Usize.max` (the Server's own allocation guard) and `length + 88 < limit`, and a Server key ID below the maximum, because the Server's key-ID counter starts at its own key ID. No hardness assumption is used, no premise constrains `Checks` in the two controls, because the control adversary does not query the Server and the relay delivers a Phase 2 only when the Server produces one, and `PqxdhServerAuthAssumptions.X25519ClassLaw` is not needed.

Scope and trust boundary. As in B4a, messages are abstract byte strings read and written by the free functions of `Codec`. The read-back and writer-success laws are abstract message-model premises, not facts about Cap'n Proto, and no libsodium internal is used; the primitives enter only through the functional contracts named above and the random oracles of the experiment. A concrete instance on which all premises hold with zero KEM error is left to stage B5b, because it needs the toy primitives of the module PqxdhHypothesisWitness, whose import would add the authenticated-root proof chain to this module and to every later stage that imports it. The axioms used are `propext`, `Classical.choice` and `Quot.sound` only.

Differences from the stage design. The design's single `ControlLaws`, which included honest admission checks and writer totality restricted to honest fields, is split into `RelayLaws` and `ControlLaws`, the admission-check premise is dropped from the two controls because it is not needed, writer success is stated for messages below a size bound `limit`, and `PqxdhChallengeSecretRouting.FunctionalDecapsulation` is a separate argument because it carries data. The control adversary takes no `Checks` argument, and `relay_not_win` has no nonempty-payload premise. `RawCtxSourcePublication.BodyLength` is added as explained above, and `relay_live` is added at review. The control adversary reads the Beacon's keys without verifying signatures, uses the key ID 0 and forms the Beacon's associated data and material through the public expressions `PqxdhBeaconPhase2Shared.associatedData` and `beaconMaterial` rather than by running a local copy of the Server. `acceptAfter` is a local copy of the continuation of `acceptOracle` after its Phase 1 prefix, tied to it by `rfl` in `run_accept`. The design's `ctx_seal_open` and `honest_session_accepted` are not stated as separate theorems: the CTX seal and open completeness is `tail_seal` with `beacon_open`, and the honest session's acceptance is part of `relay_after_accept`. The design's `IsServerQuery` is local to this module, because B4a splits the Server's method into accept and build queries.
-/

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RepresentationBridge (absMaterial)
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge zeroDh sourceScalarDh)
open PqxdhJointDhExtractRoot (RootSpec)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhEd25519EufCma (Ed25519PublicKey Phase1Candidate Phase1KeyTuple)
open PqxdhRootTableInitialization (rootArray)
open PqxdhPhase2GapDhSource (peer)
open PqxdhServerAuthExperiment (Setup Codec Checks Adversary gameState body phase1Run Win W1 W2 W3 Ghost GameState
  liftCoins rom_coins acceptOracle)
open PqxdhServerAuthExperiment renaming ServerAuthSpec → ExpSpec, authHandler → expHandler,
  serverAuthGame → expGame, ServerAuthQuery → ExpQuery, AuthInput → Input, familyCoins → coins,
  initialGameState → initial

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ## Premises -/

/-- Abstract message-model law for Phase 1: whatever the Phase 1 writer produces, the Phase 1 reader parses back, and the getters return the written identity key, ML-KEM key, prekey and one-time key. It is a premise about the abstract codec, not a fact about Cap'n Proto. -/
def Phase1ReadBack (codec : Codec Reader Response) : Prop :=
  ∀ candidate bytes, codec.write1 candidate = some bytes →
    ∃ reader, codec.read1 bytes = some reader ∧ codec.identity reader = some candidate.identityKey ∧
      codec.pqField reader = some candidate.pqKey ∧ codec.preField reader = some candidate.preKey ∧
      codec.oneField reader = some candidate.oneTimeKey

/-- Abstract message-model law for Phase 2: whatever the Phase 2 writer produces, the Phase 2 reader parses back, and the getters return the written KEM ciphertext, ephemeral key, Server identity, assigned key ID and application ciphertext. It is a premise about the abstract codec, not a fact about Cap'n Proto. -/
def Phase2ReadBack (codec : Codec Reader Response) : Prop :=
  ∀ fields bytes, codec.write2 fields = some bytes →
    ∃ response, codec.read2 bytes = some response ∧
      codec.ciphertext response = some fields.kemCiphertext ∧
      codec.ephemeral response = some fields.ephemeral ∧
      codec.serverIdentity response = some fields.identity ∧
      codec.assignedId response = fields.keyId ∧
      codec.application response = some fields.appCiphertext

/-- Abstract message-model law for record frames: a frame the writer produces is a nonempty byte string that the frame reader parses back to the same frame. It is a premise about the abstract codec, not a fact about Cap'n Proto. -/
def FrameReadBack (codec : Codec Reader Response) : Prop :=
  ∀ frame bytes, codec.frameWrite frame = some bytes → bytes ≠ [] ∧ codec.frameRead bytes = some frame

/-- The functional and message-model laws the honest relay needs: honest X25519 outputs are never all-zero (`PqxdhServerAuthAssumptions.NonzeroHonestDh`, approved for the negative controls), ChaCha20-Poly1305 bodies have the plaintext's length (the existing contract `RawCtxSourcePublication.BodyLength`), and the Phase 1, Phase 2 and frame writers read back under their readers. None is a security law; each is an abstract property of the primitives or of the message model. -/
structure RelayLaws (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) : Prop where
  nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto
  bodyLength : RawCtxSourcePublication.BodyLength setup.source.crypto
  phase1 : Phase1ReadBack codec
  phase2 : Phase2ReadBack codec
  frame : FrameReadBack codec

/-- The laws of the negative control and of the relay's liveness: the relay's laws together with writer success on bounded messages, so that the Beacon always publishes its Phase 1 and a sender can always frame and answer a record whose protected payload is shorter than `limit`. The Phase 1 writer succeeds on every candidate, whose fields all have fixed sizes; the frame writer succeeds on every frame whose payload is shorter than `limit`; and the Phase 2 writer succeeds on every Phase 2 whose application ciphertext is the frame writer's output on such a frame. A size-bounded writer satisfies these laws for a small enough `limit`. -/
structure ControlLaws (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat) : Prop
    extends RelayLaws setup codec where
  phase1Total : ∀ candidate, ∃ bytes, codec.write1 candidate = some bytes
  frameBounded : ∀ frame : RawCtxReceive.DecodedFrame, frame.payload.length < limit →
    ∃ bytes, codec.frameWrite frame = some bytes
  phase2Bounded : ∀ (frame : RawCtxReceive.DecodedFrame) (frameBytes : Pqxdh.Bytes), frame.payload.length < limit →
    codec.frameWrite frame = some frameBytes → ∀ keyId ephemeral identity kemCiphertext,
      ∃ bytes, codec.write2 ⟨keyId, ephemeral, identity, kemCiphertext, frameBytes⟩ = some bytes

/-- Under the control laws, the frame writer answers every frame whose payload is shorter than the bound. -/
theorem frame_written {setup : Setup baseSpec KemSK} {codec : Codec Reader Response} {limit : Nat}
    (laws : ControlLaws setup codec limit) (frame : RawCtxReceive.DecodedFrame) (short : frame.payload.length < limit) :
    codec.frameWrite frame ≠ none := by
  obtain ⟨_, written⟩ := laws.frameBounded frame short
  rw [written]
  exact Option.some_ne_none _

/-- Under the control laws, the Phase 2 writer answers every Phase 2 whose application ciphertext is the frame writer's output on a frame whose payload is shorter than the bound. -/
theorem phase2_written {setup : Setup baseSpec KemSK} {codec : Codec Reader Response} {limit : Nat}
    (laws : ControlLaws setup codec limit) (frame : RawCtxReceive.DecodedFrame) (frameBytes : Pqxdh.Bytes)
    (short : frame.payload.length < limit) (framed : codec.frameWrite frame = some frameBytes)
    (keyId : Std.U64) (ephemeral identity : Word32) (kemCiphertext : Ciphertext) :
    codec.write2 ⟨keyId, ephemeral, identity, kemCiphertext, frameBytes⟩ ≠ none := by
  obtain ⟨_, written⟩ := laws.phase2Bounded frame frameBytes short framed keyId ephemeral identity kemCiphertext
  rw [written]
  exact Option.some_ne_none _

/-- A sealed record's protected payload, the AEAD body and tag followed by the 64-byte commitment, is 80 bytes longer than its plaintext. -/
theorem protected_length (c : Pqxdh.Crypto) (lengths : RawCtxSourcePublication.BodyLength c)
    (key nonce ad plaintext : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest) :
    ((c.aeadSeal key nonce ad plaintext).1 ++ (c.aeadSeal key nonce ad plaintext).2 ++ digest.toList).length =
      plaintext.length + 80 := by
  simp only [List.length_append, lengths key nonce ad plaintext, c.aeadSeal_tag_length, List.Vector.toList_length]

set_option linter.deprecated false in
/-- The KEM correctness error of the experiment's ML-KEM: the probability, under the experiment's ambient coins, that a fresh key pair fails to decapsulate a fresh encapsulation to itself. -/
noncomputable def kemError (setup : Setup baseSpec KemSK) : ℝ :=
  (Pr[= true | simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
    (PqxdhKemCorrectnessError.errorExperiment setup.kem)]).toReal

/-! ## The honest relay -/

/-- The honest relay's last step: deliver the Server's Phase 2, if any, to the target Beacon's finish. -/
def relayFinish (response : Option PqxdhServerRegistrationPublication.Response) : OracleComp ExpSpec Unit :=
  match response with
  | none => pure ()
  | some response => do
      let _ ← (ExpSpec.query (.inr (.finish response.serialized)) : OracleComp ExpSpec (Option Pqxdh.Bytes))
      pure ()

/-- The honest relay's middle step: build the accepted session, if any, with the payload. -/
def relayBuild (payload : Option Pqxdh.Bytes) (session : Option Nat) : OracleComp ExpSpec Unit :=
  match session with
  | none => pure ()
  | some session =>
      (ExpSpec.query (.inr (.build session payload)) :
        OracleComp ExpSpec (Option PqxdhServerRegistrationPublication.Response)) >>= relayFinish

/-- Honest relay: the target Beacon's Phase 1 is accepted by the Server, the accepted session is built with the payload, and the Server's Phase 2 is delivered to the Beacon's finish; nothing else is queried. -/
def relayAdversary (payload : Option Pqxdh.Bytes) : Adversary := fun input =>
  match input.phase1 with
  | none => pure ()
  | some phase1 => (ExpSpec.query (.inr (.accept phase1)) : OracleComp ExpSpec (Option Nat)) >>= relayBuild payload

/-! ## The target Beacon's Phase 1 -/

open PqxdhServerAuthExperiment (projection phase1Impl freshBeacon binding) in
/-- The target Beacon's Phase 1 candidate: its Ed25519 identity, the public prekey, one-time and ML-KEM keys, and its signatures on the three keys. -/
def beaconCandidate (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) : Phase1Candidate :=
  PqxdhJointPhase1SourceWriter.candidate (setup.joint.publicKeys beaconSeed).ed25519
    ⟨publicValue.prekey, setup.dh.publicKey oneTime, kemPk⟩
    (setup.joint.sign beaconSeed (PqxdhEd25519EufCma.prekeyMessage publicValue.prekey))
    (setup.joint.sign beaconSeed (PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey oneTime)))
    (setup.joint.sign beaconSeed (PqxdhEd25519EufCma.pqMessage kemPk))

open PqxdhServerAuthExperiment (projection phase1Impl freshBeacon binding) in
/-- The target Beacon's lifecycle state after it has published its Phase 1: it waits for Phase 2 with its one-time scalar and ML-KEM secret key. -/
def publishedBeacon (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (oneTime : ScalarBytes) (kemSk : KemSK) : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK :=
  PqxdhBeaconPhase1Publication.publish
    (PqxdhLivePhase1Bundle.identityArray (setup.joint.publicKeys beaconSeed).ed25519)
    ⟨⟨binding setup publicValue⟩, .inl (), .inr oneTime, kemSk⟩ (freshBeacon setup publicValue kemSk)

open PqxdhServerAuthExperiment (projection phase1Impl freshBeacon binding) in
/-- The Beacon's Phase 1 writing step under the experiment's Phase 1 handler is the codec's writer followed by the deterministic choice of the published or unchanged Beacon state. -/
theorem writing_eq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (publicValue : PublicChallenge) (oneTime : ScalarBytes) (kemSk : KemSK)
    (candidate : Phase1Candidate) :
    simulateQ (phase1Impl setup codec beaconSeed oneTime) (PqxdhLivePhase1Bundle.writing
      (PqxdhLivePhase1Bundle.identityArray (setup.joint.publicKeys beaconSeed).ed25519) candidate
      (some (.inr oneTime)) (freshBeacon setup publicValue kemSk)) =
      (pure (codec.write1 candidate) : ProbComp _) >>= fun w =>
        pure (match w with
        | none => (none, freshBeacon setup publicValue kemSk)
        | some bytes => (some bytes, publishedBeacon setup publicValue beaconSeed oneTime kemSk)) := by
  simp only [PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning,
    PqxdhBeaconPhase1Publication.prepare, freshBeacon, Option.map_some, simulateQ_bind, simulateQ_spec_query]
  refine bind_congr fun w => ?_
  cases w <;> rfl

open PqxdhServerAuthExperiment (projection phase1Impl freshBeacon binding) in
/-- The experiment's Phase 1 run is the writing step on the target Beacon's candidate. -/
theorem phase1Run_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk =
      simulateQ (phase1Impl setup codec beaconSeed oneTime) (PqxdhLivePhase1Bundle.writing
      (PqxdhLivePhase1Bundle.identityArray (setup.joint.publicKeys beaconSeed).ed25519)
      (beaconCandidate setup publicValue beaconSeed oneTime kemPk)
      (some (.inr oneTime)) (freshBeacon setup publicValue kemSk)) := by
  simp only [phase1Run, PqxdhLivePhase1Bundle.bundle, freshBeacon, simulateQ_bind, simulateQ_spec_query]
  change (pure (some (Sum.inr oneTime)) : ProbComp _) >>= _ = _
  rw [pure_bind]
  simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_some,
    simulateQ_bind]
  rfl

open PqxdhServerAuthExperiment (projection phase1Impl freshBeacon binding) in
/-- The experiment's Phase 1 run is deterministic: it returns the written bytes and the published Beacon when the writer succeeds, and nothing with the fresh Beacon otherwise. -/
theorem phase1Run_eq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk =
      pure (match codec.write1 (beaconCandidate setup publicValue beaconSeed oneTime kemPk) with
        | none => (none, freshBeacon setup publicValue kemSk)
        | some bytes => (some bytes, publishedBeacon setup publicValue beaconSeed oneTime kemSk)) := by
  rw [phase1Run_bind, writing_eq, pure_bind]

/-- A lifted pure computation is pure. -/
theorem lift_pure_state {σ α : Type} (value : α) : (StateT.lift (pure value) : StateT σ ProbComp α) = pure value := by
  funext state
  simp [StateT.lift]
  rfl

/-! ## The Beacon's Phase 2 prefix -/

/-- The Beacon's DH2: its converted identity secret with the Server's ephemeral public key. -/
def beaconSecond (setup : Setup baseSpec KemSK) (beaconSeed : IdentitySeed) (e : ScalarBytes) : DhOutput :=
  ⟨setup.source.crypto.x25519 (setup.source.crypto.xsk (setup.secretOfSeed beaconSeed).toList)
    (setup.source.crypto.xpub e.toList), setup.source.crypto.x25519_length _ _⟩

/-- The Beacon's DH4: its one-time secret with the Server's ephemeral public key. -/
def beaconFourth (setup : Setup baseSpec KemSK) (oneTime e : ScalarBytes) : DhOutput :=
  ⟨setup.source.crypto.x25519 oneTime.toList (setup.source.crypto.xpub e.toList),
    setup.source.crypto.x25519_length _ _⟩

/-- The inputs the Beacon collects from an honest Phase 2: the parsed response, the KEM ciphertext, the Server's ephemeral and identity keys, the assigned key ID, the four DH values and the KEM secret. -/
def beaconCollected (setup : Setup baseSpec KemSK) (seed beaconSeed : IdentitySeed) (oneTime e : ScalarBytes)
    (response : Response) (ciphertext : Ciphertext) (keyId : Std.U64) (secret : PqxdhKemIndCca.MlKemSharedSecret) :
    PqxdhPhase2GapDhSource.Inputs Response :=
  ⟨response, ciphertext, rootArray (setup.dh.publicKey e), rootArray (setup.joint.publicKeys seed).ed25519,
    rootArray (setup.joint.publicKeys seed).convertedX25519, keyId,
    .selected (peer (rootArray (setup.joint.publicKeys seed).convertedX25519)),
    rootArray (beaconSecond setup beaconSeed e), .selected (peer (rootArray (setup.dh.publicKey e))),
    rootArray (beaconFourth setup oneTime e), rootArray secret⟩

/-- Reading a root array back as a peer encoding gives the original 32 bytes. -/
theorem peer_rootArray (value : List.Vector UInt8 32) : peer (rootArray value) = value := by
  apply List.Vector.toList_injective
  exact PqxdhRootTableInitialization.rootArray_bytes value

/-- The source's scalar DH is present when its X25519 output is nonzero. -/
theorem sourceScalarDh_some (c : Pqxdh.Crypto) (scalar : ScalarBytes) (point : PeerEncoding)
    (nonzero : c.x25519 scalar.toList point.toList ≠ Pqxdh.zero32) :
    sourceScalarDh c scalar point = some ⟨c.x25519 scalar.toList point.toList, c.x25519_length _ _⟩ := by
  simp [sourceScalarDh, nonzero]

/-- The source's converted-static DH reply is present when its X25519 output is nonzero. -/
theorem dhReply_of_nonzero (c : Pqxdh.Crypto) (secret : Pqxdh.Bytes) (point : PeerEncoding)
    (nonzero : c.x25519 (c.xsk secret) point.toList ≠ Pqxdh.zero32) :
    sourceDhReply c secret point = some ⟨c.x25519 (c.xsk secret) point.toList, c.x25519_length _ _⟩ := by
  simp [sourceDhReply, nonzero]

/-- The public conversion of the pinned Server identity. -/
theorem server_conversion (setup : Setup baseSpec KemSK) (seed : IdentitySeed) :
    (setup.source.crypto.xpkConv (absBytes (rootArray (setup.joint.publicKeys seed).ed25519))).bind
      PqxdhServerAuthExperiment.toWord32 = some (rootArray (setup.joint.publicKeys seed).convertedX25519) := by
  rw [PqxdhRootTableInitialization.rootArray_bytes,
    jointPublic_conversion setup.source.crypto setup.joint setup.secretOfSeed setup.wiring seed]
  simp [PqxdhServerAuthExperiment.toWord32]

/-- An honestly generated X25519 public key is accepted by the Beacon's public domain. -/
theorem accepts_public (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (e : ScalarBytes) :
    setup.beaconDomain.accepts (setup.dh.publicKey e) = true := by
  rw [← setup.beaconDomain.available e]
  show (sourceScalarDh setup.source.crypto e (setup.dh.publicKey e)).isSome = true
  rw [sourceScalarDh_some _ _ _ (by exact nonzero _ _)]
  rfl

/-- The pinned Server's converted identity is accepted by the Beacon's public domain. -/
theorem accepts_server (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (seed : IdentitySeed)
    (e : ScalarBytes) :
    setup.beaconDomain.accepts (setup.joint.publicKeys seed).convertedX25519 = true := by
  rw [← setup.beaconDomain.available e]
  change (sourceScalarDh setup.source.crypto e (setup.joint.publicKeys seed).convertedX25519).isSome = true
  have converted := setup.wiring.xPublic seed
  rw [sourceScalarDh_some _ _ _ (by rw [converted]; exact nonzero _ _)]
  rfl

/-- The Beacon's DH2 with an honest ephemeral. -/
theorem beacon_staticDh_some (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (beaconSeed : IdentitySeed)
    (e : ScalarBytes) :
    setup.joint.staticDh beaconSeed (setup.dh.publicKey e) = some (beaconSecond setup beaconSeed e) := by
  rw [setup.wiring.staticDh, dhReply_of_nonzero _ _ _ (by exact nonzero _ _)]
  rfl

/-- The Beacon's DH4 with an honest ephemeral. -/
theorem beacon_oneTimeDh_some (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (oneTime e : ScalarBytes) :
    sourceScalarDh setup.source.crypto oneTime (setup.dh.publicKey e) = some (beaconFourth setup oneTime e) := by
  rw [sourceScalarDh_some _ _ _ (by exact nonzero _ _)]
  rfl

/-- The Beacon's metadata admission of the honest collected inputs. -/
theorem beacon_admitted (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto)
    (seed beaconSeed : IdentitySeed) (oneTime e : ScalarBytes) (response : Response) (ciphertext : Ciphertext)
    (keyId : Std.U64) (secret : PqxdhKemIndCca.MlKemSharedSecret) (control : pqxdh.BeaconInitSent)
    (hpin : absBytes control.expected_server_binding.identity_public_key =
      (setup.joint.publicKeys seed).ed25519.toList) :
    PqxdhPhase2DhMetadata.admitted control
        (beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret) =
      some ⟨control.expected_server_binding, keyId, PqxdhBeaconPhase2Shared.associatedData control⟩ := by
  have known : PqxdhPhase2DhMetadata.knownNonzero
      (beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret) := by
    refine ⟨?_, ?_⟩
    · rw [beaconCollected, PqxdhRootTableInitialization.rootArray_bytes]
      exact nonzero _ _
    · rw [beaconCollected, PqxdhRootTableInitialization.rootArray_bytes]
      exact nonzero _ _
  have pinned : absBytes control.expected_server_binding.identity_public_key =
      absBytes (beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret).server := by
    rw [hpin, beaconCollected, PqxdhRootTableInitialization.rootArray_bytes]
  simp only [PqxdhPhase2DhMetadata.admitted, pinned, known, ite_true]
  rfl

/-- The Beacon's Phase 2 prefix on an honest Phase 2 whose fields read back and whose KEM ciphertext decapsulates collects the honest inputs and admits them with the pinned binding, the assigned key ID and the Beacon's associated data. -/
theorem beacon_prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto)
    (seed beaconSeed : IdentitySeed) (oneTime e : ScalarBytes) (kemSk : KemSK) (raw : Pqxdh.Bytes)
    (response : Response) (ciphertext : Ciphertext) (keyId : Std.U64) (secret : PqxdhKemIndCca.MlKemSharedSecret)
    (control : pqxdh.BeaconInitSent)
    (hread : codec.read2 raw = some response) (hct : codec.ciphertext response = some ciphertext)
    (heph : codec.ephemeral response = some (rootArray (setup.dh.publicKey e)))
    (hsid : codec.serverIdentity response = some (rootArray (setup.joint.publicKeys seed).ed25519))
    (hid : codec.assignedId response = keyId)
    (hdecap : functional.result kemSk (PqxdhPhase2InputBytes.ciphertext ciphertext) = some secret)
    (hpin : absBytes control.expected_server_binding.identity_public_key =
      (setup.joint.publicKeys seed).ed25519.toList)
    :
    (PqxdhServerAuthExperiment.beaconPrefix setup codec beaconSeed control () (.inr oneTime) kemSk raw).run () =
      pure (some ⟨beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret,
        ⟨control.expected_server_binding, keyId, PqxdhBeaconPhase2Shared.associatedData control⟩⟩, ()) := by
  simp only [PqxdhPhase2DhMetadata.prepare, PqxdhPhase2GapDhSource.collect, OptionT.run_bind,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, simulateQ_map, PqxdhServerAuthExperiment.beaconPrefix,
    PqxdhPhase2GapDhSource.prefixImpl, PqxdhServerAuthExperiment.beaconAuxUnit, PqxdhServerAuthExperiment.beaconAux,
    lift_pure_state, hread, hct, heph, hsid, hid, bind_assoc, pure_bind,
    Option.elim_some, functional.exact, hdecap, map_pure, Option.map_some, server_conversion, PqxdhPhase2GapDhSource.selectedReply,
    accepts_server setup nonzero seed e, accepts_public setup nonzero e, ite_true, peer_rootArray,
    beacon_staticDh_some setup nonzero, beacon_oneTimeDh_some setup nonzero]
  have admitted := beacon_admitted setup nonzero seed beaconSeed oneTime e response ciphertext keyId secret
    control hpin
  simp only [beaconCollected, peer_rootArray] at admitted
  simp only [Option.bind_some, admitted, Option.map_some, StateT.run_pure, beaconCollected, peer_rootArray]

/-! ## The Beacon's receive, opening and finish -/

open ratchet.concrete in
/-- The Beacon's initial kernel at a root word. -/
noncomputable def beaconKernel (c : Pqxdh.Crypto) (root : Word32) : ConcreteRatchetKernel :=
  PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root)
    (RawCtxSourceHkdf.initialResponse c (PqxdhInitialRatchetComplementarity.beaconPending root).request)

/-- The KDF interpreter of the fixed source crypto, used to read the extracted ratchet. -/
def sourceKdf (c : Pqxdh.Crypto) : ratchet.concrete.KdfInterpreter := RawCtxSourceHkdf.response c

/-- The model crypto used to read the extracted ratchet. -/
noncomputable def modelCrypto (c : Pqxdh.Crypto) :
    Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial Unit Unit Unit :=
  ratchet.concrete.withInterpreter PqxdhServerAuthExperiment.unitRatchet (sourceKdf c)

/-- The sequence-one message material of a ratchet chain under the source KDF. -/
noncomputable def chainMaterial (c : Pqxdh.Crypto) (chain : ratchet.RatchetChain) : ratchet.RatchetMaterial :=
  (ratchet.concrete.interpretedStep (sourceKdf c) chain).material

/-- The Beacon kernel is the extracted Beacon initialization. -/
theorem beaconKernel_run (source : FixedHkdfSha512NoSaltSource) (root : Word32) :
    PqxdhRootTableInitialization.initialKernelRun source true (PqxdhPhase2InputBytes.word root) =
      ok (beaconKernel source.crypto root) := by
  simp only [PqxdhRootTableInitialization.initialKernelRun, ↓reduceIte, PqxdhPhase2InputBytes.word_roundtrip,
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon_eq]
  exact PqxdhBeaconPhase2Publication.normalInitial_exact _ _

open ratchet.concrete in
/-- The Beacon's sequence-one receive requests one KDF derivation and then opens with the chain material. -/
theorem beacon_receive (source : FixedHkdfSha512NoSaltSource) (root : Word32) {Context : Type}
    (context : Context) :
    ∃ pending opened, RawCtxOwnerOracle.begin (beaconKernel source.crypto root) 1#u64 context =
        .ReceiveKdfRequested pending ∧
      RawCtxOwnerOracle.resume pending (sourceKdf source.crypto pending.request) = .ReceiveOpenRequested opened ∧
      opened.material = ok (.Some (chainMaterial source.crypto (beaconKernel source.crypto root).refined.receive_chain)) ∧
      opened.sequence = ok 1#u64 ∧ opened.context = context := by
  obtain ⟨kernel, run, _, _, refines⟩ := PqxdhRootTableInitialization.initialize_refines source
    (modelCrypto source.crypto) true (PqxdhPhase2InputBytes.word root)
  rw [beaconKernel_run] at run
  cases RustM.ok.inj run
  have lengthZero : (beaconKernel source.crypto root).refined.control.receive_cache.len.val = 0 := by
    simpa only [ratchet.control.cacheSeqs_length, List.length_map, List.length_nil] using
      refines.receiveControl.cache.length_eq
  obtain ⟨pending, opened, begun, trace, openRefines⟩ := KernelRefines.begin_receive_future_trace
    PqxdhServerAuthExperiment.unitRatchet (sourceKdf source.crypto) _ _ _ _ context 1#u64 refines
    (by simp) (by rw [lengthZero]; simp)
  have hbegin : RawCtxOwnerOracle.begin (beaconKernel source.crypto root) 1#u64 context =
      .ReceiveKdfRequested pending :=
    RustM.ok.inj ((RawCtxOwnerOracle.begin_exact _ _ _).symm.trans begun)
  have hresume : RawCtxOwnerOracle.resume pending (sourceKdf source.crypto pending.request) =
      .ReceiveOpenRequested opened := by
    cases trace with
    | step p next f count resumed tail =>
        cases tail
        exact RustM.ok.inj ((RawCtxOwnerOracle.resume_exact _ _).symm.trans resumed)
  obtain ⟨future, _, hcontext, hprepared, frefines⟩ := openRefines
  refine ⟨pending, opened, hbegin, hresume, ?_, ?_, hcontext⟩
  · rcases opened with ⟨entry, openedContext, prepared⟩
    simp only at hprepared
    subst hprepared
    rw [ReceiveOpen.future_material_exact, frefines.targetMaterial]
    rfl
  · rcases opened with ⟨entry, openedContext, prepared⟩
    simp only at hprepared
    subst hprepared
    rw [ReceiveOpen.future_sequence_exact, frefines.targetSequence]

/-- The Beacon's native tail under the tail adapter. -/
noncomputable def beaconTail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response)
      (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp) :=
  PqxdhServerAuthExperiment.beaconNative setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter

/-- A protected payload of body, 16-byte tag and 64-byte commitment has its three slices. -/
theorem fromPayload_honest (body tag commitment : Pqxdh.Bytes) (nonempty : body ≠ []) (htag : tag.length = 16)
    (hcommit : commitment.length = 64) :
    RawCtxFrameDecoding.fromPayload (body ++ tag ++ commitment) = some ⟨body ++ tag, tag, commitment⟩ := by
  have positive : 0 < body.length := List.length_pos_iff.mpr nonempty
  unfold RawCtxFrameDecoding.fromPayload
  have hlen : (body ++ tag ++ commitment).length = body.length + 16 + 64 := by
    simp [htag, hcommit]
  split_ifs with short
  · exfalso
    rw [hlen] at short
    omega
  simp only [hlen, Option.some.injEq]
  have base : (body ++ tag ++ commitment).take (body.length + 16 + 64 - 64) = body ++ tag := by
    rw [show body.length + 16 + 64 - 64 = (body ++ tag).length by simp [htag]]
    exact List.take_left' rfl
  have commit : (body ++ tag ++ commitment).drop (body.length + 16 + 64 - 64) = commitment := by
    rw [show body.length + 16 + 64 - 64 = (body ++ tag).length by simp [htag]]
    exact List.drop_left' rfl
  rw [base, commit]
  congr 1
  rw [show (body ++ tag).length - 16 = body.length by simp [htag]]
  exact List.drop_left' rfl

/-- A cached commitment query of the shared native primitives returns the cached digest. -/
theorem native_hash_hit {A : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (bytes : Pqxdh.Bytes) (auxiliary : A) (cache : CtxRomAuth.CtxRO.QueryCache) (digest : CtxRomAuth.CtxDigest)
    (hit : cache ((), bytes) = some digest) :
    (RawCtxSharedPrimitive.nativeImpl c kdf (.inr (.inl bytes))).run (auxiliary, cache) =
      pure (some digest.toList, (auxiliary, cache)) := by
  change (RawCtxSharedPrimitive.openingImpl c (.inl bytes)).run (auxiliary, cache) = _
  simp only [RawCtxSharedPrimitive.openingImpl, StateT.run]
  rw [show CtxRomAuth.ctxRandomOracle ((), bytes) cache = pure (digest, cache) from
    QueryImpl.withCaching_run_some _ hit]
  simp

/-- A base opening of the shared native primitives is the functional opening. -/
theorem native_base {A : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (input : RawCtxSourceOpen.BaseInput) (state : RawCtxSharedPrimitive.SharedState A) :
    (RawCtxSharedPrimitive.nativeImpl c kdf (.inr (.inr input))).run state =
      pure (RawCtxSourceOpen.baseOpen c input, state) :=
  rfl

/-- The Beacon's CTX opening of an honestly sealed record whose commitment is cached. -/
theorem beacon_open (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : RawCtxWholeOwner.OpenInput) (body tag plaintext : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (hpayload : input.context.frame.payload = body ++ tag ++ digest.toList) (hbody : body ≠ [])
    (had : input.context.associatedData.length = 153)
    (hseal : setup.source.crypto.aeadSeal (absMaterial input.material).1 (absMaterial input.material).2
      input.context.associatedData plaintext = (body, tag))
    (hcache : cache ((), Pqxdh.ctxPreimage (absMaterial input.material)
      ⟨input.context.associatedData, input.sequence.val, input.context.frame.sender.val⟩ tag) = some digest) :
    (beaconTail setup codec (.inl (.inr input))).run ((), cache) = pure (.Some plaintext, ((), cache)) := by
  have htag : tag.length = 16 := by
    have := setup.source.crypto.aeadSeal_tag_length (absMaterial input.material).1 (absMaterial input.material).2
      input.context.associatedData plaintext
    rw [hseal] at this
    exact this
  have hslices := fromPayload_honest body tag digest.toList hbody htag (by simp)
  simp only [beaconTail, QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeTailAdapter,
    RawCtxSourceOpen.nativeAdapter, RawCtxSourceOpen.openInput, hpayload, hslices, had, ite_true,
    RawCtxSourceOpen.openSlices, simulateQ_bind, simulateQ_spec_query, RawCtxSourceOpen.openLift,
    PqxdhBeaconPhase2Publication.nativeRawLift, PqxdhServerAuthExperiment.beaconNative, StateT.run_bind]
  rw [native_hash_hit _ _ (RawCtxSourceOpen.hashInput input ⟨body ++ tag, tag, digest.toList⟩) _ _ _ hcache]
  simp only [pure_bind, ite_true, simulateQ_spec_query, RawCtxSourceOpen.openLift,
    PqxdhBeaconPhase2Publication.nativeRawLift, PqxdhServerAuthExperiment.beaconNative]
  have opened := setup.source.crypto.aead_open_seal (absMaterial input.material).1 (absMaterial input.material).2
    input.context.associatedData plaintext
  rw [hseal] at opened
  rw [native_base]
  simp only [RawCtxSourceOpen.baseInput, RawCtxSourceOpen.baseOpen_combined _ _ _ _ _ _ htag, opened]

/-- The opening arguments of a capability with present material. -/
theorem arguments_of (opened : ratchet.concrete.ReceiveOpen RawCtxWholeOwner.OpenContext)
    (material : ratchet.RatchetMaterial) (sequence : Std.U64)
    (hmaterial : opened.material = ok (.Some material)) (hsequence : opened.sequence = ok sequence) :
    RawCtxWholeOwner.arguments opened = some ⟨material, sequence, opened.context⟩ := by
  have hchoose := RustM.ok.inj (opened.material_total.choose_spec.symm.trans hmaterial)
  have hseq := RustM.ok.inj (opened.sequence_total.choose_spec.symm.trans hsequence)
  simp only [RawCtxWholeOwner.arguments, hchoose, hseq]

/-- The Beacon's sequence-one material at a root word. -/
noncomputable def beaconMaterial (c : Pqxdh.Crypto) (root : Word32) : ratchet.RatchetMaterial :=
  chainMaterial c (beaconKernel c root).refined.receive_chain

/-- The Beacon's raw receive of an honestly sealed sequence-one record opens its plaintext. -/
theorem beacon_raw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (root : Word32)
    (candidate : pqxdh.BeaconRegistrationCandidate) (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame)
    (body tag plaintext : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest) (cache : CtxRomAuth.CtxRO.QueryCache)
    (hraw : raw ≠ []) (hdecode : codec.frameRead raw = some frame)
    (hsender : frame.sender = candidate.server_binding.identity_key_id) (hsequence : frame.sequence = 1#u64)
    (hpayload : frame.payload = body ++ tag ++ digest.toList) (hbody : body ≠ [])
    (hseal : setup.source.crypto.aeadSeal (absMaterial (beaconMaterial setup.source.crypto root)).1
      (absMaterial (beaconMaterial setup.source.crypto root)).2 (absBytes candidate.associated_data) plaintext =
        (body, tag))
    (hcache : cache ((), Pqxdh.ctxPreimage (absMaterial (beaconMaterial setup.source.crypto root))
      ⟨absBytes candidate.associated_data, 1, frame.sender.val⟩ tag) = some digest) :
    ∃ kernel, (simulateQ (beaconTail setup codec) (simulateQ PqxdhBeaconPhase2Publication.rawLift
        ((RawCtxWholeOwner.rawReceive codec.frameRead raw).run
          (PqxdhBeaconPhase2Publication.localOwner candidate (beaconKernel setup.source.crypto root))))).run
          ((), cache) =
      pure ((.Some ⟨plaintext, frame.sender, 1#u64⟩,
        ⟨{ (PqxdhBeaconPhase2Publication.localOwner candidate
          (beaconKernel setup.source.crypto root)).owner with kernel := kernel }, 1⟩), ((), cache)) := by
  obtain ⟨pending, opened, hbegin, hresume, hmaterial, hsequence', hcontext⟩ :=
    beacon_receive setup.source (root := root)
      (⟨raw, frame, absBytes candidate.associated_data⟩ : RawCtxWholeOwner.OpenContext)
  have hempty : raw.isEmpty = false := by
    cases raw with
    | nil => exact absurd rfl hraw
    | cons _ _ => rfl
  have htag : tag.length = 16 := by
    have := setup.source.crypto.aeadSeal_tag_length (absMaterial (beaconMaterial setup.source.crypto root)).1
      (absMaterial (beaconMaterial setup.source.crypto root)).2 (absBytes candidate.associated_data) plaintext
    rw [hseal] at this
    exact this
  have hvalid : RawCtxReceive.ValidFrame candidate.server_binding.identity_key_id
      (absBytes candidate.associated_data) frame := by
    refine ⟨hsender, ?_, by simp⟩
    have positive : 0 < body.length := List.length_pos_iff.mpr hbody
    rw [hpayload]
    simp [htag]
    omega
  have hargs := arguments_of opened _ _ hmaterial hsequence'
  refine ⟨(RawCtxOwnerOracle.finish opened
    (.Some (RawCtxWholeOwner.Decrypted.mk plaintext frame.sender 1#u64))).1, ?_⟩
  simp only [RawCtxWholeOwner.rawReceive, StateT.run, hempty, Bool.false_eq_true, ite_false, hdecode,
    PqxdhBeaconPhase2Publication.localOwner, hvalid, ite_true, hsequence, RawCtxOwnerOracle.receive, hbegin]
  rw [RawCtxOwnerOracle.program]
  simp only [simulateQ_bind, simulateQ_spec_query, RawCtxWholeOwner.adapter, PqxdhBeaconPhase2Publication.rawLift,
    simulateQ_pure]
  change (simulateQ (beaconTail setup codec) _ >>= _).run ((), cache) = _
  rw [StateT.run_bind]
  erw [hresume]
  rw [RawCtxOwnerOracle.program]
  simp only [simulateQ_bind, simulateQ_spec_query, RawCtxWholeOwner.adapter, PqxdhBeaconPhase2Publication.rawLift,
    simulateQ_pure, hargs, hcontext]
  simp only [StateT.run_bind, bind_assoc]
  have hcache' : cache ((), Pqxdh.ctxPreimage (absMaterial (beaconMaterial setup.source.crypto root))
      ⟨absBytes candidate.associated_data, (1#u64 : Std.U64).val, frame.sender.val⟩ tag) = some digest := hcache
  have hopen := beacon_open setup codec ⟨beaconMaterial setup.source.crypto root, 1#u64,
    ⟨raw, frame, absBytes candidate.associated_data⟩⟩ body tag plaintext digest cache hpayload hbody
    (by simp) hseal hcache'
  rw [show chainMaterial setup.source.crypto (beaconKernel setup.source.crypto root).refined.receive_chain =
    beaconMaterial setup.source.crypto root from rfl, hopen]
  simp only [pure_bind, StateT.run_pure]
  rfl

/-- The Beacon's post-root tail on an honest Phase 2 stages the sealed plaintext. -/
theorem beacon_afterRoot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : Word32) (raw : Pqxdh.Bytes)
    (frame : RawCtxReceive.DecodedFrame) (body tag payload : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (happ : codec.application pending.collected.response = some raw)
    (hraw : raw ≠ []) (hdecode : codec.frameRead raw = some frame)
    (hsender : frame.sender = pending.metadata.binding.identity_key_id) (hsequence : frame.sequence = 1#u64)
    (hpayload : frame.payload = body ++ tag ++ digest.toList) (hbody : body ≠ []) (nonempty : payload ≠ [])
    (hseal : setup.source.crypto.aeadSeal (absMaterial (beaconMaterial setup.source.crypto root)).1
      (absMaterial (beaconMaterial setup.source.crypto root)).2 (absBytes pending.metadata.associatedData)
        (Pqxdh.LE64 pending.metadata.assigned.val ++ payload) = (body, tag))
    (hcache : cache ((), Pqxdh.ctxPreimage (absMaterial (beaconMaterial setup.source.crypto root))
      ⟨absBytes pending.metadata.associatedData, 1, frame.sender.val⟩ tag) = some digest) :
    ∃ kernel, (simulateQ (PqxdhServerAuthExperiment.beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending root)).run ((), cache) =
      pure (some ⟨⟨PqxdhBeaconPhase2Publication.clearedCandidate
          (PqxdhPhase2DhRootConsumer.cleared pending).candidate⟩,
        pending.metadata.associatedData, kernel,
        ⟨Pqxdh.LE64 pending.metadata.assigned.val ++ payload, frame.sender, 1#u64⟩⟩, ((), cache)) := by
  obtain ⟨kernel, hraw'⟩ := beacon_raw setup codec root
    (PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate)
    raw frame body tag (Pqxdh.LE64 pending.metadata.assigned.val ++ payload) digest cache hraw hdecode hsender
    hsequence hpayload hbody hseal hcache
  refine ⟨kernel, ?_⟩
  simp only [PqxdhPhase2DhRootConsumer.afterRoot, ← QueryImpl.simulateQ_compose,
    PqxdhBeaconPhase2Publication.afterRoot, PqxdhBeaconPhase2Publication.initialRun, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, bind_assoc, pure_bind, PqxdhBeaconPhase2Publication.nativeTailAdapter,
    PqxdhServerAuthExperiment.beaconNative, PqxdhPhase2DhRootConsumer.cleared, happ]
  simp only [beaconTail, ← QueryImpl.simulateQ_compose, PqxdhPhase2DhRootConsumer.cleared, beaconKernel] at hraw'
  rw [StateT.run_bind, hraw', pure_bind, StateT.run_pure]
  have staged := PqxdhPhase2LocalMatching.afterOpening_of_binding
    (PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata))
    kernel ⟨Pqxdh.LE64 pending.metadata.assigned.val ++ payload, frame.sender, 1#u64⟩ hsender rfl payload nonempty rfl
  simp only []
  rw [staged]
  rfl

open PqxdhServerAuthExperiment (stageImpl beaconPrefix beaconAuxUnit liftUnit simulateQ_liftUnit) in
/-- The Beacon stage's preparation is the lifted stateless preparation. -/
theorem stage_prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK)
    (raw : Pqxdh.Bytes) :
    simulateQ (stageImpl setup codec beaconSeed) (simulateQ PqxdhPhase2DhStage.prefixLift
      (PqxdhPhase2DhMetadata.prepare (Response := Response) control identity oneTime kem raw)) =
      liftCoins ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run' ()) := by
  rw [← QueryImpl.simulateQ_compose]
  have prefixEq : stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.prefixLift =
      liftUnit (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain (beaconAuxUnit setup codec beaconSeed)
        (fun _ => pure ())) := by
    funext query
    exact simulateQ_spec_query (stageImpl setup codec beaconSeed) _
  rw [prefixEq, simulateQ_liftUnit]
  rfl

open PqxdhServerAuthExperiment (stageImpl beaconFamily beaconNative onCtx) in
/-- The Beacon stage's native tail requests run on the shared cache. -/
theorem stage_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    {α : Type} (work : OracleComp (PqxdhBeaconPhase2Publication.NativeTailSpec Response) α) :
    simulateQ (stageImpl setup codec beaconSeed) (simulateQ (PqxdhPhase2DhStage.tailLift (I := Unit)
      (D := Unit ⊕ ScalarBytes) (K := KemSK) (X := Unit) (Response := Response))
        (simulateQ PqxdhPhase2DhRootConsumer.nativeLift work)) =
      simulateQ (fun query => onCtx (beaconNative setup codec query)) work := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, PqxdhPhase2DhRootConsumer.nativeLift, PqxdhPhase2DhStage.tailLift,
    simulateQ_spec_query]
  rfl

open PqxdhServerAuthExperiment (onCtx) in
/-- A cache-only computation run inside the game. -/
theorem onCtx_simulate {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (handler : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp))
    (work : OracleComp spec α) (state : GameState KemSK) :
    (simulateQ (fun query => onCtx (handler query)) work).run state =
      coins ((simulateQ handler work).run ((), state.ctx)) >>= fun result =>
        pure (result.1, { state with ctx := result.2.2 }) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp [coins]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ih]
      rw [show StateT.run (onCtx (handler query)) state = coins ((handler query).run ((), state.ctx)) >>=
        fun result => pure (result.1, { state with ctx := result.2.2 }) from rfl]
      simp only [coins, simulateQ_bind, bind_assoc, pure_bind]

open PqxdhServerAuthExperiment (binding) in
/-- The target Beacon's control after its Phase 1. -/
def beaconControl (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) :
    pqxdh.BeaconInitSent :=
  PqxdhBeaconPhase1Publication.control ⟨binding setup publicValue⟩
    (PqxdhLivePhase1Bundle.identityArray (setup.joint.publicKeys beaconSeed).ed25519)

/-- The Extract random-oracle interpretation of the experiment's root requests. -/
noncomputable abbrev romReduction (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp) :=
  PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction

/-- A root request whose input bytes are already in the table returns the real Expand of the cached block. -/
theorem rom_root_hit (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (bytes : Pqxdh.Bytes) (prk : HmacBlock)
    (family : PqxdhJointDhExtractFamily.State)
    (hinput : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message = some bytes)
    (hprk : family.cache bytes = some prk) :
    (romReduction setup seed scalar (.inr (.derive message))).run family =
      pure (some (expandRoot setup.hmac prk), (⟨family.history ++ [.derive message (some prk),
        .publicHmac prk rootExpandInput (setup.hmac.eval prk rootExpandInput)], family.cache⟩ :
          PqxdhJointDhExtractFamily.State)) := by
  rw [PqxdhExtractRomFamily.rom_root]
  simp only [hinput, randomOracle.run_eq, hprk, map_pure]

/-- The Beacon's final checks publish a staged registration whose pins match. -/
theorem finish_honest {I D K : Type} (control : pqxdh.BeaconInitSent) (beacon : RawCtxBeaconLifecycle.State I D K)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (hkey : control.expected_server_binding.identity_key_id =
      staged.authenticated.candidate.server_binding.identity_key_id)
    (hidentity : absBytes beacon.beacon.serverIdentity =
      absBytes staged.authenticated.candidate.server_binding.identity_public_key) :
    PqxdhBeaconPhase2Publication.finish control beacon (some staged) =
      (some (staged.opened.plaintext.drop 8), (PqxdhBeaconPhase2Publication.publish beacon staged).2) := by
  simp only [PqxdhBeaconPhase2Publication.finish, hkey, hidentity, ne_eq, not_true_eq_false, ite_false]
  rfl

/-- The key-ID binding prefix is dropped from the accepted payload. -/
theorem drop_binding (keyId : Std.U64) (payload : Pqxdh.Bytes) :
    (Pqxdh.LE64 keyId.val ++ payload).drop 8 = payload :=
  List.drop_left' (Pqxdh.LE64_length _)

open PqxdhServerAuthExperiment (finishOracle stageImpl beaconFamily beaconNative onCtx forwardFamily recordTouch) in
/-- The target Beacon's finish on an honest Phase 2 accepts the sealed payload. -/
theorem beacon_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (oneTime e : ScalarBytes)
    (kemSk : KemSK) (raw : Pqxdh.Bytes) (response : Response) (ciphertext : Ciphertext) (keyId : Std.U64)
    (secret : PqxdhKemIndCca.MlKemSharedSecret)
    (hread : codec.read2 raw = some response) (hct : codec.ciphertext response = some ciphertext)
    (heph : codec.ephemeral response = some (rootArray (setup.dh.publicKey e)))
    (hsid : codec.serverIdentity response = some (rootArray (setup.joint.publicKeys seed).ed25519))
    (hid : codec.assignedId response = keyId)
    (hdecap : functional.result kemSk (PqxdhPhase2InputBytes.ciphertext ciphertext) = some secret)
    (frameBytes : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) (body tag payload : Pqxdh.Bytes)
    (digest : CtxRomAuth.CtxDigest)
    (happ : codec.application response = some frameBytes) (hframeBytes : frameBytes ≠ [])
    (hdecode : codec.frameRead frameBytes = some frame) (hsender : frame.sender = setup.serverKeyId)
    (hsequence : frame.sequence = 1#u64) (hpayload : frame.payload = body ++ tag ++ digest.toList)
    (hbody : body ≠ []) (nonempty : payload ≠ [])
    (bytes : Pqxdh.Bytes) (prk : HmacBlock) (family : PqxdhJointDhExtractFamily.State)
    (hinput : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar
      (PqxdhJointDhExtractRoot.beaconMessage (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
        (beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret)) = some bytes)
    (hprk : family.cache bytes = some prk)
    (hseal : setup.source.crypto.aeadSeal
      (absMaterial (beaconMaterial setup.source.crypto (rootArray (expandRoot setup.hmac prk)))).1
      (absMaterial (beaconMaterial setup.source.crypto (rootArray (expandRoot setup.hmac prk)))).2
      (absBytes (PqxdhBeaconPhase2Shared.associatedData
        (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed)))
        (Pqxdh.LE64 keyId.val ++ payload) = (body, tag))
    (state : GameState KemSK)
    (hbeacon : state.beacon = publishedBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed oneTime kemSk)
    (hcache : state.ctx ((), Pqxdh.ctxPreimage
      (absMaterial (beaconMaterial setup.source.crypto (rootArray (expandRoot setup.hmac prk))))
      ⟨absBytes (PqxdhBeaconPhase2Shared.associatedData
        (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed)),
        1, frame.sender.val⟩ tag) = some digest) :
    ∃ beacon family', (simulateQ (romReduction setup seed scalar)
        ((finishOracle setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed raw).run
          state)).run family =
      pure ((some payload, { state with
        beacon := beacon
        ghost := ({ state.ghost with touches := state.ghost.touches ++
          [.beacon (PqxdhJointDhExtractRoot.beaconMessage (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            (beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret))] } : Ghost).accept
          (some ⟨keyId, payload, absBytes (PqxdhBeaconPhase2Shared.associatedData
            (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed))⟩) }),
        family') := by
  have hphase : state.beacon.beacon.phase = .initSent
      (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed)
      (.inl ()) (.inr oneTime) kemSk := by
    rw [hbeacon]; rfl
  have hidentity : state.beacon.beacon.identity = () := rfl
  have hpin : absBytes (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed).expected_server_binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList :=
    PqxdhRootTableInitialization.rootArray_bytes _
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind, hphase, hidentity,
    PqxdhPhase2DhStage.stage, simulateQ_bind, stage_prepare, StateT.run'_eq,
    beacon_prepare setup codec functional nonzero seed beaconSeed oneTime e kemSk raw response ciphertext keyId
      secret _ hread hct heph hsid hid hdecap hpin, map_pure, PqxdhServerAuthExperiment.liftCoins_pure]
  simp only [PqxdhPhase2DhRootConsumer.tail, simulateQ_bind, PqxdhPhase2DhRootConsumer.root,
    simulateQ_map, simulateQ_spec_query, StateT.run_bind, StateT.run_map, 
    bind_assoc]
  simp only [PqxdhPhase2DhRootConsumer.rootLift, PqxdhPhase2DhStage.tailLift, simulateQ_spec_query, stageImpl,
    beaconFamily, recordTouch, forwardFamily, StateT.run_bind, StateT.run_modify, StateT.run_lift, bind_assoc, pure_bind,
    map_bind, simulateQ_bind, simulateQ_pure]
  rw [rom_root_hit setup seed scalar _ bytes prk family hinput hprk]
  simp only [pure_bind, map_pure, Option.map_some, StateT.run_pure, simulateQ_pure, stage_native]
  obtain ⟨kernel, hafter⟩ := beacon_afterRoot setup codec
    ⟨beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret,
      ⟨(beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
        beaconSeed).expected_server_binding, keyId, PqxdhBeaconPhase2Shared.associatedData
          (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed)⟩⟩
    (rootArray (expandRoot setup.hmac prk)) frameBytes frame body tag payload digest state.ctx happ hframeBytes
    hdecode hsender hsequence hpayload hbody nonempty hseal hcache
  rw [onCtx_simulate, hafter]
  simp only [coins, simulateQ_pure, pure_bind, StateT.run_pure]
  rw [finish_honest _ _ _ rfl (by rw [hbeacon]; rfl)]
  simp only [PqxdhServerAuthExperiment.acceptedOf, Option.isSome_some, ite_true, Option.map_some,
    PqxdhServerAuthExperiment.Accepted.ofStaged, drop_binding, StateT.run_set, simulateQ_pure, StateT.run_pure,
    pure_bind]
  exact ⟨_, _, rfl⟩

/-! ## Running adversaries and the KEM split -/

/-- The experiment's run of an adversary computation from a game state and a family state. -/
noncomputable def runAdversary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) {α : Type}
    (work : OracleComp ExpSpec α) (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    ProbComp ((α × GameState KemSK) × PqxdhJointDhExtractFamily.State) :=
  (simulateQ (romReduction setup seed scalar) ((simulateQ (expHandler setup codec checks
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed) work).run state)).run family

/-- Sequencing of the experiment's run. -/
theorem runAdversary_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) {α β : Type}
    (first : OracleComp ExpSpec α) (next : α → OracleComp ExpSpec β) (state : GameState KemSK)
    (family : PqxdhJointDhExtractFamily.State) :
    runAdversary setup codec checks seed scalar beaconSeed (first >>= next) state family =
      runAdversary setup codec checks seed scalar beaconSeed first state family >>= fun result =>
        runAdversary setup codec checks seed scalar beaconSeed (next result.1.1) result.1.2 result.2 := by
  simp only [runAdversary, simulateQ_bind, StateT.run_bind]

/-- A returned value leaves both states unchanged. -/
theorem runAdversary_pure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) {α : Type} (value : α)
    (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    runAdversary setup codec checks seed scalar beaconSeed (pure value) state family =
      pure ((value, state), family) := by
  simp only [runAdversary, simulateQ_pure, StateT.run_pure]

/-- One adversary query is its oracle's run. -/
theorem runAdversary_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (query : ExpSpec.Domain)
    (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    runAdversary setup codec checks seed scalar beaconSeed (liftM (ExpSpec.query query)) state family =
      (simulateQ (romReduction setup seed scalar) ((expHandler setup codec checks
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed query).run state)).run family := by
  simp only [runAdversary, simulateQ_spec_query]

/-- The adversary's use of uniform coins: every coin query of a probabilistic computation is forwarded to the experiment's coin oracle. -/
def advCoins {α : Type} (work : ProbComp α) : OracleComp ExpSpec α :=
  simulateQ (fun query => (ExpSpec.query (.inl query) : OracleComp ExpSpec _)) work

/-- The adversary's coins run the computation itself and leave both states unchanged. -/
theorem runAdversary_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) {α : Type} (work : ProbComp α)
    (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    runAdversary setup codec checks seed scalar beaconSeed (advCoins work) state family =
      (fun value => ((value, state), family)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state family with
  | pure value => simp [advCoins, runAdversary]
  | query_bind query next ih =>
      simp only [advCoins] at ih ⊢
      rw [simulateQ_bind, runAdversary_bind, simulateQ_spec_query, runAdversary_query]
      simp only [ih]
      change (simulateQ (romReduction setup seed scalar)
        ((PqxdhServerAuthExperiment.forwardFamily (.inl query) : PqxdhServerAuthExperiment.Game KemSK _).run state)).run
          family >>= _ = _
      simp only [PqxdhServerAuthExperiment.forwardFamily, StateT.run_lift, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure]
      simp only [romReduction]
      rw [(PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).1 query]
      simp only [PqxdhExtractRomFamily.romImpl, StateT.run, bind_assoc, pure_bind, map_bind]

/-- The target Beacon's Phase 1 outcome: the written bytes and the published Beacon, or nothing and the fresh Beacon. -/
def phase1Result (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (publicValue : PublicChallenge)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK :=
  match codec.write1 (beaconCandidate setup publicValue beaconSeed oneTime kemPk) with
  | none => (none, PqxdhServerAuthExperiment.freshBeacon setup publicValue kemSk)
  | some bytes => (some bytes, publishedBeacon setup publicValue beaconSeed oneTime kemSk)

/-- The adversary's input in the experiment: the pinned Server identity, the Server key ID, the Beacon's Phase 1 and the revealed seed, if any. -/
def controlInput (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (phase1 : Option Pqxdh.Bytes)
    (revealed : Option IdentitySeed) : Input :=
  ⟨publicValue.identity, setup.serverKeyId, phase1, revealed⟩

/-- The KEM key-generation computation of the experiment. -/
noncomputable abbrev keygenRun (setup : Setup baseSpec KemSK) :
    ProbComp (PqxdhKemIndCca.MlKem768PublicKey × KemSK) :=
  simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen

set_option linter.deprecated false in
/-- The per-key-pair KEM correctness error: the probability that an encapsulation to the key is not recovered. -/
noncomputable def keyPairError (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) : ℝ≥0∞ :=
  Pr[fun drawn => PqxdhKemCorrectnessError.Bad setup.kem functional ⟨keys.1, keys.2, drawn.1, drawn.2⟩ |
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps keys.1)]

/-- The body under the Extract random oracle samples the Beacon's secrets and Phase 1, then runs the adversary. -/
theorem body_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealed : Option IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes) :
    (simulateQ (romReduction setup seed scalar) (body setup codec checks adversary revealed
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run PqxdhJointDhExtractFamily.empty =
      sampleSeed >>= fun beaconSeed => PqxdhJointGapDh.sampleScalar >>= fun oneTime => keygenRun setup >>= fun keys =>
      (fun result => (result.1.2, result.2)) <$> runAdversary setup codec checks seed scalar beaconSeed
        (adversary (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 revealed))
        (initial setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2)
        PqxdhJointDhExtractFamily.empty := by
  simp only [body, simulateQ_bind, StateT.run_bind, rom_coins, bind_map_left, simulateQ_map, StateT.run_map,
    romReduction]
  refine bind_congr fun beaconSeed => bind_congr fun oneTime => bind_congr fun keys => ?_
  rw [phase1Run_eq, pure_bind]
  rfl

set_option linter.deprecated false in
/-- Averaging the per-key-pair error over key generation gives the KEM correctness error. -/
theorem keyPairError_average (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) :
    ∑' keys, Pr[= keys | keygenRun setup] * keyPairError setup functional keys =
      Pr[= true | simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (PqxdhKemCorrectnessError.errorExperiment setup.kem)] := by
  rw [PqxdhKemCorrectnessError.error_probability setup.baseImpl setup.kem functional]
  simp only [PqxdhKemCorrectnessError.sample, simulateQ_bind, simulateQ_pure]
  rw [probEvent_bind_eq_tsum]
  refine tsum_congr fun keys => ?_
  congr 1
  rw [keyPairError, bind_pure_comp, probEvent_map]
  rfl

set_option linter.deprecated false in
/-- KEM split of the experiment: if, for every sampled Beacon key pair, the adversary's run makes an event hold with probability at most the key pair's correctness error, then the event has probability at most the KEM correctness error. -/
theorem kem_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (event : IdentitySeed → ScalarBytes → GameState KemSK → Prop)
    (bound : ∀ seed scalar beaconSeed oneTime keys, keys ∈ support (keygenRun setup) →
      Pr[fun result => event seed scalar result.1.2 | runAdversary setup codec checks seed scalar beaconSeed
        (adversary (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 (if revealSeed then some seed else none)))
        (initial setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2)
        PqxdhJointDhExtractFamily.empty] ≤ keyPairError setup functional keys) :
    Pr[fun result => event result.1 result.2.1 result.2.2.1 | gameState setup codec checks revealSeed adversary] ≤
      Pr[= true | simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (PqxdhKemCorrectnessError.errorExperiment setup.kem)] := by
  rw [gameState]
  refine probEvent_bind_le_of_forall_le fun seed _ => probEvent_bind_le_of_forall_le fun scalar _ => ?_
  rw [bind_pure_comp, probEvent_map]
  change Pr[_ | (simulateQ (romReduction setup seed scalar) (body setup codec checks adversary
    (if revealSeed then some seed else none) (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run
      PqxdhJointDhExtractFamily.empty] ≤ _
  rw [body_run]
  refine probEvent_bind_le_of_forall_le fun beaconSeed _ => probEvent_bind_le_of_forall_le fun oneTime _ => ?_
  rw [probEvent_bind_eq_tsum, ← keyPairError_average setup functional]
  refine ENNReal.tsum_le_tsum fun keys => ?_
  by_cases supported : keys ∈ support (keygenRun setup)
  · refine mul_le_mul_right ?_ _
    rw [probEvent_map]
    exact bound seed scalar beaconSeed oneTime keys supported
  · rw [probOutput_eq_zero_of_not_mem_support supported, zero_mul, zero_mul]

/-! ## The control adversary -/

open PqxdhEd25519EufCma (splitAttachedSignature parseIdentity parsePrekeyMessage parseOneTimeMessage parsePqMessage) in
/-- The control adversary's parse of a published Phase 1: the Beacon's identity key and its three signed public keys, read with the codec and without verifying signatures. -/
def parsePhase1 (codec : Codec Reader Response) (bytes : Pqxdh.Bytes) :
    Option (Ed25519PublicKey × Phase1KeyTuple) := do
  let reader ← codec.read1 bytes
  let encoded ← codec.identity reader
  let identity ← parseIdentity encoded
  let pre ← codec.preField reader
  let one ← codec.oneField reader
  let pq ← codec.pqField reader
  let preSplit ← splitAttachedSignature pre
  let oneSplit ← splitAttachedSignature one
  let pqSplit ← splitAttachedSignature pq
  let prekey ← parsePrekeyMessage preSplit.2
  let oneTime ← parseOneTimeMessage oneSplit.2
  let pqKey ← parsePqMessage pqSplit.2
  pure (identity, ⟨prekey, oneTime, pqKey⟩)

/-- The control adversary recovers the target Beacon's keys from the published Phase 1. -/
theorem parse_honest (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (readBack : Phase1ReadBack codec)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (bytes : Pqxdh.Bytes)
    (written : codec.write1 (beaconCandidate setup publicValue beaconSeed oneTime kemPk) = some bytes) :
    parsePhase1 codec bytes = some ((setup.joint.publicKeys beaconSeed).ed25519,
      ⟨publicValue.prekey, setup.dh.publicKey oneTime, kemPk⟩) := by
  obtain ⟨reader, hread, hidentity, hpq, hpre, hone⟩ := readBack _ bytes written
  simp [parsePhase1, hread, hidentity, hpq, hpre, hone, beaconCandidate,
    PqxdhJointPhase1SourceWriter.candidate]

/-- The pinned control of a Beacon with a given identity, as seen from the public input. -/
def controlOf (input : Input) (identity : Ed25519PublicKey) : pqxdh.BeaconInitSent :=
  ⟨⟨rootArray input.server.ed25519, input.serverKeyId⟩, PqxdhLivePhase1Bundle.identityArray identity⟩

/-- An X25519 value as a 32-byte DH output. -/
def dhValue (c : Pqxdh.Crypto) (scalar : ScalarBytes) (point : Pqxdh.Bytes) : DhOutput :=
  ⟨c.x25519 scalar.toList point, c.x25519_length _ _⟩

/-- The 192-byte root input an honest Server with seed `seed` and ephemeral `e` derives for a Beacon's keys and a KEM secret. -/
def controlBytes (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (identity : Ed25519PublicKey)
    (keys : Phase1KeyTuple) (e : ScalarBytes) (secret : PqxdhKemIndCca.MlKemSharedSecret) : Option Pqxdh.Bytes :=
  (setup.joint.staticDh seed keys.prekey).map fun first =>
    PqxdhJointGapDh.assemble ⟨keys.prekey, keys.prekey,
      dhValue setup.source.crypto e ((setup.source.crypto.xpkConv identity.toList).getD []),
      dhValue setup.source.crypto e keys.oneTime.toList, secret⟩ first
      (dhValue setup.source.crypto e keys.prekey.toList)

/-- The fixed key ID the control adversary assigns. -/
def controlKeyId : Std.U64 := 0#u64

/-- The control adversary: with the Server seed revealed and the target's Phase 1 parsed, it draws an ephemeral and an encapsulation to the Beacon's ML-KEM key, obtains the Extract block of the Beacon's root input through the public zero-key HMAC, derives the root and the sequence-one material, seals `LE64 0 ++ payload` under the Beacon's associated data with the commitment from the public BLAKE2b oracle, writes the frame and Phase 2, and delivers it to the finish. It never queries accept or build. -/
noncomputable def controlAdversary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (payload : Pqxdh.Bytes) : Adversary := fun input =>
  match input.revealed, input.phase1.bind (parsePhase1 codec) with
  | some seed, some parsed => do
      let e ← advCoins PqxdhJointGapDh.sampleScalar
      let encapsulated ← advCoins (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.encaps parsed.2.pqKey))
      match controlBytes setup seed parsed.1 parsed.2 e encapsulated.2 with
      | none => pure ()
      | some bytes => do
          let prk ← (ExpSpec.query (.inr (.hmac zeroSalt bytes)) : OracleComp ExpSpec HmacBlock)
          let material := beaconMaterial setup.source.crypto (rootArray (expandRoot setup.hmac prk))
          let ad := absBytes (PqxdhBeaconPhase2Shared.associatedData (controlOf input parsed.1))
          let sealed := setup.source.crypto.aeadSeal (absMaterial material).1 (absMaterial material).2 ad
            (Pqxdh.LE64 controlKeyId.val ++ payload)
          let digest ← (ExpSpec.query (.inr (.hash (Pqxdh.ctxPreimage (absMaterial material)
            ⟨ad, 1, input.serverKeyId.val⟩ sealed.2))) : OracleComp ExpSpec CtxRomAuth.CtxDigest)
          match codec.frameWrite ⟨1#u64, input.serverKeyId, sealed.1 ++ sealed.2 ++ digest.toList⟩ with
          | none => pure ()
          | some frameBytes =>
              match codec.write2 ⟨controlKeyId, rootArray (setup.dh.publicKey e), rootArray input.server.ed25519,
                  PqxdhAcceptedRegistration.ciphertextArray encapsulated.1, frameBytes⟩ with
              | none => pure ()
              | some phase2 => do
                  let _ ← (ExpSpec.query (.inr (.finish phase2)) : OracleComp ExpSpec (Option Pqxdh.Bytes))
                  pure ()
  | _, _ => pure ()

/-! ## Query budgets -/

/-- The adversary's coins never count against a budget whose predicate ignores coin queries. -/
theorem advCoins_bound {α : Type} (p : ExpSpec.Domain → Prop) [DecidablePred p]
    (free : ∀ query, ¬ p (.inl query)) (work : ProbComp α) (n : ℕ) : (advCoins work).IsQueryBoundP p n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure x => simp [advCoins]
  | query_bind t mx ih =>
      rw [advCoins, simulateQ_query_bind]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (free t), fun _ => ih _ _⟩

/-- Coins followed by a budgeted continuation stay within the continuation's budget. -/
theorem advCoins_bind {α β : Type} (p : ExpSpec.Domain → Prop) [DecidablePred p]
    (free : ∀ query, ¬ p (.inl query)) (work : ProbComp α) (next : α → OracleComp ExpSpec β) (n : ℕ)
    (bounded : ∀ value, (next value).IsQueryBoundP p n) : (advCoins work >>= next).IsQueryBoundP p n := by
  simpa using isQueryBoundP_bind (advCoins_bound p free work 0) (fun value _ => bounded value)

open PqxdhServerAuthExperiment (AuthBudget IsAcceptQuery IsRomQuery IsHashQuery) in
/-- The honest relay makes at most one Server accept and no random-oracle HMAC or BLAKE2b query. -/
theorem relay_budget (payload : Option Pqxdh.Bytes) : AuthBudget (relayAdversary payload) 1 0 0 := by
  refine ⟨fun input => ?_, fun input => ?_, fun input => ?_⟩ <;>
  · unfold relayAdversary
    split
    · simp
    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery],
        fun session => ?_⟩
      unfold relayBuild
      split
      · simp
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery],
          fun response => ?_⟩
        unfold relayFinish
        split
        · simp
        · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery],
            fun _ => by simp⟩

open PqxdhServerAuthExperiment (AuthBudget IsAcceptQuery IsRomQuery IsHashQuery) in
/-- The control adversary makes no Server accept, at most one random-oracle HMAC query and at most one BLAKE2b query. -/
theorem control_budget (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (payload : Pqxdh.Bytes) :
    AuthBudget (controlAdversary setup codec payload) 0 1 1 := by
  refine ⟨fun input => ?_, fun input => ?_, fun input => ?_⟩ <;>
  · unfold controlAdversary
    split
    · refine advCoins_bind _ (fun _ => id) _ _ _ fun e => advCoins_bind _ (fun _ => id) _ _ _ fun encapsulated => ?_
      split
      · simp
      · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery],
          fun prk => ?_⟩
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery],
          fun digest => ?_⟩
        split
        · simp
        · split
          · simp
          · refine (isQueryBoundP_query_bind_iff _ _ _ _).2
              ⟨by simp [IsAcceptQuery, IsRomQuery, IsHashQuery], fun _ => by simp⟩
    · simp

/-- Queries to the Server's private-state methods: accept, build and reveal. -/
def IsServerQuery : ExpSpec.Domain → Prop
  | .inr (.accept _) => True
  | .inr (.build _ _) => True
  | .inr (.reveal _) => True
  | _ => False

/-- Server queries are decidable. -/
instance : DecidablePred IsServerQuery := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr (.accept _) => isTrue trivial
  | .inr (.build _ _) => isTrue trivial
  | .inr (.finish _) => isFalse id
  | .inr (.hmac _ _) => isFalse id
  | .inr (.hash _) => isFalse id
  | .inr (.reveal _) => isTrue trivial

/-- The control adversary never queries the Server: it makes no accept, build or reveal query. -/
theorem control_no_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (payload : Pqxdh.Bytes)
    (input : Input) : (controlAdversary setup codec payload input).IsQueryBoundP IsServerQuery 0 := by
  unfold controlAdversary
  split
  · refine advCoins_bind _ (fun _ => id) _ _ _ fun e => advCoins_bind _ (fun _ => id) _ _ _ fun encapsulated => ?_
    split
    · simp
    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsServerQuery], fun prk => ?_⟩
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsServerQuery], fun digest => ?_⟩
      split
      · simp
      · split
        · simp
        · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [IsServerQuery], fun _ => by simp⟩
  · simp

/-! ## The negative control -/

/-- The public conversion of an honest Ed25519 identity is the X25519 public key of its converted secret. -/
theorem identity_conversion (setup : Setup baseSpec KemSK) (beaconSeed : IdentitySeed) :
    (setup.source.crypto.xpkConv (setup.joint.publicKeys beaconSeed).ed25519.toList).getD [] =
      setup.source.crypto.xpub (setup.source.crypto.xsk (setup.secretOfSeed beaconSeed).toList) := by
  rw [setup.wiring.edPublic, setup.source.crypto.conv_agree]
  rfl

/-- The Beacon's DH2 is the Server's ephemeral DH with the converted Beacon identity. -/
theorem beaconSecond_eq (setup : Setup baseSpec KemSK) (beaconSeed : IdentitySeed) (e : ScalarBytes) :
    beaconSecond setup beaconSeed e = dhValue setup.source.crypto e
      ((setup.source.crypto.xpkConv (setup.joint.publicKeys beaconSeed).ed25519.toList).getD []) := by
  apply Subtype.ext
  rw [identity_conversion]
  exact (setup.source.crypto.dh_comm _ _).symm

/-- The Beacon's DH4 is the Server's ephemeral DH with the one-time key. -/
theorem beaconFourth_eq (setup : Setup baseSpec KemSK) (oneTime e : ScalarBytes) :
    beaconFourth setup oneTime e = dhValue setup.source.crypto e (setup.dh.publicKey oneTime).toList := by
  apply Subtype.ext
  exact setup.source.crypto.dh_comm _ _

/-- The Beacon's selected DH3 is the Server's ephemeral DH with the prekey. -/
theorem beacon_third_eq (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (scalar e : ScalarBytes) :
    setup.dh.dh scalar (setup.dh.publicKey e) = some (dhValue setup.source.crypto e (setup.dh.publicKey scalar).toList) := by
  change sourceScalarDh setup.source.crypto scalar (setup.dh.publicKey e) = _
  rw [sourceScalarDh_some _ _ _ (by exact nonzero _ _)]
  congr 1
  apply Subtype.ext
  exact setup.source.crypto.dh_comm _ _

/-- The Beacon's 192-byte root input is the one an honest Server derives with the revealed seed. -/
theorem beacon_input_eq (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (oneTime e : ScalarBytes)
    (response : Response) (ciphertext : Ciphertext) (keyId : Std.U64) (secret : PqxdhKemIndCca.MlKemSharedSecret)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) :
    PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar
        (PqxdhJointDhExtractRoot.beaconMessage (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (beaconCollected setup seed beaconSeed oneTime e response ciphertext keyId secret)) =
      controlBytes setup seed (setup.joint.publicKeys beaconSeed).ed25519
        ⟨setup.dh.publicKey scalar, setup.dh.publicKey oneTime, kemPk⟩ e secret := by
  simp only [PqxdhJointDhExtractFamily.input, PqxdhJointDhExtractRoot.beaconMessage, beaconCollected,
    PqxdhJointDhExtractFamily.thirdValue, PqxdhJointDhExtractFamily.address, peer_rootArray,
    beacon_third_eq setup nonzero, PqxdhPhase2InputBytes.word_rootArray, controlBytes,
    beaconSecond_eq, beaconFourth_eq, PqxdhJointGapDh.challenge]
  cases setup.joint.staticDh seed (setup.dh.publicKey scalar) <;> rfl

/-- After a lazy random-oracle query, the cache holds the returned answer at the queried point. -/
theorem randomOracle_cached {ι' : Type} [DecidableEq ι'] {spec : OracleSpec.{0, 0} ι'}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] (t : spec.Domain) (cache : spec.QueryCache)
    (result : spec.Range t × spec.QueryCache) (supported : result ∈ support ((spec.randomOracle t).run cache)) :
    result.2 t = some result.1 := by
  rw [randomOracle.run_eq] at supported
  cases hit : cache t with
  | some value =>
      simp only [hit, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact hit
  | none =>
      simp only [hit, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact QueryCache.cacheQuery_self _ _ _

/-- A public zero-key HMAC query on a 192-byte message is logged as an adversary touch and leaves its answer in the Extract table. -/
theorem run_hmac (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (bytes : Pqxdh.Bytes)
    (length : bytes.length = 192) (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (result : (HmacBlock × GameState KemSK) × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (runAdversary setup codec checks seed scalar beaconSeed
      (liftM (ExpSpec.query (.inr (.hmac zeroSalt bytes)))) state family)) :
    result.2.cache bytes = some result.1.1 ∧
      result.1.2 = { state with ghost := { state.ghost with touches := state.ghost.touches ++ [.adversary bytes] } } := by
  rw [runAdversary_query] at supported
  simp only [expHandler, PqxdhServerAuthExperiment.hmacOracle, and_self, length, ite_true,
    PqxdhServerAuthExperiment.recordTouch, PqxdhServerAuthExperiment.forwardFamily, StateT.run_bind,
    StateT.run_modify, StateT.run_lift, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, pure_bind] at supported
  simp only [romReduction] at supported
  rw [(PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).2.2 zeroSalt bytes,
    PqxdhExtractRomFamily.rom_public_oracle setup.hmac setup.joint setup.dh seed scalar zeroSalt bytes
      ⟨rfl, length⟩ family] at supported
  simp only [StateT.run_pure, bind_map_left, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨answer, member, rfl⟩ := supported
  exact ⟨randomOracle_cached _ _ _ member, rfl⟩

/-- A BLAKE2b query leaves its answer in the shared cache and changes nothing else. -/
theorem run_hash (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (bytes : Pqxdh.Bytes)
    (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (result : (CtxRomAuth.CtxDigest × GameState KemSK) × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (runAdversary setup codec checks seed scalar beaconSeed
      (liftM (ExpSpec.query (.inr (.hash bytes)))) state family)) :
    ∃ cache, result.1.2 = { state with ctx := cache } ∧ cache ((), bytes) = some result.1.1 ∧ result.2 = family := by
  rw [runAdversary_query] at supported
  simp only [expHandler, PqxdhServerAuthExperiment.hashOracle, StateT.run, simulateQ_bind, simulateQ_pure
] at supported
  change result ∈ support ((simulateQ (romReduction setup seed scalar)
    (coins ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.ctx))).run family >>= _) at supported
  rw [romReduction, rom_coins] at supported
  simp only [bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨answer, member, rfl⟩ := supported
  exact ⟨answer.2, rfl, randomOracle_cached (spec := CtxRomAuth.CtxRO) _ _ _ member, rfl⟩

/-- The Server's static DH with an honest prekey is present. -/
theorem static_present (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (seed : IdentitySeed)
    (scalar : ScalarBytes) : ∃ value, setup.joint.staticDh seed (setup.dh.publicKey scalar) = some value := by
  rw [setup.dh.agreement]
  change ∃ value, sourceScalarDh setup.source.crypto scalar (setup.joint.publicKeys seed).convertedX25519 = some value
  have converted := setup.wiring.xPublic seed
  exact ⟨_, sourceScalarDh_some _ _ _ (by rw [converted]; exact nonzero _ _)⟩

/-- The Phase 1 outcome when the writer succeeds. -/
theorem phase1Result_some (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) (bytes : Pqxdh.Bytes)
    (written : codec.write1 (beaconCandidate setup publicValue beaconSeed oneTime kemPk) = some bytes) :
    phase1Result setup codec publicValue beaconSeed oneTime kemPk kemSk =
      (some bytes, publishedBeacon setup publicValue beaconSeed oneTime kemSk) := by
  simp only [phase1Result, written]

set_option linter.deprecated false in
/-- Per key pair, the control adversary fails to make the Beacon accept without a partner (the event `W1`) with probability at most the key pair's KEM correctness error. -/
theorem control_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (limit : Nat) (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload : Pqxdh.Bytes) (nonempty : payload ≠ []) (short : payload.length + 88 < limit) (seed : IdentitySeed) (scalar : ScalarBytes)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) :
    Pr[fun result => ¬ PqxdhServerAuthExperiment.W1 setup seed scalar result.1.2.ghost | runAdversary setup codec checks seed scalar beaconSeed
        (controlAdversary setup codec payload (controlInput setup
          (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 (some seed)))
        (initial setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2)
        PqxdhJointDhExtractFamily.empty] ≤ keyPairError setup functional keys := by
  obtain ⟨bytes, written⟩ := laws.phase1Total (beaconCandidate setup
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1)
  rw [phase1Result_some setup codec _ beaconSeed oneTime keys.1 keys.2 bytes written]
  simp only [controlAdversary, controlInput, Option.bind_some,
    parse_honest setup codec laws.phase1 _ beaconSeed oneTime keys.1 bytes written]
  rw [runAdversary_bind, runAdversary_coins, bind_map_left]
  refine probEvent_bind_le_of_forall_le fun e _ => ?_
  rw [runAdversary_bind, runAdversary_coins, bind_map_left]
  refine le_trans (probEvent_bind_le_probEvent
    (p := fun drawn => PqxdhKemCorrectnessError.Bad setup.kem functional ⟨keys.1, keys.2, drawn.1, drawn.2⟩)
    fun encapsulated _ good => ?_) le_rfl
  obtain ⟨first, hfirst⟩ := static_present setup laws.nonzero seed scalar
  obtain ⟨bytes0, hcb⟩ : ∃ bytes0, controlBytes setup seed (setup.joint.publicKeys beaconSeed).ed25519
      ⟨setup.dh.publicKey scalar, setup.dh.publicKey oneTime, keys.1⟩ e encapsulated.2 = some bytes0 :=
    ⟨_, by rw [controlBytes, hfirst]; rfl⟩
  have hlen : bytes0.length = 192 := by
    simp only [controlBytes, hfirst, Option.map_some, Option.some.injEq] at hcb
    rw [← hcb]
    exact PqxdhJointGapDh.assemble_length _ _ _
  simp only [PqxdhJointGapDh.challenge, hcb]
  refine probEvent_eq_zero fun result supported => ?_
  rw [not_not]
  rw [runAdversary_bind, mem_support_bind_iff] at supported
  obtain ⟨first', hmacRun, supported⟩ := supported
  obtain ⟨hprk, hstate1⟩ := run_hmac setup codec checks seed scalar beaconSeed bytes0 hlen _ _ first' hmacRun
  rw [runAdversary_bind, mem_support_bind_iff] at supported
  obtain ⟨second, hashRun, supported⟩ := supported
  obtain ⟨cache2, hstate2, hcache2, hfamily2⟩ := run_hash setup codec checks seed scalar beaconSeed _ _ _ second hashRun
  have hshort : ∀ key nonce ad : Pqxdh.Bytes, ∀ digest : CtxRomAuth.CtxDigest,
      ((setup.source.crypto.aeadSeal key nonce ad (Pqxdh.LE64 controlKeyId.val ++ payload)).1 ++
        (setup.source.crypto.aeadSeal key nonce ad (Pqxdh.LE64 controlKeyId.val ++ payload)).2 ++
          digest.toList).length < limit := by
    intro key nonce ad digest
    rw [protected_length _ laws.bodyLength, List.length_append, Pqxdh.LE64_length]
    omega
  split at supported
  · rename_i hnone
    exact absurd hnone (frame_written laws _ (hshort _ _ _ _))
  rename_i frameBytes hframe
  split at supported
  · rename_i hnone
    exact absurd hnone (phase2_written laws _ frameBytes (hshort _ _ _ _) hframe _ _ _ _)
  rename_i phase2 hphase2
  rw [runAdversary_bind, mem_support_bind_iff] at supported
  obtain ⟨third, finishRun, supported⟩ := supported
  rw [runAdversary_pure, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨response, hread, hct, heph, hsid, hid, happ⟩ := laws.phase2 _ phase2 hphase2
  obtain ⟨hne, hdecode⟩ := laws.frame _ frameBytes hframe
  have hdecap : functional.result keys.2 (PqxdhPhase2InputBytes.ciphertext
      (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1)) = some encapsulated.2 := by
    rw [(PqxdhPhase2InputBytes.ciphertext_roundtrip (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1)
      encapsulated.1).2]
    exact not_not.mp good
  have hbody : ∀ key nonce ad : Pqxdh.Bytes, (setup.source.crypto.aeadSeal key nonce ad
      (Pqxdh.LE64 controlKeyId.val ++ payload)).1 ≠ [] := by
    intro key nonce ad empty
    have := laws.bodyLength key nonce ad (Pqxdh.LE64 controlKeyId.val ++ payload)
    rw [empty, List.length_append, Pqxdh.LE64_length] at this
    simp at this
  have hinput := beacon_input_eq setup laws.nonzero seed scalar beaconSeed oneTime e response
    (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1) controlKeyId encapsulated.2 keys.1
  rw [hcb] at hinput
  obtain ⟨beacon', family', hfinish⟩ := beacon_finish setup codec functional laws.nonzero seed scalar beaconSeed
    oneTime e keys.2 phase2 response (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1) controlKeyId
    encapsulated.2 hread hct heph hsid hid hdecap frameBytes _ _ _ payload second.1.1 happ hne hdecode rfl rfl rfl
    (hbody _ _ _) nonempty bytes0 first'.1.1 second.2 hinput (by rw [hfamily2]; exact hprk) rfl second.1.2
    (by rw [hstate2, hstate1]; rfl) (by rw [hstate2]; exact hcache2)
  rw [runAdversary_query] at finishRun
  change third ∈ support ((simulateQ (romReduction setup seed scalar)
    ((PqxdhServerAuthExperiment.finishOracle setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed phase2).run second.1.2)).run second.2) at finishRun
  rw [hfinish, support_pure, Set.mem_singleton_iff] at finishRun
  subst supported
  subst finishRun
  have hghost : second.1.2.ghost = ⟨[.adversary bytes0], [], none⟩ := by
    rw [hstate2, hstate1]
    rfl
  refine ⟨_, by simp only [hghost]; rfl, fun index partner => ?_⟩
  obtain ⟨message, reply, _, member, _⟩ := partner
  simp [] at member

set_option linter.deprecated false in
/-- The experiment's success probability is the probability of the winning event. -/
theorem game_win (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    Pr[= true | expGame setup codec checks revealSeed adversary] =
      Pr[fun result => Win setup result.1 result.2.1 result.2.2.1.ghost |
        gameState setup codec checks revealSeed adversary] := by
  classical
  rw [expGame, ← probEvent_eq_eq_probOutput, probEvent_map]
  congr 1
  funext result
  simp only [Function.comp_apply, decide_eq_true_eq]

set_option linter.deprecated false in
/-- Lower KEM split: if, for every sampled Beacon key pair, the adversary's run misses an event with probability at most the key pair's correctness error, then the event has probability at least one minus the KEM correctness error. -/
theorem kem_lower (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (event : IdentitySeed → ScalarBytes → GameState KemSK → Prop)
    (bound : ∀ seed scalar beaconSeed oneTime keys, keys ∈ support (keygenRun setup) →
      Pr[fun result => ¬ event seed scalar result.1.2 | runAdversary setup codec checks seed scalar beaconSeed
        (adversary (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 (if revealSeed then some seed else none)))
        (initial setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2)
        PqxdhJointDhExtractFamily.empty] ≤ keyPairError setup functional keys) :
    1 - kemError setup ≤ (Pr[fun result => event result.1 result.2.1 result.2.2.1 |
      gameState setup codec checks revealSeed adversary]).toReal := by
  have split := kem_split setup codec checks revealSeed adversary functional
    (fun seed scalar state => ¬ event seed scalar state) bound
  have total := probEvent_compl (gameState setup codec checks revealSeed adversary)
    (fun result => event result.1 result.2.1 result.2.2.1)
  simp only [probFailure_eq_zero, tsub_zero] at total
  rw [kemError]
  have eventEq := ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) total
  have missLe : Pr[fun result => ¬ event result.1 result.2.1 result.2.2.1 |
      gameState setup codec checks revealSeed adversary] ≤ 1 := probEvent_le_one
  rw [eventEq, ENNReal.toReal_sub_of_le missLe ENNReal.one_ne_top, ENNReal.toReal_one]
  have mono := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one) split
  linarith

set_option linter.deprecated false in
/-- Negative control (gate B5a): with the Server seed revealed, the control adversary, which never queries the Server, makes the Beacon accept without any partner session (the event `W1`) with probability at least one minus the KEM correctness error. -/
theorem negative_control (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (limit : Nat) (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload : Pqxdh.Bytes) (nonempty : payload ≠ []) (short : payload.length + 88 < limit) :
    1 - kemError setup ≤ (Pr[fun result => PqxdhServerAuthExperiment.W1 setup result.1 result.2.1 result.2.2.1.ghost |
      gameState setup codec checks true (controlAdversary setup codec payload)]).toReal :=
  kem_lower setup codec checks true (controlAdversary setup codec payload) functional
    (fun seed scalar state => PqxdhServerAuthExperiment.W1 setup seed scalar state.ghost)
    (fun seed scalar beaconSeed oneTime keys _ =>
      control_bound setup codec checks limit laws functional payload nonempty short seed scalar beaconSeed oneTime keys)

set_option linter.deprecated false in
/-- The negative control in the form of the experiment's success probability: since `W1` implies `Win`, the control adversary wins the experiment with probability at least one minus the KEM correctness error. -/
theorem negative_control_win (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (limit : Nat) (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload : Pqxdh.Bytes) (nonempty : payload ≠ []) (short : payload.length + 88 < limit) :
    1 - kemError setup ≤ (Pr[= true | expGame setup codec checks true (controlAdversary setup codec payload)]).toReal :=
  (negative_control setup codec checks limit laws functional payload nonempty short).trans (by
    rw [game_win]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one)
      (probEvent_mono fun _ _ w1 => Or.inl w1))

/-! ## The Server's honest accept -/

/-- The Server's attached verification accepts the Beacon's honest signatures. -/
theorem server_verify (setup : Setup baseSpec KemSK) (beaconSeed : IdentitySeed) (message : Pqxdh.Bytes) :
    setup.source.crypto.verify (setup.joint.publicKeys beaconSeed).ed25519.toList
      (PqxdhEd25519EufCma.attachSignature (setup.joint.sign beaconSeed message) message) = some message := by
  rw [setup.wiring.attachedSign, setup.wiring.edPublic, setup.source.crypto.verify_sign]

/-- The typed verified Phase 1 of the target Beacon, as the Server reads it. -/
def honestVerified (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (reader : Reader) :
    PqxdhServerRootPreparation.Verified Reader :=
  ⟨reader, beaconCandidate setup publicValue beaconSeed oneTime kemPk, (setup.joint.publicKeys beaconSeed).ed25519,
    ⟨publicValue.prekey, setup.dh.publicKey oneTime, kemPk⟩⟩

/-- The Server's collected inputs for the target Beacon's Phase 1, an ephemeral and an encapsulation. -/
def honestInputs (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (reader : Reader) (e : ScalarBytes)
    (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret) :
    PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding :=
  ⟨honestVerified setup publicValue beaconSeed oneTime kemPk reader, ⟨e, rootArray (setup.dh.publicKey e)⟩,
    PqxdhAcceptedRegistration.ciphertextArray encapsulated.1,
    rootArray (setup.joint.publicKeys beaconSeed).convertedX25519, publicValue.prekey,
    rootArray (dhValue setup.source.crypto e (setup.joint.publicKeys beaconSeed).convertedX25519.toList),
    rootArray (dhValue setup.source.crypto e publicValue.prekey.toList),
    rootArray (dhValue setup.source.crypto e (setup.dh.publicKey oneTime).toList), rootArray encapsulated.2⟩

/-- Running a state computation given as a function applies it. -/
theorem run_lambda {σ α : Type} (work : σ → ProbComp (α × σ)) (state : σ) :
    StateT.run (m := ProbComp) (fun current => work current) state = work state :=
  rfl

/-- Binding after a state read that leaves the state unchanged. -/
theorem lambda_bind {σ α β : Type} (read : σ → α) (next : α → StateT σ ProbComp β) :
    ((fun state => pure (read state, state)) : StateT σ ProbComp α) >>= next = fun state => next (read state) state := by
  funext state
  change (StateT.run ((fun state => pure (read state, state)) >>= next) state) = _
  rw [StateT.run_bind]
  exact pure_bind _ _

/-- Binding after a lifted probabilistic step, applied to a state. -/
theorem lift_bind_apply {σ α β : Type} (work : ProbComp α) (next : α → StateT σ ProbComp β) (state : σ) :
    (StateT.lift work >>= next) state = work >>= fun value => next value state := by
  change StateT.run (StateT.lift work >>= next) state = _
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  simp only [pure_bind]
  rfl

/-- The public conversion of the target Beacon's identity, as the Server computes it. -/
theorem beacon_conversion (setup : Setup baseSpec KemSK) (beaconSeed : IdentitySeed) :
    (setup.source.crypto.xpkConv (setup.joint.publicKeys beaconSeed).ed25519.toList).bind
      PqxdhServerAuthExperiment.toWord32 = some (rootArray (setup.joint.publicKeys beaconSeed).convertedX25519) := by
  rw [jointPublic_conversion setup.source.crypto setup.joint setup.secretOfSeed setup.wiring beaconSeed]
  simp [PqxdhServerAuthExperiment.toWord32]

/-- The Server's public static-DH domain accepts an honest prekey. -/
theorem server_accepts (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (seed : IdentitySeed)
    (scalar : ScalarBytes) : setup.serverDomain.accepts (setup.dh.publicKey scalar) = true := by
  rw [← setup.serverDomain.available seed]
  obtain ⟨value, present⟩ := static_present setup nonzero seed scalar
  rw [present]
  rfl

/-- The Server's ephemeral DH with an honest public key. -/
theorem ephemeral_public (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (e other : ScalarBytes) :
    sourceScalarDh setup.source.crypto e (setup.dh.publicKey other) =
      some (dhValue setup.source.crypto e (setup.dh.publicKey other).toList) :=
  sourceScalarDh_some _ _ _ (by exact nonzero _ _)

/-- The Server's ephemeral DH with the converted Beacon identity. -/
theorem ephemeral_identity (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto) (e : ScalarBytes)
    (beaconSeed : IdentitySeed) :
    sourceScalarDh setup.source.crypto e (setup.joint.publicKeys beaconSeed).convertedX25519 =
      some (dhValue setup.source.crypto e (setup.joint.publicKeys beaconSeed).convertedX25519.toList) :=
  sourceScalarDh_some _ _ _ (by rw [setup.wiring.xPublic]; exact nonzero _ _)

/-- The Server's Phase 1 prefix on the target Beacon's Phase 1. -/
theorem serverPrefix_honest (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (bytes : Pqxdh.Bytes) (reader : Reader)
    (hread : codec.read1 bytes = some reader)
    (hidentity : codec.identity reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).identityKey)
    (hpq : codec.pqField reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).pqKey)
    (hpre : codec.preField reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).preKey)
    (hone : codec.oneField reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).oneTimeKey)
    (h1 : checks.identityPoint (setup.joint.publicKeys beaconSeed).ed25519 = true)
    (h2 : checks.reserveRegistration = true)
    (h3 : checks.x25519Point (rootArray (setup.dh.publicKey scalar)) = true)
    (h4 : checks.x25519Point (rootArray (setup.dh.publicKey oneTime)) = true)
    (h5 : checks.kemKey kemPk = true) :
    (PqxdhServerAuthExperiment.serverPrefix setup codec checks bytes).run [] =
      PqxdhJointGapDh.sampleScalar >>= fun e =>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps kemPk) >>= fun enc =>
          pure (some (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed
            oneTime kemPk reader e enc), []) := by
  simp only [PqxdhServerAuthExperiment.serverPrefix, PqxdhServerRootPreparation.collect,
    PqxdhServerRootPreparation.verifyInput, PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, simulateQ_map,
    PqxdhServerStaticDhSource.prefixImpl, PqxdhServerAuthExperiment.serverAux, 
    run_lambda, pure_bind, hread, hidentity, hpq, hpre, hone,
    beaconCandidate, PqxdhJointPhase1SourceWriter.candidate, PqxdhEd25519EufCma.parseIdentity_encodedIdentity,
    server_verify, h1, h2, h3, h4, h5, Bool.not_true, Bool.false_eq_true, List.not_mem_nil,
    Option.elim_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage, PqxdhEd25519EufCma.parseOneTimeMessage_oneTimeMessage,
    PqxdhEd25519EufCma.parsePqMessage_pqMessage, PqxdhServerRootPreparation.registrationId,
    PqxdhJointGapDh.challenge, lambda_bind, lift_bind_apply,
    PqxdhServerAuthExperiment.generateEphemeral, PqxdhServerAuthExperiment.encapsulate, bind_assoc,
    beacon_conversion, PqxdhServerStaticDhSource.selectedReply, peer_rootArray, server_accepts setup nonzero seed,
    ephemeral_public setup nonzero, ephemeral_identity setup nonzero, Option.map_some, ↓reduceIte]
  rfl

/-- The Server's Phase 1 prefix on the target Beacon's Phase 1, for every outcome of the admission checks: it answers nothing unless the identity, reservation and two point checks pass; then it draws the ephemeral, and it encapsulates and answers the honest inputs exactly when the ML-KEM key check passes. -/
theorem serverPrefix_eq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (bytes : Pqxdh.Bytes) (reader : Reader)
    (hread : codec.read1 bytes = some reader)
    (hidentity : codec.identity reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).identityKey)
    (hpq : codec.pqField reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).pqKey)
    (hpre : codec.preField reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).preKey)
    (hone : codec.oneField reader = some (beaconCandidate setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk).oneTimeKey) :
    (PqxdhServerAuthExperiment.serverPrefix setup codec checks bytes).run [] =
      if (checks.identityPoint (setup.joint.publicKeys beaconSeed).ed25519 && checks.reserveRegistration &&
          checks.x25519Point (rootArray (setup.dh.publicKey scalar)) &&
          checks.x25519Point (rootArray (setup.dh.publicKey oneTime))) = true then
        PqxdhJointGapDh.sampleScalar >>= fun e =>
          if checks.kemKey kemPk = true then
            simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps kemPk) >>= fun enc =>
              pure (some (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed
                oneTime kemPk reader e enc), [])
          else pure (none, [])
      else pure (none, []) := by
  cases h1 : checks.identityPoint (setup.joint.publicKeys beaconSeed).ed25519
  · simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    simp only [h1, Bool.not_false, PqxdhServerAuthExperiment.serverPrefix, PqxdhServerRootPreparation.collect,
    PqxdhServerRootPreparation.verifyInput, PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, 
    PqxdhServerStaticDhSource.prefixImpl, PqxdhServerAuthExperiment.serverAux, 
    run_lambda, pure_bind, hread, hidentity, 
    beaconCandidate, PqxdhJointPhase1SourceWriter.candidate, PqxdhEd25519EufCma.parseIdentity_encodedIdentity,
    
    Option.elim_some, Option.bind_eq_bind, Option.pure_def,
    
    PqxdhServerRootPreparation.registrationId,
    PqxdhJointGapDh.challenge, 
    bind_assoc,
    
    ↓reduceIte]
    rfl
  cases h2 : checks.reserveRegistration
  · simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false]
    simp only [h1, h2, Bool.not_false, PqxdhServerAuthExperiment.serverPrefix, PqxdhServerRootPreparation.collect,
    PqxdhServerRootPreparation.verifyInput, PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, 
    PqxdhServerStaticDhSource.prefixImpl, PqxdhServerAuthExperiment.serverAux, 
    run_lambda, pure_bind, hread, hidentity, hpq, hpre, hone,
    beaconCandidate, PqxdhJointPhase1SourceWriter.candidate, PqxdhEd25519EufCma.parseIdentity_encodedIdentity,
    server_verify, Bool.not_true, Bool.false_eq_true, List.not_mem_nil,
    Option.elim_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage, PqxdhEd25519EufCma.parseOneTimeMessage_oneTimeMessage,
    PqxdhEd25519EufCma.parsePqMessage_pqMessage, PqxdhServerRootPreparation.registrationId,
    PqxdhJointGapDh.challenge, lambda_bind, OptionT.run_failure,
    bind_assoc,
    
    ↓reduceIte]
    rfl
  cases h3 : checks.x25519Point (rootArray (setup.dh.publicKey scalar))
  · simp only [Bool.true_and, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false]
    simp only [h1, h2, h3, Bool.not_false, PqxdhServerAuthExperiment.serverPrefix, PqxdhServerRootPreparation.collect,
    PqxdhServerRootPreparation.verifyInput, PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, 
    PqxdhServerStaticDhSource.prefixImpl, PqxdhServerAuthExperiment.serverAux, 
    run_lambda, pure_bind, hread, hidentity, hpq, hpre, hone,
    beaconCandidate, PqxdhJointPhase1SourceWriter.candidate, PqxdhEd25519EufCma.parseIdentity_encodedIdentity,
    server_verify, Bool.not_true, Bool.false_eq_true, List.not_mem_nil,
    Option.elim_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage, PqxdhEd25519EufCma.parseOneTimeMessage_oneTimeMessage,
    PqxdhEd25519EufCma.parsePqMessage_pqMessage, PqxdhServerRootPreparation.registrationId,
    PqxdhJointGapDh.challenge, lambda_bind, OptionT.run_failure,
    bind_assoc,
    
    ↓reduceIte]
    rfl
  cases h4 : checks.x25519Point (rootArray (setup.dh.publicKey oneTime))
  · simp only [Bool.true_and, Bool.and_false, Bool.false_eq_true, ite_false]
    simp only [h1, h2, h3, h4, Bool.not_false, PqxdhServerAuthExperiment.serverPrefix, PqxdhServerRootPreparation.collect,
    PqxdhServerRootPreparation.verifyInput, PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, 
    PqxdhServerStaticDhSource.prefixImpl, PqxdhServerAuthExperiment.serverAux, 
    run_lambda, pure_bind, hread, hidentity, hpq, hpre, hone,
    beaconCandidate, PqxdhJointPhase1SourceWriter.candidate, PqxdhEd25519EufCma.parseIdentity_encodedIdentity,
    server_verify, Bool.not_true, Bool.false_eq_true, List.not_mem_nil,
    Option.elim_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage, PqxdhEd25519EufCma.parseOneTimeMessage_oneTimeMessage,
    PqxdhEd25519EufCma.parsePqMessage_pqMessage, PqxdhServerRootPreparation.registrationId,
    PqxdhJointGapDh.challenge, lambda_bind, OptionT.run_failure,
    bind_assoc,
    
    ↓reduceIte]
    rfl
  cases h5 : checks.kemKey kemPk
  · simp only [Bool.and_true, ite_true, Bool.false_eq_true, ite_false]
    simp only [h1, h2, h3, h4, h5, Bool.not_false, PqxdhServerAuthExperiment.serverPrefix, PqxdhServerRootPreparation.collect,
    PqxdhServerRootPreparation.verifyInput, PqxdhServerRootPreparation.collectVerified, OptionT.run_bind,
    OptionT.run_mk, OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, 
    PqxdhServerStaticDhSource.prefixImpl, PqxdhServerAuthExperiment.serverAux, 
    run_lambda, pure_bind, hread, hidentity, hpq, hpre, hone,
    beaconCandidate, PqxdhJointPhase1SourceWriter.candidate, PqxdhEd25519EufCma.parseIdentity_encodedIdentity,
    server_verify, Bool.not_true, Bool.false_eq_true, List.not_mem_nil,
    Option.elim_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    PqxdhEd25519EufCma.parsePrekeyMessage_prekeyMessage, PqxdhEd25519EufCma.parseOneTimeMessage_oneTimeMessage,
    PqxdhEd25519EufCma.parsePqMessage_pqMessage, PqxdhServerRootPreparation.registrationId,
    PqxdhJointGapDh.challenge, lambda_bind, lift_bind_apply, OptionT.run_failure,
    PqxdhServerAuthExperiment.generateEphemeral, bind_assoc,
    
    ↓reduceIte]
    rfl
  · simp only [Bool.and_true, ite_true]
    exact serverPrefix_honest setup codec checks nonzero seed scalar beaconSeed oneTime kemPk bytes reader hread
      hidentity hpq hpre hone h1 h2 h3 h4 h5

open PqxdhServerAuthExperiment (sessionImpl binding) in
/-- The part of the Server's accept after its Phase 1 prefix, as in `acceptOracle`. -/
noncomputable def acceptAfter (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (state : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) × List Pqxdh.Bytes) :
    PqxdhServerAuthExperiment.Game KemSK (Option Nat) := do
  set { state with sessions := state.sessions + 1, server := { state.server with consumed := collected.2 } }
  match collected.1 with
  | none => pure none
  | some input =>
      let returned ← simulateQ (sessionImpl state.sessions)
        (PqxdhServerRelatedRootConsumer.client (binding setup publicValue) input)
      match returned with
      | .ok (some token) => do
          modify fun current => { current with pending := Function.update current.pending state.sessions (some token) }
          pure (some state.sessions)
      | _ => pure none

/-- The Server's accept runs its Phase 1 prefix and then `acceptAfter`. -/
theorem run_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    runAdversary setup codec checks seed scalar beaconSeed (liftM (ExpSpec.query (.inr (.accept raw)))) state family =
      (PqxdhServerAuthExperiment.serverPrefix setup codec checks raw).run state.server.consumed >>= fun collected =>
        (simulateQ (romReduction setup seed scalar) ((acceptAfter setup
          (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) state collected).run state)).run family := by
  rw [runAdversary_query]
  change (simulateQ (romReduction setup seed scalar) ((PqxdhServerAuthExperiment.acceptOracle setup codec checks
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) raw).run state)).run family = _
  simp only [PqxdhServerAuthExperiment.acceptOracle, StateT.run_bind, StateT.run_get, pure_bind, liftCoins,
    StateT.run_lift, bind_assoc, simulateQ_bind]
  simp only [romReduction]
  rw [rom_coins, bind_map_left]
  simp only [acceptAfter, StateT.run_bind, simulateQ_bind]
  rfl

open PqxdhServerAuthExperiment (sessionImpl sessionFamily binding forwardFamily recordTouch) in
/-- After an honest collection, the accept derives the root through one Extract-table read, logs the session's touch with the root, consumes the registration ID and stores the pending token. -/
theorem acceptAfter_honest (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (consumed : List Pqxdh.Bytes)
    (bytes : Pqxdh.Bytes)
    (hinput : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar
      (PqxdhServerRelatedRootInput.message input) = some bytes)
    (nonzeroInput : PqxdhServerRelatedRootInput.localNonzero input)
    (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    (simulateQ (romReduction setup seed scalar) ((acceptAfter setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) state (some input, consumed)).run state)).run
        family =
      (HmacOracle.randomOracle bytes).run family.cache >>= fun answer =>
        pure ((some state.sessions, { state with
          sessions := state.sessions + 1
          server := { state.server with consumed := consumed ++
            [absBytes (PqxdhServerClearedRoot.pending (binding setup
              (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) input).registration_id.bytes] }
          pending := Function.update state.pending state.sessions
            (some ⟨expandRoot setup.hmac answer.1, PqxdhServerClearedRoot.pending (binding setup
              (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) input⟩)
          ghost := { state.ghost with touches := state.ghost.touches ++
            [.session state.sessions (PqxdhServerRelatedRootInput.message input)
              (some (expandRoot setup.hmac answer.1))] } }),
          (⟨family.history ++ [.derive (PqxdhServerRelatedRootInput.message input) (some answer.1),
            .publicHmac answer.1 rootExpandInput (setup.hmac.eval answer.1 rootExpandInput)], answer.2⟩ :
              PqxdhJointDhExtractFamily.State)) := by
  classical
  simp only [acceptAfter, PqxdhServerRelatedRootConsumer.client, nonzeroInput, not_true_eq_false, ite_false,
    simulateQ_bind, simulateQ_spec_query, sessionImpl, sessionFamily, forwardFamily, recordTouch,
    StateT.run_bind, StateT.run_set, StateT.run_modify, StateT.run_lift, pure_bind, bind_assoc]
  rw [PqxdhExtractRomFamily.rom_root]
  simp only [hinput, bind_map_left, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, sessionImpl,
    StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc]
  refine bind_congr fun answer => ?_
  rfl

/-! ## The Server's build -/

/-- The seal primitives of the Server's native tail. -/
noncomputable def sealHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl RawCtxSourceSeal.SealSpec
      (StateT (RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) ProbComp) :=
  (PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite
    (PqxdhServerAuthExperiment.tailAux codec checks) ∘ₛ
      fun request => liftM ((PqxdhServerRegistrationPublication.NativeSpec).query (.inl request))) ∘ₛ
    RawCtxSourceSeal.sealLift

/-- The Server's AEAD seal is the functional AEAD. -/
theorem sealHandler_aead (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (input : RawCtxSourceSeal.AeadInput)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (sealHandler setup codec checks (.inl input)).run state =
      pure (some (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext), state) := by
  simp only [sealHandler, QueryImpl.apply_compose, RawCtxSourceSeal.sealLift, simulateQ_spec_query,
    PqxdhRegistrationProtocolState.registrationImpl, QueryImpl.apply_compose, RawCtxMixedOwner.sendLift,
    RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, simulateQ_pure, StateT.run_pure]

/-- The Server's commitment hash is the BLAKE2b random oracle on the shared cache. -/
theorem sealHandler_hash (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (bytes : Pqxdh.Bytes) (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (sealHandler setup codec checks (.inr (.inl bytes))).run state = (do
      let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2
      pure (some result.1.toList, (state.1, result.2))) := by
  simp only [sealHandler, QueryImpl.apply_compose, RawCtxSourceSeal.sealLift, simulateQ_spec_query,
    PqxdhRegistrationProtocolState.registrationImpl, QueryImpl.apply_compose, RawCtxMixedOwner.sendLift]
  exact RawCtxMixedShared.shared_hash _ _ _ bytes state

/-- The Server's frame writer is the codec's. -/
theorem sealHandler_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (frame : RawCtxReceive.DecodedFrame)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (sealHandler setup codec checks (.inr (.inr frame))).run state = pure (codec.frameWrite frame, state) := by
  simp only [sealHandler, QueryImpl.apply_compose, RawCtxSourceSeal.sealLift, simulateQ_spec_query,
    PqxdhRegistrationProtocolState.registrationImpl, QueryImpl.apply_compose, RawCtxMixedOwner.sendLift,
    RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, simulateQ_pure, StateT.run_pure]

/-- A successful sequence-one seal of the logging tail: the AEAD body and tag, a cached commitment and the frame writer's bytes; the seal context is logged. -/
theorem tail_seal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (input : RawCtxSourceSend.SealInput) (log : List RawCtxSourceSend.SealContext) (cache : CtxRomAuth.CtxRO.QueryCache)
    (result : Option Pqxdh.Bytes × RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((PqxdhServerAuthExperiment.tailImpl setup codec checks (.inl (.inr input))).run
      (log, cache))) (ciphertext : Pqxdh.Bytes) (present : result.1 = some ciphertext) :
    ∃ digest : CtxRomAuth.CtxDigest,
      result.2.2 ((), RawCtxSourceSeal.hashInput input
        (setup.source.crypto.aeadSeal (RawCtxSourceSeal.aeadInput input).key (RawCtxSourceSeal.aeadInput input).nonce
          (RawCtxSourceSeal.aeadInput input).associatedData (RawCtxSourceSeal.aeadInput input).plaintext).2) = some digest ∧
      codec.frameWrite (RawCtxSourceSeal.frame input
        (setup.source.crypto.aeadSeal (RawCtxSourceSeal.aeadInput input).key (RawCtxSourceSeal.aeadInput input).nonce
          (RawCtxSourceSeal.aeadInput input).associatedData (RawCtxSourceSeal.aeadInput input).plaintext).1
        (setup.source.crypto.aeadSeal (RawCtxSourceSeal.aeadInput input).key (RawCtxSourceSeal.aeadInput input).nonce
          (RawCtxSourceSeal.aeadInput input).associatedData (RawCtxSourceSeal.aeadInput input).plaintext).2
        digest.toList) = some ciphertext ∧
      result.2.1 = log ++ [input.context] := by
  simp only [PqxdhServerAuthExperiment.tailImpl, PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxSourceSeal.nativeAdapter, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨sealed, sealedRun, rest⟩ := supported
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at sealedRun
  change sealed ∈ support ((simulateQ (sealHandler setup codec checks) (RawCtxSourceSeal.sealInput input)).run
    (log, cache)) at sealedRun
  rcases sealed with ⟨_ | sealedBytes, afterSeal⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ite_false, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at rest
    rw [rest] at present
    cases present
  simp only [Option.isSome_some, ite_true, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at rest
  subst rest
  simp only [Option.some.injEq] at present
  subst present
  obtain ⟨body, tag, afterAead, commitment, afterHash, aeadRun, _, _, hashRun, frameRun⟩ :=
    RawCtxSourceSeal.sealInput_success (sealHandler setup codec checks) input (log, cache) afterSeal sealedBytes
      sealedRun
  rw [sealHandler_aead, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at aeadRun
  obtain ⟨sealedEq, rfl⟩ := aeadRun
  rw [sealHandler_hash, mem_support_bind_iff] at hashRun
  obtain ⟨answer, answerRun, hashEq⟩ := hashRun
  rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hashEq
  obtain ⟨rfl, rfl⟩ := hashEq
  rw [sealHandler_frame, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at frameRun
  obtain ⟨frameEq, rfl⟩ := frameRun
  refine ⟨answer.1, ?_, ?_, rfl⟩
  · rw [← sealedEq]
    exact randomOracle_cached (spec := CtxRomAuth.CtxRO) _ _ _ answerRun
  · rw [← sealedEq]
    exact frameEq.symm

/-- A KDF request of the logging tail is the fixed source response, with the state unchanged. -/
theorem tailImpl_kdf_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (request : ratchet.SymmetricRatchetKdfRequest)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (PqxdhServerAuthExperiment.tailImpl setup codec checks (.inl (.inl request))).run state =
      pure (RawCtxSourceHkdf.response setup.source.crypto request, state) := by
  change (PqxdhServerAuthExperiment.nativeTail setup codec checks (.inl (.inl request))).run state = _
  simp only [PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxSourceSeal.nativeAdapter, simulateQ_spec_query,
    PqxdhRegistrationProtocolState.registrationImpl, RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedImpl,
    RawCtxMixedShared.sharedAdapter]
  exact RawCtxSourceHkdf.kdf_step setup.source request state

/-- The sequence-one material of the Server's initial kernel is the chain material of its send chain. -/
theorem send_material (c : Pqxdh.Crypto) (pending : ratchet.concrete.SendKdf RawCtxSourceSend.SealContext)
    (chain : ratchet.RatchetChain) (hinput : pending.request.input = chain.bytes)
    (hinfo : pending.request.info = ratchet.SYM_RATCHET_INFO) :
    (RawCtxSourceSend.resumeSend pending (RawCtxSourceHkdf.response c pending.request)).material =
      chainMaterial c chain := by
  obtain ⟨stepped, hstep, hready⟩ := RawCtxSourceSend.resumeSend_fields pending (RawCtxSourceHkdf.response c pending.request)
  have hrequest : pending.request = ⟨chain.bytes, ratchet.SYM_RATCHET_INFO⟩ := by
    cases hreq : pending.request
    simp only [hreq] at hinput hinfo
    rw [hinput, hinfo]
  have hspec := ratchet.concrete.interpretedStep_spec (sourceKdf c) chain
  rw [ratchet.concrete.interpretedResponse] at hspec
  rw [hrequest] at hstep
  have same := RustM.ok.inj (hstep.symm.trans hspec)
  rw [hready]
  simp only [chainMaterial, ← same]

/-- The Server's first send under the logging tail: a produced record carries the sequence-one seal, under the chain material of the initial kernel's send chain, with its commitment cached, and the seal context is logged. -/
theorem tail_send (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (root : RootOutput) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (hkernel : PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel)
    (context : RawCtxSourceSend.SealContext) (log : List RawCtxSourceSend.SealContext)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (sent : (ratchet.concrete.ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : sent ∈ support ((simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
      (simulateQ PqxdhServerRegistrationPublication.sendLift (simulateQ RawCtxSourceSend.adapter
        (RawCtxSourceSend.send kernel context)))).run (log, cache)))
    (encrypted : RawCtxSourceSend.Encrypted) (present : sent.1.2 = some encrypted) :
    ∃ digest : CtxRomAuth.CtxDigest,
      encrypted = RawCtxSourceSend.encrypted ⟨chainMaterial setup.source.crypto kernel.refined.send_chain, 1#u64,
        context⟩ encrypted.ciphertext ∧
      sent.2.2 ((), RawCtxSourceSeal.hashInput ⟨chainMaterial setup.source.crypto kernel.refined.send_chain, 1#u64,
        context⟩ (setup.source.crypto.aeadSeal
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).1
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).2
          context.associatedData context.plaintext).2) = some digest ∧
      codec.frameWrite (RawCtxSourceSeal.frame ⟨chainMaterial setup.source.crypto kernel.refined.send_chain, 1#u64,
        context⟩ (setup.source.crypto.aeadSeal
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).1
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).2
          context.associatedData context.plaintext).1
        (setup.source.crypto.aeadSeal
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).1
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).2
          context.associatedData context.plaintext).2 digest.toList) = some encrypted.ciphertext ∧
      sent.2.1 = log ++ [context] := by
  obtain ⟨initial, hrun, _, _, refines⟩ :=
    PqxdhRootTableInitialization.initialize_refines setup.source PqxdhServerAuthExperiment.unitRatchet false root
  have same : initial = kernel := RustM.ok.inj (hrun.symm.trans hkernel)
  subst same
  have hzero := refines.sendSequence
  have hmax : initial.refined.control.send_sequence ≠ core.num.U64.MAX := by
    intro h
    have hv := congrArg UScalar.val h
    simp only [hzero] at hv
    contradiction
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at supported
  obtain ⟨pending, hbegin, _, hcontext, hinput, hinfo, _, hnext, _, _⟩ :=
    RawCtxSourceSend.beginSend_fields initial context hmax
  rw [RawCtxSourceSend.send, hbegin] at supported
  obtain ⟨response, afterKdf, reply, afterSeal, hkdf, hseal, hsent⟩ :=
    RawCtxSourceSend.requested_support _ pending (log, cache) sent supported
  simp only [QueryImpl.apply_compose, RawCtxSourceSend.adapter, PqxdhServerRegistrationPublication.sendLift,
    simulateQ_spec_query] at hkdf
  rw [tailImpl_kdf_run, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hkdf
  obtain ⟨hresponse, hafter⟩ := hkdf
  have hresponse' : response = RawCtxSourceHkdf.response setup.source.crypto pending.request := hresponse
  subst hresponse' hafter hsent
  have hsequence : pending.sequence = 1#u64 := by
    apply UScalar.eq_of_val_eq
    rw [hnext, hzero]
    rfl
  have hargs : RawCtxSourceSend.arguments (RawCtxSourceSend.resumeSend pending
      (RawCtxSourceHkdf.response setup.source.crypto pending.request)) =
      ⟨chainMaterial setup.source.crypto initial.refined.send_chain, 1#u64, context⟩ := by
    obtain ⟨stepped, _, hready⟩ := RawCtxSourceSend.resumeSend_fields pending
      (RawCtxSourceHkdf.response setup.source.crypto pending.request)
    have hmaterial := send_material setup.source.crypto pending initial.refined.send_chain hinput hinfo
    simp only [RawCtxSourceSend.arguments]
    rw [hmaterial]
    rw [hready]
    simp only [hsequence, hcontext]
  simp only [QueryImpl.apply_compose, RawCtxSourceSend.adapter, PqxdhServerRegistrationPublication.sendLift,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff, hargs] at hseal
  obtain ⟨sealed, sealedRun, hpair⟩ := hseal
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hreply, rfl⟩ := hpair
  rw [hreply] at present
  cases hsealed : sealed.1 with
  | none => rw [hsealed] at present; cases present
  | some ciphertext =>
      rw [hsealed, Option.map_some, Option.some.injEq] at present
      subst present
      obtain ⟨digest, hcache, hframe, hlog⟩ := tail_seal setup codec checks _ log cache sealed sealedRun ciphertext
        hsealed
      rw [hargs] at hcache hframe hlog
      exact ⟨digest, rfl, hcache, hframe, hlog⟩

/-- A prepared registration candidate carries the pending registration's fields, the current Server binding and the associated data of the Server and Beacon identities. -/
theorem prepare_commit_fields (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (current : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (prepared : pqxdh.server_prepare_commit state pending current availability = ok (.Ok candidate)) :
    candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = current.identity_public_key ∧
      candidate.server_identity_key_id = current.identity_key_id ∧
      candidate.ephemeral_public_key = pending.ephemeral_public_key ∧
      candidate.kem_ciphertext = pending.kem_ciphertext ∧
      pqxdh.build_associated_data current.identity_public_key pending.beacon_identity_public_key =
        ok candidate.associated_data := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state
  obtain ⟨ad, had⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok current.identity_public_key
    pending.beacon_identity_public_key
  simp only [pqxdh.server_prepare_commit, array_eq_abs, bind_tc_ok, hnext, had] at prepared
  split_ifs at prepared
  all_goals cases next
  all_goals cases availability
  all_goals simp_all
  subst prepared
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The logging tail's callbacks are the stateless tail callbacks. -/
theorem tailImpl_aux (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.AuxQuery)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (PqxdhServerAuthExperiment.tailImpl setup codec checks (.inr query)).run state =
      (PqxdhServerAuthExperiment.tailAux codec checks query).run state := by
  change (PqxdhServerAuthExperiment.nativeTail setup codec checks (.inr query)).run state = _
  simp only [PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, simulateQ_spec_query,
    PqxdhRegistrationProtocolState.registrationImpl]

/-- A published Server build: the candidate carries the pending registration and the Server's binding, the sequence-one record is sealed under the chain material of the initial kernel for the root with its commitment cached, the frame and Phase 2 are written, and the seal context is the only logged seal. -/
theorem build_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
        RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run ([], cache)))
    (response : PqxdhServerRegistrationPublication.Response)
    (published : (PqxdhServerAuthExperiment.settle server result.1).1 = some response) :
    ∃ (candidate : pqxdh.ServerRegistrationCandidate) (kernel : ratchet.concrete.ConcreteRatchetKernel)
      (digest : CtxRomAuth.CtxDigest) (frameBytes : Pqxdh.Bytes),
      candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = server.server.identity ∧
      candidate.server_identity_key_id = server.identityKeyId ∧
      candidate.ephemeral_public_key = pending.ephemeral_public_key ∧
      candidate.kem_ciphertext = pending.kem_ciphertext ∧
      pqxdh.build_associated_data server.server.identity pending.beacon_identity_public_key =
        ok candidate.associated_data ∧
      PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel ∧
      payload.getD PqxdhServerRegistrationPublication.registrationWitness ≠ [] ∧
      result.2.2 ((), RawCtxSourceSeal.hashInput ⟨chainMaterial setup.source.crypto kernel.refined.send_chain,
        1#u64, PqxdhServerRegistrationPublication.firstContext candidate (Pqxdh.LE64 candidate.key_id.val ++
          payload.getD PqxdhServerRegistrationPublication.registrationWitness)⟩
        (setup.source.crypto.aeadSeal (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).1
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).2
          (absBytes candidate.associated_data) (Pqxdh.LE64 candidate.key_id.val ++
            payload.getD PqxdhServerRegistrationPublication.registrationWitness)).2) = some digest ∧
      codec.frameWrite (RawCtxSourceSeal.frame ⟨chainMaterial setup.source.crypto kernel.refined.send_chain,
        1#u64, PqxdhServerRegistrationPublication.firstContext candidate (Pqxdh.LE64 candidate.key_id.val ++
          payload.getD PqxdhServerRegistrationPublication.registrationWitness)⟩
        (setup.source.crypto.aeadSeal (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).1
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).2
          (absBytes candidate.associated_data) (Pqxdh.LE64 candidate.key_id.val ++
            payload.getD PqxdhServerRegistrationPublication.registrationWitness)).1
        (setup.source.crypto.aeadSeal (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).1
          (absMaterial (chainMaterial setup.source.crypto kernel.refined.send_chain)).2
          (absBytes candidate.associated_data) (Pqxdh.LE64 candidate.key_id.val ++
            payload.getD PqxdhServerRegistrationPublication.registrationWitness)).2
        digest.toList) = some frameBytes ∧
      codec.write2 ⟨candidate.key_id, candidate.ephemeral_public_key, candidate.server_identity_public_key,
        candidate.kem_ciphertext, frameBytes⟩ = some response.serialized ∧
      result.2.1 = [PqxdhServerRegistrationPublication.firstContext candidate (Pqxdh.LE64 candidate.key_id.val ++
        payload.getD PqxdhServerRegistrationPublication.registrationWitness)] := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok server.control
  simp only [PqxdhServerRegistrationPublication.build, hnext, PqxdhServerRegistrationPublication.continueRust]
    at supported
  cases next with
  | Err error =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported] at published
      cases published
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        server.control pending ⟨server.server.identity, server.identityKeyId⟩
        (if (server.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
      simp only [hprepared] at supported
      cases prepared with
      | Err error =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          rw [supported] at published
          cases published
      | Ok candidate =>
          obtain ⟨hbeaconId, hserverId, hserverKey, heph, hkem, had⟩ :=
            prepare_commit_fields _ _ _ _ candidate hprepared
          obtain ⟨kernel, hrun, _, _, _⟩ :=
            PqxdhRootTableInitialization.initialize_refines setup.source PqxdhServerAuthExperiment.unitRatchet false root
          have hinit : BeaconcryptCore.Refinement.ServerTransactionRefinement.initializeCandidate candidate
              (rootArray root)
              (PqxdhRootTableInitialization.initialResponse setup.source.crypto) = ok kernel :=
            (PqxdhServerRegistrationPublication.candidate_initialization setup.source candidate root).trans hrun
          obtain ⟨binding, hbinding, hbytes⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
          simp only [PqxdhServerRegistrationPublication.candidateTail, hinit, hbinding,
            PqxdhServerRegistrationPublication.continueRust, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, mem_support_bind_iff, tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, rfl, supported⟩ := supported
          cases hvalid : checks.beaconIdentity candidate.beacon_identity_public_key
          · simp only [hvalid, Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published
          simp only [hvalid, Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, mem_support_bind_iff, tailImpl_aux, PqxdhServerAuthExperiment.tailAux, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, rfl, supported⟩ := supported
          cases hreserved : checks.reservePeer
          · simp only [hreserved, Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published
          simp only [hreserved, Bool.not_true, Bool.false_eq_true, ite_false] at supported
          by_cases empty : (payload.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
          · simp only [empty, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published
          simp only [empty, Bool.false_eq_true, ite_false] at supported
          split_ifs at supported with fits
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff, tailImpl_aux,
              PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
            obtain ⟨_, rfl, supported⟩ := supported
            cases hallocated : checks.reservePlaintext
                (8 + (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length)
            · simp only [hallocated, Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at supported
              rw [supported] at published
              cases published
            simp only [hallocated, Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
              support_map, Set.mem_image] at supported
            obtain ⟨inner, innerSupported, rfl⟩ := supported
            rw [hbytes] at innerSupported
            obtain ⟨sent, afterSend, afterErase, hsent, herase, rest⟩ :=
              PqxdhServerRegistrationPublication.afterInitialization_support _ candidate _ kernel () server
                ([], cache) inner innerSupported
            rw [tailImpl_aux] at herase
            simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq, true_and] at herase
            subst herase
            cases hs : sent.2 with
            | none =>
                rw [hs] at rest
                rw [rest] at published
                cases published
            | some encrypted =>
                rw [hs] at rest
                obtain ⟨written, afterWrite, hwritten, eq⟩ := rest
                rw [tailImpl_aux] at hwritten
                simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hwritten
                obtain ⟨rfl, rfl⟩ := hwritten
                subst eq
                cases hwrite : codec.write2 (PqxdhServerRegistrationPublication.responseFields candidate encrypted) with
                | none =>
                    simp only [hwrite, Option.map_none] at published
                    cases published
                | some bytes =>
                    simp only [hwrite, Option.map_some, Option.isSome_some, ite_true,
                      PqxdhServerAuthExperiment.settle, Option.some.injEq] at published
                    subst published
                    obtain ⟨digest, hencrypted, hcache, hframe, hlog⟩ := tail_send setup codec checks root kernel hrun
                      _ [] cache _ hsent encrypted hs
                    refine ⟨candidate, kernel, digest, encrypted.ciphertext, hbeaconId, hserverId, hserverKey, heph, hkem,
                      had, hrun, fun nil => by rw [nil] at empty; exact empty rfl, hcache, hframe, ?_, hlog⟩
                    exact hwrite
          · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
            rw [supported] at published
            cases published

/-! ## The Server's build publishes -/

/-- Under the control laws, the Server's seal of an input with 153-byte associated data and a plaintext at least 80 bytes shorter than the bound always produces a frame. -/
theorem seal_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (limit : Nat)
    (laws : ControlLaws setup codec limit) (input : RawCtxSourceSend.SealInput)
    (hAD : input.context.associatedData.length = 153) (short : input.context.plaintext.length + 80 < limit)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : Option Pqxdh.Bytes × RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((simulateQ (sealHandler setup codec checks)
      (RawCtxSourceSeal.sealInput input)).run state)) :
    result.1 ≠ none := by
  rw [RawCtxSourceSeal.sealInput_run, sealHandler_aead, pure_bind] at supported
  have hbody := laws.bodyLength (RawCtxSourceSeal.aeadInput input).key (RawCtxSourceSeal.aeadInput input).nonce
    (RawCtxSourceSeal.aeadInput input).associatedData (RawCtxSourceSeal.aeadInput input).plaintext
  have htag := setup.source.crypto.aeadSeal_tag_length (RawCtxSourceSeal.aeadInput input).key
    (RawCtxSourceSeal.aeadInput input).nonce (RawCtxSourceSeal.aeadInput input).associatedData
    (RawCtxSourceSeal.aeadInput input).plaintext
  generalize setup.source.crypto.aeadSeal (RawCtxSourceSeal.aeadInput input).key
    (RawCtxSourceSeal.aeadInput input).nonce (RawCtxSourceSeal.aeadInput input).associatedData
    (RawCtxSourceSeal.aeadInput input).plaintext = sealed at supported hbody htag
  obtain ⟨body, tag⟩ := sealed
  dsimp only at supported hbody htag
  simp only [hAD, htag, ↓reduceIte] at supported
  rw [sealHandler_hash, bind_assoc, mem_support_bind_iff] at supported
  obtain ⟨answer, _, supported⟩ := supported
  rw [pure_bind] at supported
  dsimp only at supported
  rw [sealHandler_frame, support_pure, Set.mem_singleton_iff] at supported
  rw [supported]
  refine frame_written laws _ ?_
  simp only [RawCtxSourceSeal.frame, List.length_append, hbody, htag, List.Vector.toList_length]
  simp only [RawCtxSourceSeal.aeadInput] at hbody ⊢
  omega

/-- Under the control laws, the logging tail's seal of an input with 153-byte associated data and a short plaintext always produces a frame. -/
theorem tail_seal_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (limit : Nat) (laws : ControlLaws setup codec limit) (input : RawCtxSourceSend.SealInput)
    (hAD : input.context.associatedData.length = 153) (short : input.context.plaintext.length + 80 < limit)
    (log : List RawCtxSourceSend.SealContext) (cache : CtxRomAuth.CtxRO.QueryCache)
    (result : Option Pqxdh.Bytes × RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((PqxdhServerAuthExperiment.tailImpl setup codec checks (.inl (.inr input))).run
      (log, cache))) :
    result.1 ≠ none := by
  simp only [PqxdhServerAuthExperiment.tailImpl, PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxSourceSeal.nativeAdapter, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨sealed, sealedRun, rest⟩ := supported
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at sealedRun
  change sealed ∈ support ((simulateQ (sealHandler setup codec checks) (RawCtxSourceSeal.sealInput input)).run
    (log, cache)) at sealedRun
  have written := seal_written setup codec checks limit laws input hAD short _ sealed sealedRun
  rcases sealed with ⟨_ | sealedBytes, afterSeal⟩
  · exact absurd rfl written
  simp only [Option.isSome_some, ite_true, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at rest
  rw [rest]
  exact Option.some_ne_none _

/-- Under the control laws, the Server's first send under the logging tail always produces a record when the seal context has 153-byte associated data and a short plaintext. -/
theorem send_written (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (limit : Nat) (laws : ControlLaws setup codec limit)
    (root : RootOutput) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (hkernel : PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel)
    (context : RawCtxSourceSend.SealContext) (hAD : context.associatedData.length = 153)
    (short : context.plaintext.length + 80 < limit) (log : List RawCtxSourceSend.SealContext)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (sent : (ratchet.concrete.ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : sent ∈ support ((simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
      (simulateQ PqxdhServerRegistrationPublication.sendLift (simulateQ RawCtxSourceSend.adapter
        (RawCtxSourceSend.send kernel context)))).run (log, cache))) :
    sent.1.2 ≠ none := by
  obtain ⟨initial, hrun, _, _, refines⟩ :=
    PqxdhRootTableInitialization.initialize_refines setup.source PqxdhServerAuthExperiment.unitRatchet false root
  have same : initial = kernel := RustM.ok.inj (hrun.symm.trans hkernel)
  subst same
  have hzero := refines.sendSequence
  have hmax : initial.refined.control.send_sequence ≠ core.num.U64.MAX := by
    intro h
    have hv := congrArg UScalar.val h
    simp only [hzero] at hv
    contradiction
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at supported
  obtain ⟨pending, hbegin, _, hcontext, hinput, hinfo, _, hnext, _, _⟩ :=
    RawCtxSourceSend.beginSend_fields initial context hmax
  rw [RawCtxSourceSend.send, hbegin] at supported
  obtain ⟨response, afterKdf, reply, afterSeal, hkdf, hseal, hsent⟩ :=
    RawCtxSourceSend.requested_support _ pending (log, cache) sent supported
  simp only [QueryImpl.apply_compose, RawCtxSourceSend.adapter, PqxdhServerRegistrationPublication.sendLift,
    simulateQ_spec_query] at hkdf
  rw [tailImpl_kdf_run, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hkdf
  obtain ⟨hresponse, hafter⟩ := hkdf
  have hresponse' : response = RawCtxSourceHkdf.response setup.source.crypto pending.request := hresponse
  subst hresponse' hafter hsent
  have hsequence : pending.sequence = 1#u64 := by
    apply UScalar.eq_of_val_eq
    rw [hnext, hzero]
    rfl
  have hargs : RawCtxSourceSend.arguments (RawCtxSourceSend.resumeSend pending
      (RawCtxSourceHkdf.response setup.source.crypto pending.request)) =
      ⟨chainMaterial setup.source.crypto initial.refined.send_chain, 1#u64, context⟩ := by
    obtain ⟨stepped, _, hready⟩ := RawCtxSourceSend.resumeSend_fields pending
      (RawCtxSourceHkdf.response setup.source.crypto pending.request)
    have hmaterial := send_material setup.source.crypto pending initial.refined.send_chain hinput hinfo
    simp only [RawCtxSourceSend.arguments]
    rw [hmaterial]
    rw [hready]
    simp only [hsequence, hcontext]
  simp only [QueryImpl.apply_compose, RawCtxSourceSend.adapter, PqxdhServerRegistrationPublication.sendLift,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff, hargs] at hseal
  obtain ⟨sealed, sealedRun, hpair⟩ := hseal
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hreply, rfl⟩ := hpair
  rw [hreply]
  have written := tail_seal_written setup codec checks limit laws _ (by rw [hargs]; exact hAD)
    (by rw [hargs]; exact short) log cache sealed sealedRun
  cases hsealed : sealed.1 with
  | none => exact absurd hsealed written
  | some ciphertext =>
      rw [Option.map_some]
      exact Option.some_ne_none _

/-- The Server's next key ID is available whenever its counter is below the maximum. -/
theorem next_key_id_some (state : pqxdh.ServerState) (below : state.last_key_id ≠ core.num.U64.MAX) :
    ∃ next, pqxdh.server_next_key_id state = ok (.Ok next) :=
  (u64_add_one state.last_key_id (by
    have hne : state.last_key_id.val ≠ 2 ^ 64 - 1 :=
      fun hv => below (UScalar.eq_of_val_eq (hv.trans u64_max_val.symm))
    scalar_tac)).elim fun next hnext => ⟨next, by simp [pqxdh.server_next_key_id, below, hnext.1]⟩

/-- The Server's commit preparation succeeds on a pending registration with the current binding, an available key ID and a counter below the maximum. -/
theorem prepare_commit_some (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (current : pqxdh.ServerBinding) (below : state.last_key_id ≠ core.num.U64.MAX)
    (sameKey : pending.server_binding.identity_key_id = current.identity_key_id)
    (sameIdentity : pending.server_binding.identity_public_key = current.identity_public_key) :
    ∃ candidate, pqxdh.server_prepare_commit state pending current .Available = ok (.Ok candidate) := by
  obtain ⟨next, hnext⟩ := next_key_id_some state below
  obtain ⟨ad, had⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok current.identity_public_key
    pending.beacon_identity_public_key
  exact ⟨pqxdh.ServerRegistrationCandidate.mk state ⟨next⟩ next pending.beacon_identity_public_key
    current.identity_public_key current.identity_key_id pending.ephemeral_public_key pending.kem_ciphertext ad,
    by simp [pqxdh.server_prepare_commit, sameKey, sameIdentity, array_eq_abs, hnext, had]⟩

/-- The public checks that accept everything: every point, key and identity check passes and every allocation succeeds. -/
def acceptAll : Checks :=
  ⟨fun _ => true, fun _ => true, fun _ => true, fun _ => true, true, true, fun _ => true⟩

/-- The Server's build of a pending registration under a root publishes a Phase 2 on every run of the logging tail. -/
def Publishes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (cache : CtxRomAuth.CtxRO.QueryCache) : Prop :=
  ∀ built ∈ support ((simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run ([], cache)),
    ((PqxdhServerAuthExperiment.settle server built.1).1).isSome

/-- Converse of `build_published`: under the control laws and the accepting checks, the Server's build publishes on every run when its key-ID counter is below the maximum, it has no peer, the pending registration carries the Server's current binding, and the plaintext is nonempty and short. -/
theorem build_publishes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat)
    (laws : ControlLaws setup codec limit) (pending : pqxdh.PendingServerRegistration) (root : RootOutput)
    (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (cache : CtxRomAuth.CtxRO.QueryCache) (below : server.control.last_key_id ≠ core.num.U64.MAX)
    (noPeer : ∀ id, server.server.peers id = none)
    (sameKey : pending.server_binding.identity_key_id = server.identityKeyId)
    (sameIdentity : pending.server_binding.identity_public_key = server.server.identity)
    (nonempty : payload.getD PqxdhServerRegistrationPublication.registrationWitness ≠ [])
    (allocatable : 8 + (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length ≤ Usize.max)
    (short : (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length + 88 < limit) :
    Publishes setup codec acceptAll pending root payload server cache := by
  intro built supported
  obtain ⟨next, hnext⟩ := next_key_id_some server.control below
  obtain ⟨candidate, hprepared⟩ := prepare_commit_some server.control pending
    ⟨server.server.identity, server.identityKeyId⟩ below sameKey sameIdentity
  simp only [PqxdhServerRegistrationPublication.build, hnext, PqxdhServerRegistrationPublication.continueRust,
    noPeer, Option.isSome_none, Bool.false_eq_true, ite_false, hprepared] at supported
  obtain ⟨kernel, hrun, _, _, _⟩ :=
    PqxdhRootTableInitialization.initialize_refines setup.source PqxdhServerAuthExperiment.unitRatchet false root
  have hinit : BeaconcryptCore.Refinement.ServerTransactionRefinement.initializeCandidate candidate
      (rootArray root)
      (PqxdhRootTableInitialization.initialResponse setup.source.crypto) = ok kernel :=
    (PqxdhServerRegistrationPublication.candidate_initialization setup.source candidate root).trans hrun
  obtain ⟨binding, hbinding, hbytes⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
  simp only [PqxdhServerRegistrationPublication.candidateTail, hinit, hbinding,
    PqxdhServerRegistrationPublication.continueRust, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff, tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, rfl, supported⟩ := supported
  simp only [acceptAll, Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff, tailImpl_aux, PqxdhServerAuthExperiment.tailAux, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, rfl, supported⟩ := supported
  have notEmpty : (payload.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = false := by
    cases h : payload.getD PqxdhServerRegistrationPublication.registrationWitness with
    | nil => exact absurd h nonempty
    | cons _ _ => rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, notEmpty, allocatable, ite_true,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff, tailImpl_aux,
    PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, rfl, supported⟩ := supported
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  obtain ⟨sent, afterSend, afterErase, hsent, herase, rest⟩ :=
    PqxdhServerRegistrationPublication.afterInitialization_support _ candidate _ kernel () server
      ([], cache) inner innerSupported
  rw [tailImpl_aux] at herase
  simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, true_and] at herase
  subst herase
  have plaintextLength : (absBytes binding.bytes ++
      payload.getD PqxdhServerRegistrationPublication.registrationWitness).length + 80 < limit := by
    rw [List.length_append, hbytes, Pqxdh.LE64_length]
    omega
  have written := send_written setup codec acceptAll limit laws root kernel hrun _ (by
    simp [PqxdhServerRegistrationPublication.firstContext]) plaintextLength [] cache _ hsent
  cases hs : sent.2 with
  | none => exact absurd hs written
  | some encrypted =>
      rw [hs] at rest
      obtain ⟨written', afterWrite, hwritten, eq⟩ := rest
      rw [tailImpl_aux] at hwritten
      simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hwritten
      obtain ⟨rfl, rfl⟩ := hwritten
      obtain ⟨digest, hencrypted, _, hframe, _⟩ := tail_send setup codec acceptAll root kernel hrun
        _ [] cache _ hsent encrypted hs
      have phase2 := phase2_written laws _ encrypted.ciphertext (by
        simp only [RawCtxSourceSeal.frame, protected_length _ laws.bodyLength]
        exact plaintextLength) hframe candidate.key_id candidate.ephemeral_public_key
        candidate.server_identity_public_key candidate.kem_ciphertext
      rw [eq]
      simp only [PqxdhServerAuthExperiment.settle, PqxdhServerRegistrationPublication.responseFields]
      cases hw : codec.write2 ⟨candidate.key_id, candidate.ephemeral_public_key,
          candidate.server_identity_public_key, candidate.kem_ciphertext, encrypted.ciphertext⟩ with
      | none => exact absurd hw phase2
      | some _ => simp

/-! ## The relay control -/

/-- The Server's sequence-one send material for a root is the Beacon's sequence-one receive material for the same root. -/
theorem material_agree (source : FixedHkdfSha512NoSaltSource) (root : RootOutput)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (hkernel : PqxdhRootTableInitialization.initialKernelRun source false root = ok kernel) :
    chainMaterial source.crypto kernel.refined.send_chain = beaconMaterial source.crypto (rootArray root) := by
  obtain ⟨_, _, beacon, server, hbeacon, hserver, _, _, hchain, _⟩ :=
    PqxdhRootTableInitialization.complementary_kernels source (modelCrypto source.crypto) root
  have hbeacon' := beaconKernel_run source (rootArray root)
  rw [PqxdhPhase2InputBytes.word_rootArray] at hbeacon'
  have sameBeacon : beacon = beaconKernel source.crypto (rootArray root) := RustM.ok.inj (hbeacon.symm.trans hbeacon')
  have sameServer : server = kernel := RustM.ok.inj (hserver.symm.trans hkernel)
  subst sameBeacon sameServer
  rw [beaconMaterial, hchain]

/-- The Server's 192-byte root input for the target Beacon is the one the control adversary computes. -/
theorem server_input_eq (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (reader : Reader)
    (e : ScalarBytes) (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret) :
    PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar (PqxdhServerRelatedRootInput.message
        (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime kemPk
          reader e encapsulated)) =
      controlBytes setup seed (setup.joint.publicKeys beaconSeed).ed25519
        ⟨setup.dh.publicKey scalar, setup.dh.publicKey oneTime, kemPk⟩ e encapsulated.2 := by
  simp only [PqxdhServerRelatedRootInput.message, PqxdhJointDhExtractRoot.server_input, honestInputs,
    honestVerified, peer_rootArray, PqxdhPhase2InputBytes.word_rootArray, controlBytes, identity_conversion,
    PqxdhJointGapDh.challenge]
  rw [show (setup.joint.publicKeys beaconSeed).convertedX25519.toList =
    setup.source.crypto.xpub (setup.source.crypto.xsk (setup.secretOfSeed beaconSeed).toList) from
      setup.wiring.xPublic beaconSeed]

/-- The Server's honest inputs pass its local nonzero test. -/
theorem honest_localNonzero (setup : Setup baseSpec KemSK)
    (nonzero : PqxdhServerAuthAssumptions.NonzeroHonestDh setup.source.crypto)
    (publicValue : PublicChallenge) (scalar : ScalarBytes) (prekey : publicValue.prekey = setup.dh.publicKey scalar)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (reader : Reader)
    (e : ScalarBytes) (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret) :
    PqxdhServerRelatedRootInput.localNonzero
      (honestInputs setup publicValue beaconSeed oneTime kemPk reader e encapsulated) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [honestInputs, PqxdhRootTableInitialization.rootArray_bytes, dhValue, setup.wiring.xPublic]
    exact nonzero _ _
  · rw [honestInputs, PqxdhRootTableInitialization.rootArray_bytes, dhValue, prekey]
    exact nonzero _ _
  · rw [honestInputs, PqxdhRootTableInitialization.rootArray_bytes, dhValue]
    exact nonzero _ _

/-- A build query with a pending token runs the logging tail once and installs its outcome. -/
theorem run_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (token : PqxdhServerRelatedRootConsumer.Returned) (hpending : state.pending session = some token) :
    runAdversary setup codec checks seed scalar beaconSeed (liftM (ExpSpec.query (.inr (.build session payload))))
        state family =
      (fun result => (((PqxdhServerAuthExperiment.settle state.server result.1).1, { state with
        pending := Function.update state.pending session none
        server := (PqxdhServerAuthExperiment.settle state.server result.1).2
        ctx := result.2.2
        ghost := { state.ghost with seals := state.ghost.seals ++ result.2.1.map (fun context => (session, context)) } }),
          family)) <$>
        (simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () state.server)).run
            ([], state.ctx) := by
  rw [runAdversary_query]
  change (simulateQ (romReduction setup seed scalar) ((PqxdhServerAuthExperiment.buildOracle setup codec checks
    session payload).run state)).run family = _
  simp only [PqxdhServerAuthExperiment.buildOracle, StateT.run_bind, StateT.run_get, pure_bind, hpending, liftCoins,
    StateT.run_lift, bind_assoc, simulateQ_bind, simulateQ_pure, StateT.run_set, StateT.run_pure]
  simp only [romReduction]
  rw [rom_coins, bind_map_left, map_eq_bind_pure_comp]
  rfl

open PqxdhServerAuthExperiment (binding) in
/-- After the honest accept, when the KEM decapsulation is correct, the relay cannot win: either no Phase 2 reaches the Beacon and it never accepts, or the Beacon accepts the partner session's sealed fields. Moreover, if the Server's build publishes on every run, the Beacon accepts. -/
theorem relay_after_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (laws : RelayLaws setup codec) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload : Option Pqxdh.Bytes) (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed)
    (oneTime : ScalarBytes) (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (reader : Reader) (e : ScalarBytes)
    (encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret)
    (good : functional.result keys.2 encapsulated.1 = some encapsulated.2)
    (bytes : Pqxdh.Bytes) (prk : HmacBlock)
    (hinputS : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar
      (PqxdhServerRelatedRootInput.message (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
        beaconSeed oneTime keys.1 reader e encapsulated)) = some bytes)
    (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (hpending : state.pending 0 = some ⟨expandRoot setup.hmac prk, PqxdhServerClearedRoot.pending
      (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))
        (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1
          reader e encapsulated)⟩)
    (hserverIdentity : state.server.server.identity = rootArray (setup.joint.publicKeys seed).ed25519)
    (hserverKey : state.server.identityKeyId = setup.serverKeyId)
    (hbeacon : state.beacon = publishedBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed oneTime keys.2)
    (hghost : state.ghost = ⟨[.session 0 (PqxdhServerRelatedRootInput.message (honestInputs setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1 reader e encapsulated))
        (some (expandRoot setup.hmac prk))], [], none⟩)
    (hprk : family.cache bytes = some prk)
    (result : (Unit × GameState KemSK) × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (runAdversary setup codec checks seed scalar beaconSeed
      (relayBuild payload (some 0)) state family)) :
    ¬ Win setup seed scalar result.1.2.ghost ∧
      (Publishes setup codec checks (PqxdhServerClearedRoot.pending
        (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))
        (honestInputs setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1
          reader e encapsulated)) (expandRoot setup.hmac prk) payload state.server state.ctx →
        result.1.2.ghost.acceptance ≠ none) := by
  simp only [relayBuild] at supported
  rw [runAdversary_bind, run_build setup codec checks seed scalar beaconSeed 0 payload state family _ hpending,
    bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨built, builtRun, supported⟩ := supported
  cases hsettled : (PqxdhServerAuthExperiment.settle state.server built.1).1 with
  | none =>
      rw [hsettled] at supported
      simp only [relayFinish, runAdversary_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨?_, fun publishes => absurd (publishes built builtRun) (by rw [hsettled]; simp)⟩
      rintro (⟨snap, hsnap, _⟩ | ⟨snap, hsnap, _⟩ | ⟨snap, hsnap, _⟩) <;> simp [hghost] at hsnap
  | some response =>
      rw [hsettled] at supported
      obtain ⟨candidate, kernel, digest, frameBytes, hbeaconId, hserverId, hserverKeyC, heph, hkem, had, hrun,
        hnonempty, hcache, hframe, hwrite, hlog⟩ := build_published setup codec checks _ _ payload state.server
          state.ctx built builtRun response hsettled
      simp only [relayFinish] at supported
      rw [runAdversary_bind, mem_support_bind_iff] at supported
      obtain ⟨finished, finishRun, supported⟩ := supported
      rw [runAdversary_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      obtain ⟨resp, hread, hct, heph', hsid, hid, happ⟩ := laws.phase2 _ response.serialized hwrite
      rw [hkem] at hct
      rw [heph] at heph'
      rw [hserverId, hserverIdentity] at hsid
      obtain ⟨hne, hdecode⟩ := laws.frame _ frameBytes hframe
      have hdecap : functional.result keys.2 (PqxdhPhase2InputBytes.ciphertext
          (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1)) = some encapsulated.2 := by
        rw [(PqxdhPhase2InputBytes.ciphertext_roundtrip (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1)
          encapsulated.1).2]
        exact good
      have hmat := material_agree setup.source (expandRoot setup.hmac prk) kernel hrun
      have hAD : candidate.associated_data = PqxdhBeaconPhase2Shared.associatedData
          (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed) := by
        have spec := (BeaconcryptCore.PanicFreedom.build_associated_data_ok
          (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed).expected_server_binding.identity_public_key
          (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed).beacon_identity_public_key).choose_spec
        rw [hserverIdentity] at had
        exact RustM.ok.inj (had.symm.trans spec)
      simp only [PqxdhServerRegistrationPublication.firstContext, RawCtxSourceSeal.hashInput,
        RawCtxSourceSeal.frame] at hframe hcache hdecode
      rw [hmat, hAD] at hframe hcache hdecode
      rw [hserverKeyC, hserverKey] at hframe hcache hdecode
      have hbody : ∀ key nonce ad : Pqxdh.Bytes, (setup.source.crypto.aeadSeal key nonce ad
          (Pqxdh.LE64 candidate.key_id.val ++ payload.getD PqxdhServerRegistrationPublication.registrationWitness)).1
            ≠ [] := by
        intro key nonce ad empty
        have := laws.bodyLength key nonce ad
          (Pqxdh.LE64 candidate.key_id.val ++ payload.getD PqxdhServerRegistrationPublication.registrationWitness)
        rw [empty, List.length_append, Pqxdh.LE64_length] at this
        simp at this
      have hinputB := beacon_input_eq setup laws.nonzero seed scalar beaconSeed oneTime e resp
        (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1) candidate.key_id encapsulated.2 keys.1
      rw [← server_input_eq, hinputS] at hinputB
      obtain ⟨beacon', family', hfinish⟩ := beacon_finish setup codec functional laws.nonzero seed scalar beaconSeed
        oneTime e keys.2 response.serialized resp (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1)
        candidate.key_id encapsulated.2 hread hct heph' hsid hid hdecap frameBytes _ _ _
        (payload.getD PqxdhServerRegistrationPublication.registrationWitness) digest happ hne hdecode rfl rfl rfl
        (hbody _ _ _) hnonempty bytes prk family hinputB hprk rfl
        { state with
          pending := Function.update state.pending 0 none
          server := (PqxdhServerAuthExperiment.settle state.server built.1).2
          ctx := built.2.2
          ghost := { state.ghost with seals := state.ghost.seals ++ built.2.1.map (fun context => (0, context)) } }
        hbeacon hcache
      rw [runAdversary_query] at finishRun
      change finished ∈ support ((simulateQ (romReduction setup seed scalar)
        ((PqxdhServerAuthExperiment.finishOracle setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          beaconSeed response.serialized).run _)).run family) at finishRun
      rw [hfinish, support_pure, Set.mem_singleton_iff] at finishRun
      subst finishRun
      have hbeaconInput := hinputB
      have hsessionInput := hinputS
      refine ⟨fun hwin => ?_, fun _ => by simp [Ghost.accept, hghost]⟩
      simp only [Win, PqxdhServerAuthExperiment.W1, PqxdhServerAuthExperiment.W2, PqxdhServerAuthExperiment.W3,
        Ghost.accept, hghost, hlog, List.nil_append, List.map_cons, List.map_nil, Option.some.injEq,
        exists_eq_left'] at hwin
      have hpartner : ∀ j, PqxdhServerAuthExperiment.Partner setup seed scalar
          ⟨⟨candidate.key_id, payload.getD PqxdhServerRegistrationPublication.registrationWitness,
            absBytes (PqxdhBeaconPhase2Shared.associatedData
              (beaconControl setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed))⟩,
            [.session 0 (PqxdhServerRelatedRootInput.message (honestInputs setup
              (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1 reader e
                encapsulated)) (some (expandRoot setup.hmac prk)),
             .beacon (PqxdhJointDhExtractRoot.beaconMessage (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
              (beaconCollected setup seed beaconSeed oneTime e resp
                (PqxdhAcceptedRegistration.ciphertextArray encapsulated.1) candidate.key_id encapsulated.2))],
            [(0, PqxdhServerRegistrationPublication.firstContext candidate (Pqxdh.LE64 candidate.key_id.val ++
              payload.getD PqxdhServerRegistrationPublication.registrationWitness))]⟩ j ↔ j = 0 := by
        intro j
        constructor
        · rintro ⟨message, reply, _, member, _, _⟩
          simp at member
          exact member.1
        · rintro rfl
          refine ⟨PqxdhServerRelatedRootInput.message (honestInputs setup
            (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1 reader e
              encapsulated), some (expandRoot setup.hmac prk), bytes, by simp, hsessionInput, ?_⟩
          simp only [PqxdhServerAuthExperiment.beaconInput, PqxdhServerAuthExperiment.firstBeacon,
            List.findSome?_cons, Option.bind_some, PqxdhServerAuthExperiment.rootInput]
          exact hbeaconInput
      simp only [List.singleton_append] at hwin
      rcases hwin with hw1 | ⟨_, hw2⟩ | ⟨i, j, hij, hpi, hpj⟩
      · exact hw1 0 ((hpartner 0).mpr rfl)
      · refine hw2 0 ((hpartner 0).mpr rfl) _ (List.mem_singleton_self _) ?_
        simp only [PqxdhServerAuthExperiment.sealed, PqxdhServerRegistrationPublication.firstContext, drop_binding, hAD]
      · exact hij (((hpartner i).mp hpi).trans ((hpartner j).mp hpj).symm)

/-- Without an acceptance there is no win. -/
theorem no_acceptance (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (ghost : Ghost)
    (none : ghost.acceptance = none) : ¬ Win setup seed scalar ghost := by
  rintro (⟨snap, hsnap, _⟩ | ⟨snap, hsnap, _⟩ | ⟨snap, hsnap, _⟩) <;> rw [none] at hsnap <;> cases hsnap

/-- An accept whose prefix answers nothing answers nothing. -/
theorem acceptAfter_none (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (consumed : List Pqxdh.Bytes) (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State) :
    (simulateQ (romReduction setup seed scalar) ((acceptAfter (Reader := Reader) setup
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) state (none, consumed)).run state)).run family =
      pure ((none, { state with
        sessions := state.sessions + 1
        server := { state.server with consumed := consumed } }), family) := by
  simp only [acceptAfter, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, simulateQ_pure]

set_option linter.deprecated false in
/-- Per key pair, the honest relay wins with probability at most the key pair's KEM correctness error. -/
theorem relay_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (laws : RelayLaws setup codec) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload : Option Pqxdh.Bytes) (seed : IdentitySeed) (scalar : ScalarBytes)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) :
    Pr[fun result => Win setup seed scalar result.1.2.ghost | runAdversary setup codec checks seed scalar beaconSeed
        (relayAdversary payload (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 none))
        (initial setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2)
        PqxdhJointDhExtractFamily.empty] ≤ keyPairError setup functional keys := by
  cases written : codec.write1 (beaconCandidate setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
      beaconSeed oneTime keys.1) with
  | none =>
      simp only [phase1Result, written, controlInput, relayAdversary, runAdversary_pure]
      refine le_of_eq_of_le (probEvent_eq_zero fun result supported => ?_) (by simp)
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact no_acceptance setup seed scalar _ rfl
  | some bytes =>
      rw [phase1Result_some setup codec _ beaconSeed oneTime keys.1 keys.2 bytes written]
      simp only [controlInput, relayAdversary]
      rw [runAdversary_bind, run_accept, bind_assoc]
      obtain ⟨reader, hread, hidentity, hpq, hpre, hone⟩ := laws.phase1 _ bytes written
      change Pr[_ | (PqxdhServerAuthExperiment.serverPrefix setup codec checks bytes).run [] >>= _] ≤ _
      rw [serverPrefix_eq setup codec checks laws.nonzero seed scalar beaconSeed oneTime keys.1 bytes reader hread
        hidentity hpq hpre hone]
      split_ifs with hcheck hkem
      · rw [bind_assoc]
        refine probEvent_bind_le_of_forall_le fun e _ => ?_
        rw [bind_assoc]
        refine le_trans (probEvent_bind_le_probEvent
          (p := fun drawn => PqxdhKemCorrectnessError.Bad setup.kem functional ⟨keys.1, keys.2, drawn.1, drawn.2⟩)
          fun encapsulated _ bad => ?_) le_rfl
        have good : functional.result keys.2 encapsulated.1 = some encapsulated.2 := not_not.mp bad
        rw [pure_bind]
        obtain ⟨first, hfirst⟩ := static_present setup laws.nonzero seed scalar
        obtain ⟨bytesS, hcb⟩ : ∃ bytesS, controlBytes setup seed (setup.joint.publicKeys beaconSeed).ed25519
            ⟨setup.dh.publicKey scalar, setup.dh.publicKey oneTime, keys.1⟩ e encapsulated.2 = some bytesS :=
          ⟨_, by rw [controlBytes, hfirst]; rfl⟩
        have hinputS := server_input_eq setup seed scalar beaconSeed oneTime keys.1 reader e encapsulated
        rw [hcb] at hinputS
        rw [acceptAfter_honest setup seed scalar _ [] bytesS hinputS
          (honest_localNonzero setup laws.nonzero _ scalar rfl beaconSeed oneTime keys.1 reader e encapsulated)]
        refine probEvent_eq_zero fun result supported => ?_
        simp only [bind_assoc, pure_bind, mem_support_bind_iff] at supported
        obtain ⟨answer, answerRun, supported⟩ := supported
        have hcached := randomOracle_cached (spec := HmacOracle) _ _ _ answerRun
        exact (relay_after_accept setup codec checks laws functional payload seed scalar beaconSeed oneTime keys
          reader e encapsulated good bytesS answer.1 hinputS _ _ (by simp [initial]) rfl rfl rfl
          (by simp [initial, PqxdhServerAuthExperiment.Ghost.empty]) hcached
          result supported).1
      · refine le_of_eq_of_le (probEvent_eq_zero fun result supported => ?_) (by simp)
        simp only [bind_assoc, pure_bind, mem_support_bind_iff, acceptAfter_none] at supported
        obtain ⟨_, _, supported⟩ := supported
        simp only [relayBuild, runAdversary_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact no_acceptance setup seed scalar _ rfl
      · refine le_of_eq_of_le (probEvent_eq_zero fun result supported => ?_) (by simp)
        simp only [pure_bind, acceptAfter_none] at supported
        simp only [relayBuild, runAdversary_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact no_acceptance setup seed scalar _ rfl

set_option linter.deprecated false in
/-- Relay control (gate B5a): an honest relay of the target Beacon's Phase 1 to the Server and of the Server's Phase 2 to the Beacon wins with probability at most the KEM correctness error. -/
theorem relay_not_win (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (laws : RelayLaws setup codec) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (payload : Option Pqxdh.Bytes) :
    (Pr[= true | expGame setup codec checks false (relayAdversary payload)]).toReal ≤ kemError setup := by
  rw [game_win, kemError]
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one) ?_
  exact kem_split setup codec checks false (relayAdversary payload) functional
    (fun seed scalar state => Win setup seed scalar state.ghost)
    (fun seed scalar beaconSeed oneTime keys _ =>
      relay_bound setup codec checks laws functional payload seed scalar beaconSeed oneTime keys)

/-! ## Liveness of the honest relay -/

set_option linter.deprecated false in
/-- Per key pair, with the accepting checks and a nonempty short payload, the honest relay leaves the Beacon without an acceptance with probability at most the key pair's KEM correctness error. -/
theorem relay_live_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat)
    (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (payload : Option Pqxdh.Bytes)
    (nonempty : payload.getD PqxdhServerRegistrationPublication.registrationWitness ≠ [])
    (allocatable : 8 + (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length ≤ Usize.max)
    (short : (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length + 88 < limit)
    (below : setup.serverKeyId ≠ core.num.U64.MAX) (seed : IdentitySeed) (scalar : ScalarBytes)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) :
    Pr[fun result => ¬ result.1.2.ghost.acceptance ≠ none |
      runAdversary setup codec acceptAll seed scalar beaconSeed
        (relayAdversary payload (controlInput setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).1 none))
        (initial setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
          (phase1Result setup codec (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)
            beaconSeed oneTime keys.1 keys.2).2)
        PqxdhJointDhExtractFamily.empty] ≤ keyPairError setup functional keys := by
  obtain ⟨bytes, written⟩ := laws.phase1Total (beaconCandidate setup
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) beaconSeed oneTime keys.1)
  rw [phase1Result_some setup codec _ beaconSeed oneTime keys.1 keys.2 bytes written]
  simp only [controlInput, relayAdversary]
  rw [runAdversary_bind, run_accept, bind_assoc]
  obtain ⟨reader, hread, hidentity, hpq, hpre, hone⟩ := laws.phase1 _ bytes written
  change Pr[_ | (PqxdhServerAuthExperiment.serverPrefix setup codec acceptAll bytes).run [] >>= _] ≤ _
  rw [serverPrefix_eq setup codec acceptAll laws.nonzero seed scalar beaconSeed oneTime keys.1 bytes reader hread
    hidentity hpq hpre hone]
  simp only [acceptAll, Bool.and_self, ite_true]
  rw [bind_assoc]
  refine probEvent_bind_le_of_forall_le fun e _ => ?_
  rw [bind_assoc]
  refine le_trans (probEvent_bind_le_probEvent
    (p := fun drawn => PqxdhKemCorrectnessError.Bad setup.kem functional ⟨keys.1, keys.2, drawn.1, drawn.2⟩)
    fun encapsulated _ bad => ?_) le_rfl
  have good : functional.result keys.2 encapsulated.1 = some encapsulated.2 := not_not.mp bad
  rw [pure_bind]
  obtain ⟨first, hfirst⟩ := static_present setup laws.nonzero seed scalar
  obtain ⟨bytesS, hcb⟩ : ∃ bytesS, controlBytes setup seed (setup.joint.publicKeys beaconSeed).ed25519
      ⟨setup.dh.publicKey scalar, setup.dh.publicKey oneTime, keys.1⟩ e encapsulated.2 = some bytesS :=
    ⟨_, by rw [controlBytes, hfirst]; rfl⟩
  have hinputS := server_input_eq setup seed scalar beaconSeed oneTime keys.1 reader e encapsulated
  rw [hcb] at hinputS
  rw [acceptAfter_honest setup seed scalar _ [] bytesS hinputS
    (honest_localNonzero setup laws.nonzero _ scalar rfl beaconSeed oneTime keys.1 reader e encapsulated)]
  refine probEvent_eq_zero fun result supported => ?_
  simp only [bind_assoc, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨answer, answerRun, supported⟩ := supported
  have hcached := randomOracle_cached (spec := HmacOracle) _ _ _ answerRun
  exact not_not.mpr ((relay_after_accept setup codec acceptAll laws.toRelayLaws functional payload seed scalar
    beaconSeed oneTime keys reader e encapsulated good bytesS answer.1 hinputS _ _ (by simp [initial]) rfl rfl rfl
    (by simp [initial, PqxdhServerAuthExperiment.Ghost.empty]) hcached result supported).2
    (build_publishes setup codec limit laws _ _ payload _ _ below (fun _ => rfl) rfl rfl nonempty allocatable short))

set_option linter.deprecated false in
/-- Relay liveness (gate B5a): with the accepting checks, a nonempty payload short enough for the writers and the Server's allocation, and a Server key ID below the maximum, the honest relay makes the Beacon accept with probability at least one minus the KEM correctness error. -/
theorem relay_live (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (limit : Nat)
    (laws : ControlLaws setup codec limit)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (payload : Option Pqxdh.Bytes)
    (nonempty : payload.getD PqxdhServerRegistrationPublication.registrationWitness ≠ [])
    (allocatable : 8 + (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length ≤ Usize.max)
    (short : (payload.getD PqxdhServerRegistrationPublication.registrationWitness).length + 88 < limit)
    (below : setup.serverKeyId ≠ core.num.U64.MAX) :
    1 - kemError setup ≤ (Pr[fun result => result.2.2.1.ghost.acceptance ≠ none |
      gameState setup codec acceptAll false (relayAdversary payload)]).toReal :=
  kem_lower setup codec acceptAll false (relayAdversary payload) functional
    (fun _ _ state => state.ghost.acceptance ≠ none)
    (fun seed scalar beaconSeed oneTime keys _ =>
      relay_live_bound setup codec limit laws functional payload nonempty allocatable short below seed scalar
        beaconSeed oneTime keys)

end BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.frame_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.frame_written

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase2_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase2_written

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.protected_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.protected_length

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.writing_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.writing_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase1Run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase1Run_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase1Run_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase1Run_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.lift_pure_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.lift_pure_state

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.peer_rootArray' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.peer_rootArray

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sourceScalarDh_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sourceScalarDh_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.dhReply_of_nonzero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.dhReply_of_nonzero

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_conversion

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.accepts_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.accepts_public

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.accepts_server' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.accepts_server

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_staticDh_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_staticDh_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_oneTimeDh_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_oneTimeDh_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_prepare

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beaconKernel_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beaconKernel_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.fromPayload_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.fromPayload_honest

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.native_hash_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.native_hash_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.native_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.native_base

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_open

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.arguments_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.arguments_of

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_afterRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_afterRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.stage_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.stage_prepare

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.stage_native

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.onCtx_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.onCtx_simulate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.rom_root_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.rom_root_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.finish_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.finish_honest

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.drop_binding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.drop_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_query

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.runAdversary_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.body_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.body_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.keyPairError_average' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.keyPairError_average

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.kem_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.kem_split

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.parse_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.parse_honest

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.advCoins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.advCoins_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.advCoins_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.advCoins_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.control_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.control_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.control_no_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.control_no_server

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.identity_conversion' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.identity_conversion

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beaconSecond_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beaconSecond_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beaconFourth_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beaconFourth_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_third_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_third_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_input_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_input_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.randomOracle_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.randomOracle_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_hmac

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.static_present' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.static_present

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase1Result_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.phase1Result_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.control_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.control_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.game_win' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.game_win

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.kem_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.kem_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.negative_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.negative_control

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.negative_control_win' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.negative_control_win

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_verify' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_verify

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_lambda' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_lambda

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.lambda_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.lambda_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.lift_bind_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.lift_bind_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.beacon_conversion

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_accepts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_accepts

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.ephemeral_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.ephemeral_public

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.ephemeral_identity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.ephemeral_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.serverPrefix_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.serverPrefix_honest

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.serverPrefix_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.serverPrefix_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.acceptAfter_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.acceptAfter_honest

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sealHandler_aead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sealHandler_aead

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sealHandler_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sealHandler_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sealHandler_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.sealHandler_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tail_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tail_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tailImpl_kdf_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tailImpl_kdf_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.send_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.send_material

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tail_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tail_send

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.prepare_commit_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.prepare_commit_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tailImpl_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tailImpl_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.build_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.build_published

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.seal_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.seal_written

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tail_seal_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.tail_seal_written

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.send_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.send_written

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.next_key_id_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.next_key_id_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.prepare_commit_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.prepare_commit_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.build_publishes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.build_publishes

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.material_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.material_agree

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_input_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.server_input_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.honest_localNonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.honest_localNonzero

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.run_build

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_after_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_after_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.no_acceptance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.no_acceptance

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.acceptAfter_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.acceptAfter_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_not_win' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_not_win

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_live_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_live_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl.relay_live
