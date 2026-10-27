import BeaconcryptCore.Computational.PqxdhExtractRomFamily
import BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer
import BeaconcryptCore.Computational.PqxdhRegistrationProtocolState
import BeaconcryptCore.Computational.PqxdhPhase2DhStage
import BeaconcryptCore.Computational.PqxdhLivePhase1Bundle
import BeaconcryptCore.Computational.PqxdhPhase2LocalMatching

/-!
# Server authentication: the experiment, its events and support lemmas

This module is stage B4a of the Server-authentication proof (Milestone B, route R1). It defines the executable experiment in which an adversary tries to make the target Beacon complete registration with the pinned Server without a matching honest Server session, the events that the later stages bound, and the support lemmas those stages use. It adds no premise to any existing theorem and states no security law.

The experiment. `gameState` first samples, inside the game, the Server's Ed25519 identity seed and the Beacon's signed-prekey scalar, the two secrets of the Gap-DH game `PqxdhJointGapDh.game`. It then runs `body` under the Extract random-oracle family `PqxdhExtractRomFamily.romImpl` composed with the root reduction `PqxdhJointDhExtractRoot.reduction`: zero-salt HKDF-Extract on 192-byte inputs is one lazily sampled table shared by the Server's and the Beacon's root derivations and the adversary's public HMAC queries, and every other HMAC use is the real function. `body` uses neither secret. It samples the Beacon's identity seed, one-time scalar and ML-KEM key pair, publishes the Beacon's Phase 1 through the existing bundle program `PqxdhLivePhase1Bundle.bundle`, and runs the adversary against `authHandler`. The Server seed appears only in the family's root inputs and, in the negative control, in the adversary's input. `serverAuthGame` returns the winning event of the final ghost.

The adversary's interface. The adversary has uniform coins and six queries (`ServerAuthQuery`). The first two are the registration methods of the public `ProviderServer` trait (`server.rs:112-124`). `.accept phase1` is the Server's `get_shared_secret` (`server.rs:332-422`): it allocates the next session index, runs the Server's Phase 1 prefix `PqxdhServerRootPreparation.collect` with the static DH as a public reference (`PqxdhServerStaticDhSource.prefixImpl`), then the extracted `server_accept` path `PqxdhServerRelatedRootConsumer.client`, which derives the root through one family request and consumes the registration ID on success; the pending token is stored under the session index, which is returned. `.build session payload` is the Server's `build_registration_response` (`server.rs:424-502`): it consumes the session's pending token, because the Rust method takes the token by value, and runs the extracted builder `PqxdhServerRegistrationPublication.build`, which assigns the next key ID in build order, seals the sequence-one record under the stored root and writes Phase 2; a session without a pending token answers nothing. The C, Go and Python bindings call the two methods back to back (`cbinds.rs:280-291`, `pybinds.rs:125-128`), which the split interface covers. A build may come after the Beacon's finish, and a session may be accepted and never built. `.finish phase2` is the target Beacon's `finish_registration` (`beacon.rs:402-510`): in the InitSent phase it runs the executable Phase 2 stage `PqxdhPhase2DhStage.stage`, whose root derivation is one family request, and then the unchanged final checks `PqxdhBeaconPhase2Publication.finish`; in every other phase it answers nothing. `.hmac key message` is the public HMAC, patched to the table under the zero key on 192-byte messages. `.hash bytes` is the BLAKE2b random oracle on the cache that the Server's seals and the Beacon's opening share. `.reveal keyId` returns the ratchet kernel that the Server has installed for that key ID.

Primitives and callbacks. `Setup` fixes the functional primitives, the public DH domains, the ML-KEM scheme and the Server's key ID; `Codec` holds the free message readers and writers, and `Checks` the public admission and allocation predicates. Every callback that touches a secret is fixed to the functional primitive, so no parameter can leak a secret. The Server's Phase 1 prefix (`serverPrefix`) and the Beacon's Phase 2 preparation (`beaconPrefix`) are lifted probabilistic computations. The Server's response tail runs the native primitives of `PqxdhRegistrationProtocolState.registrationImpl` (real ratchet KDF, functional AEAD, BLAKE2b on the shared cache, frame writer) and logs every successful seal callback; `tail_native` shows that this log is pure instrumentation.

The ghost and the events. The handler keeps a ghost that the adversary never sees: the ordered log of Extract-table touches (a Server session's derivation with the family's reply, the Beacon's derivation, or an adversary table query), the successful sequence-one seals by session, and a write-once snapshot of both logs together with the accepted fields, taken when the Beacon accepts. A session touch carries the derived root that the family returned, so the ghost holds key material; no handler reads the ghost, and `win_erase`, `badB_erase`, `collB_erase`, `entryOwner_erase` and `entryEvent_erase` show that the events are unchanged when these roots are erased, as the key-factoring stage must do together with the family history. `Partner snap i` holds when session `i` derived, before the acceptance, the Beacon's 192-byte root input, which `rootInput` recomputes with the two secrets. The assigned key ID is not part of partnering, because it enters no key and is authenticated inside the sequence-one plaintext (`server.rs:463-470`, `beacon.rs:473-484`). `W1` is an acceptance without a partner. `W2` is an acceptance at which a partner exists and no seal that any partner made before the acceptance has the accepted key ID, payload and associated data. `W3` is an acceptance with two partners. `Win` is their disjunction. The analysis events are `BadB` (an adversary table query at the Beacon's root input), `CollB` (two sessions derived the Beacon's root input), `CandHit` (the Gap-DH scan event read from the family history), the owner `entryOwner` of the Beacon's table entry and the per-entry events `EntryEvent`; `sessionCollGame` is the collision game term. `sealed_eq_iff` identifies the comparison in `W2` with the comparison of the triples `PqxdhPhase2LocalMatching.acceptedFields` and `PqxdhPhase2LocalMatching.sealedFields` of stage B9a.

What is proved. `reachable_inv` shows that every state that any adversary program reaches from the initial state satisfies `GameInv`, from per-oracle step lemmas (`accept_step`, `build_step`, `finish_step`, `hmac_step`, `authHandler_step`), the exact effects of the Server's root consumer (`client_run`) and of the Beacon's stage (`stage_run`), and the generic simulation lemmas `run_rel` and `run_count`; `gameState_reachable` gives it for the final state. From the invariant: `snapshot_prefix` (the snapshot is a prefix of the final logs); `snapshot_atomic` (the snapshot's touch log ends with the Beacon's single touch, with no Beacon touch before it); `owner_beacon_no_partner`, `owner_beacon_only_w1`, `owner_session_partner` and `owner_session_not_w1` (a Beacon owner leaves only `W1`, a session owner below `Q` is a partner); `seal_touched` (every seal belongs to a touched session); `pending_root` (every pending token carries the reply of its session's root request); `seal_once_per_session` (no session has two seals, because a build consumes its token and seals at most once, see `build_consumes` and `build_step`); and `reveal_post_registration` (at every reached state, a revealed kernel is an `Installed` kernel: its send chain is the next chain of the step of chain_0, its receive chain and receive counters are the initial ones, its send counter is one and its receive slots are empty, so it stores neither chain_0 nor the sequence-one message material). `win_frozen` shows that `Win` reads only the snapshot, `w3_collB` that two partners are a narrowed collision, and `win_le_games` that the winning probability is at most `Pr[BadB] + Pr[CollB] + ∑ j, Pr[EntryEvent j]` over the `Q + 1` table owners. `finish_single_shot` shows that after a finish every finish at any later reached state is inactive, and `empty_payload` that a build with an empty payload answers and seals nothing. `partner_iff_root_input` shows, on every run, that a session touched in the snapshot is a partner exactly when the 192 root-input bytes of its extracted `server_accept` equal those of the Beacon's extracted builder, with all hypotheses of the input-level `root_inputs_iff` discharged on the run. `rom_coins`, `tail_native` and `beaconNative_ordinary` are interfaces for the later stages.

Adversary restrictions, each with its justification:

1. The budgets `Q` (Server accepts), `qH` (table-domain HMAC queries) and `qHash` (BLAKE2b queries) are ordinary query bounds, and `Q` is a parameter of the bound, evaluated at a few tens, as the owner decided.
2. No Beacon secret is revealed, because key-compromise impersonation is not claimed (owner decision).
3. A Server reveal returns only the kernel installed after the sequence-one seal, for any session including the partner, because that is all the Rust Server stores or exposes per established session (`server.rs:39-42, 410, 422, 456, 504-532`, `ser.rs:195-213`); `reveal_post_registration` shows that such a kernel stores neither chain_0 nor the sequence-one material.
4. There is no reveal of a pending session (accepted and not built), because the token that `get_shared_secret` returns holds the derived root but is opaque: its fields are `pub(crate)`, it has no derived trait or accessor, and the C, Go and Python bindings never surface it (`server.rs:39-42`, `cbinds.rs:280-291`, `pybinds.rs:125-128`), while reading it from memory would need access to the running code, which is out of scope.
5. There are no Server record oracles (`encrypt_and_update` and `decrypt_and_update`, `server.rs:504-532`, and the equivalent public `encrypt_message` and `decrypt_message`, `server.rs:224-231`), because they are deterministic in the revealed kernel, the real ratchet KDF outside the Extract table and the BLAKE2b oracle, and touch neither the table, the Beacon nor the sequence-one seals, so one reveal lets the adversary run them locally with the same view and the same `Win`, with `qHash` raised by the commitment hash queries each operation makes.
6. The adversary chooses the build payload, with `none` selecting `REGISTRATION_WITNESS` (`server.rs:459`), which is stronger than the real interface, where the host chooses it.
7. The Server seed is not revealed in the headline game, because before the finish this makes the claim false (the negative control) and after the finish it cannot change `Win`, which reads only the snapshot (`win_frozen`).
8. There is no persistence, no snapshot access and no access to running code or to libsodium internals, because these are outside the threat model (remediation plan, section 6).
9. There is one target Beacon with a single finish, because Beacon keys belong to one object and serve one Phase 1 and one finish (`beacon.rs:306-334, 403-406, 488-491, 493-502`, `finish_single_shot`), and several Beacons follow by a union bound.
10. Seals are logged at the successful seal callback rather than at publication, because a sealed record that is never sent is still the partner's output, and CTX counts a copy of it as a full-tuple match rather than a forgery.
11. The other public methods are omitted because they add nothing: the Beacon's `encrypt_message` and `decrypt_message` act only after the acceptance (`beacon.rs:152-174`), which `Win` never reads again (`win_frozen`); the Beacon's pre-Phase-1 helpers `new_onetime_keypair`, `delete_onetime_keypair` and `delete_pq_keypair` (`beacon.rs:222-296`) only replace the Beacon's coins before Phase 1 or abort it, which a garbage finish also achieves; and the Server's accessors `server_kid`, `pk_by_kid` and `ratchet_status` (`server.rs:182-209`) return non-secret values that the adversary computes from build responses, its own Phase 1 bundles and reveals. More generally, the secret getters of both roles (the Server's `identity_sk`, `server.rs:179-181`, and the Beacon's `identity_sk`, `pq_sk`, `get_prekey_sk` and `get_onetime_sk`, `beacon.rs:90, 114, 193, 210`) are exactly the reveals that restrictions 2 and 7 exclude, and every remaining getter returns a public value or acts only after the acceptance.
12. Availability, replay protection and key-ID uniqueness are neither claimed nor used, because the claim is authentication only.

Separate accept and build queries are part of the interface and not a restriction, so the earlier restriction that combined them no longer exists.

Scope and trust boundary. Messages are abstract byte strings that each side decodes with free functions, no serialization-library behaviour is used, and `Codec`, `Checks` and the ML-KEM scheme are universally quantified without laws. libsodium is a correct black box, and nothing about its internals is proved. That production makes exactly one Extract per root derivation is adapter-level trust (`beaconcrypt/src/pqxdh.rs:46-58`). By convention the owner of the Beacon's entry is the Beacon when the Beacon's derivation has no root input, which a successful finish excludes in the real run.

Premises. The module adds no premise and states no security law; the query budget is the only hypothesis of `win_le_games`. The axioms used are `propext`, `Classical.choice` and `Quot.sound` only.
-/

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge zeroDh readDh sourceInterface sourceScalarDh)
open PqxdhJointDhExtractRoot (RootSpec RootRequest)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhEd25519EufCma (Ed25519PublicKey Phase1Candidate)
open PqxdhRootTableInitialization (rootArray)
open PqxdhPhase2GapDhSource (peer)

/-! ## Parameters and primitives -/

/-- Fixed primitives of the experiment. Every field is an existing functional contract or a primitive the theorems quantify over; none is a security law. `serverKeyId` is the compiled-in `ServerBinding.identity_key_id`. -/
structure Setup {ι : Type} (baseSpec : OracleSpec ι) (KemSK : Type) where
  source : FixedHkdfSha512NoSaltSource
  hmac : HmacSha512
  joint : Primitives
  secretOfSeed : IdentitySeed → List.Vector UInt8 64
  wiring : SourceWiring source.crypto joint secretOfSeed
  serverDomain : PqxdhServerStaticDhSource.PublicDomain joint
  beaconDomain : PqxdhPhase2GapDhSource.PublicDomain (sourceInterface source.crypto joint secretOfSeed wiring)
  kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)
  baseImpl : QueryImpl baseSpec ProbComp
  serverKeyId : Std.U64

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The optional typed X25519 interface of the setup's functional primitives. -/
def Setup.dh (setup : Setup baseSpec KemSK) : DhInterface setup.joint :=
  sourceInterface setup.source.crypto setup.joint setup.secretOfSeed setup.wiring

/-- Messages are abstract byte strings that each side decodes with free functions: the Server's Phase 1 reader and getters, the Beacon's Phase 1 writer, the Server's Phase 2 writer, the Beacon's Phase 2 reader and getters, and the record frame codec. No law is assumed of any of them. -/
structure Codec (Reader Response : Type) where
  read1 : Pqxdh.Bytes → Option Reader
  identity : Reader → Option Pqxdh.Bytes
  pqField : Reader → Option Pqxdh.Bytes
  preField : Reader → Option Pqxdh.Bytes
  oneField : Reader → Option Pqxdh.Bytes
  write1 : Phase1Candidate → Option Pqxdh.Bytes
  write2 : PqxdhServerRegistrationPublication.ResponseFields → Option Pqxdh.Bytes
  read2 : Pqxdh.Bytes → Option Response
  ciphertext : Response → Option Ciphertext
  ephemeral : Response → Option Word32
  serverIdentity : Response → Option Word32
  assignedId : Response → Std.U64
  application : Response → Option Pqxdh.Bytes
  frameRead : RawCtxReceive.FrameDecoder
  frameWrite : RawCtxMixedShared.Writer

/-- Public admission and allocation predicates of the reference implementation: Ed25519 and X25519 point checks, the ML-KEM key check, the Server's Beacon-identity parse, and the allocation outcomes. -/
structure Checks where
  identityPoint : Ed25519PublicKey → Bool
  x25519Point : Word32 → Bool
  kemKey : PqxdhKemIndCca.MlKem768PublicKey → Bool
  beaconIdentity : RawCtxServerRouting.Identity → Bool
  reserveRegistration : Bool
  reservePeer : Bool
  reservePlaintext : Nat → Bool

/-! ## Adversary interface -/

/-- The adversary's queries: the Server's two public operations (`get_shared_secret` and `build_registration_response`), the target Beacon's single finish, the patched public HMAC, the BLAKE2b random oracle and the post-registration Server state reveal. -/
inductive ServerAuthQuery where
  | accept (phase1 : Pqxdh.Bytes)
  | build (session : Nat) (payload : Option Pqxdh.Bytes)
  | finish (phase2 : Pqxdh.Bytes)
  | hmac (key : HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)
  | reveal (keyId : Std.U64)

/-- Answer types: a session handle for a successful accept, the optional Phase 2 response of a build, the Beacon's optional application payload, an HMAC block, a BLAKE2b digest and the optional installed ratchet kernel. -/
abbrev QuerySpec : OracleSpec ServerAuthQuery
  | .accept _ => Option Nat
  | .build _ _ => Option PqxdhServerRegistrationPublication.Response
  | .finish _ => Option Pqxdh.Bytes
  | .hmac _ _ => HmacBlock
  | .hash _ => CtxRomAuth.CtxDigest
  | .reveal _ => Option ratchet.concrete.ConcreteRatchetKernel

/-- The adversary's oracle interface: uniform coins and the queries above. -/
abbrev ServerAuthSpec := unifSpec + QuerySpec

/-- Public input: the Server's identity and key ID, the target Beacon's published Phase 1, and the Server seed only in the negative control. -/
structure AuthInput where
  server : PublicIdentity
  serverKeyId : Std.U64
  phase1 : Option Pqxdh.Bytes
  revealed : Option IdentitySeed

/-- An adversary is a program over `ServerAuthSpec` started on the public input. -/
abbrev Adversary := AuthInput → OracleComp ServerAuthSpec Unit

/-- Server accept queries, the queries counted by the session budget `Q`. -/
def IsAcceptQuery : ServerAuthSpec.Domain → Prop
  | .inr (.accept _) => True
  | _ => False

/-- Accept queries are decidable. -/
instance : DecidablePred IsAcceptQuery := fun query =>
  match query with
  | .inr (.accept _) => isTrue trivial
  | .inl _ => isFalse id
  | .inr (.build _ _) => isFalse id
  | .inr (.finish _) => isFalse id
  | .inr (.hmac _ _) => isFalse id
  | .inr (.hash _) => isFalse id
  | .inr (.reveal _) => isFalse id

/-- Public HMAC queries inside the random-oracle domain (zero key, 192-byte message), counted by `qH`. -/
def IsRomQuery : ServerAuthSpec.Domain → Prop
  | .inr (.hmac key message) => key = zeroSalt ∧ message.length = 192
  | _ => False

/-- Random-oracle HMAC queries are decidable. -/
instance : DecidablePred IsRomQuery := fun query =>
  match query with
  | .inr (.hmac key message) => inferInstanceAs (Decidable (key = zeroSalt ∧ message.length = 192))
  | .inl _ => isFalse id
  | .inr (.accept _) => isFalse id
  | .inr (.build _ _) => isFalse id
  | .inr (.finish _) => isFalse id
  | .inr (.hash _) => isFalse id
  | .inr (.reveal _) => isFalse id

/-- BLAKE2b random-oracle queries, counted by `qHash`. -/
def IsHashQuery : ServerAuthSpec.Domain → Prop
  | .inr (.hash _) => True
  | _ => False

/-- BLAKE2b queries are decidable. -/
instance : DecidablePred IsHashQuery := fun query =>
  match query with
  | .inr (.hash _) => isTrue trivial
  | .inl _ => isFalse id
  | .inr (.accept _) => isFalse id
  | .inr (.build _ _) => isFalse id
  | .inr (.finish _) => isFalse id
  | .inr (.hmac _ _) => isFalse id
  | .inr (.reveal _) => isFalse id

/-- Ordinary query budgets: at most `Q` Server accepts, `qH` random-oracle HMAC queries and `qHash` BLAKE2b queries on every input. -/
structure AuthBudget (adversary : Adversary) (Q qH qHash : Nat) : Prop where
  accept : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q
  rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH
  hash : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash

/-! ## State and ghost -/

/-- The fields a Beacon acceptance fixes: the assigned key ID, the application payload after the 8-byte binding and the associated data. -/
structure Accepted where
  keyId : Std.U64
  payload : Pqxdh.Bytes
  associatedData : Pqxdh.Bytes
  deriving DecidableEq

/-- An ordered analysis log entry for each read of the Extract table: a Server session's root derivation with the family's reply, the Beacon's root derivation, or an adversary query inside the table domain. -/
inductive Touch where
  | session (index : Nat) (message : PqxdhJointDhExtractFamily.Message) (root : Option RootOutput)
  | beacon (message : PqxdhJointDhExtractFamily.Message)
  | adversary (bytes : Pqxdh.Bytes)

/-- Frozen copy of the logs at the Beacon's acceptance, together with the accepted fields. -/
structure Snapshot where
  accepted : Accepted
  touches : List Touch
  seals : List (Nat × RawCtxSourceSend.SealContext)

/-- Analysis state that the handler writes and never returns: table touches, successful sequence-one seals by session, and the write-once acceptance snapshot. -/
structure Ghost where
  touches : List Touch
  seals : List (Nat × RawCtxSourceSend.SealContext)
  acceptance : Option Snapshot

/-- The empty ghost. -/
def Ghost.empty : Ghost := ⟨[], [], none⟩

/-- Record an acceptance: the first acceptance freezes the current logs; the ghost is otherwise unchanged. -/
def Ghost.accept (ghost : Ghost) : Option Accepted → Ghost
  | none => ghost
  | some accepted =>
      match ghost.acceptance with
      | none => { ghost with acceptance := some ⟨accepted, ghost.touches, ghost.seals⟩ }
      | some _ => ghost

/-- Complete experiment state: the shared BLAKE2b cache, the Server object (peers, control, identity and consumed registration IDs), the pending registration tokens by session, the target Beacon, the session counter and the ghost. -/
structure GameState (KemSK : Type) where
  ctx : CtxRomAuth.CtxRO.QueryCache
  server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)
  pending : Nat → Option PqxdhServerRelatedRootConsumer.Returned
  beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK
  sessions : Nat
  ghost : Ghost

/-- The experiment's oracle monad: game state over programs that query the root-valued Extract family interface. -/
abbrev Game (KemSK : Type) := StateT (GameState KemSK) (OracleComp RootSpec)

/-- Uniform coins of a probabilistic computation, as family coin queries. -/
def familyCoins {α : Type} (work : ProbComp α) : OracleComp RootSpec α :=
  simulateQ (fun query => (RootSpec.query (.inl query) : OracleComp RootSpec _)) work

/-- A probabilistic computation inside the game, leaving the state unchanged. -/
def liftCoins {α : Type} (work : ProbComp α) : Game KemSK α :=
  StateT.lift (familyCoins work)

/-- Forward one family request unchanged. -/
def forwardFamily (query : RootSpec.Domain) : Game KemSK (RootSpec.Range query) :=
  StateT.lift (RootSpec.query query : OracleComp RootSpec _)

/-- Append one table touch to the ghost. -/
def recordTouch (touch : Touch) : Game KemSK Unit :=
  modify fun state => { state with ghost := { state.ghost with touches := state.ghost.touches ++ [touch] } }

/-- Run a computation on the shared BLAKE2b cache (with a unit auxiliary state) inside the game. -/
def onCtx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) : Game KemSK α :=
  fun state => do
    let result ← familyCoins (work.run ((), state.ctx))
    pure (result.1, { state with ctx := result.2.2 })

/-- A stateless callback interpretation inside the game: every answer is a lifted probabilistic computation, and the game state is unchanged. -/
def liftUnit {ι' : Type} {spec : OracleSpec ι'} (impl : QueryImpl spec (StateT Unit ProbComp)) :
    QueryImpl spec (Game KemSK) :=
  fun query => liftCoins ((impl query).run' ())

/-! ## Server oracles -/

/-- The 32-byte word of a byte string of length 32, and nothing otherwise. -/
def toWord32 (bytes : Pqxdh.Bytes) : Option Word32 :=
  if width : bytes.length = 32 then some (rootArray ⟨bytes, width⟩) else none

/-- Server ephemeral generation: a uniform 32-byte X25519 scalar and its public key. -/
def generateEphemeral (setup : Setup baseSpec KemSK) :
    ProbComp (Option (PqxdhServerRootPreparation.Ephemeral ScalarBytes)) := do
  let secret ← PqxdhJointGapDh.sampleScalar
  pure (some ⟨secret, rootArray (setup.dh.publicKey secret)⟩)

/-- Server encapsulation to the supplied ML-KEM key through the fixed ambient interpreter. -/
def encapsulate (setup : Setup baseSpec KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey) :
    ProbComp (Option (Ciphertext × Word32)) :=
  simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
    ((fun result => some (PqxdhAcceptedRegistration.ciphertextArray result.1, rootArray result.2)) <$>
      setup.kem.encaps key)

/-- The Server's Phase 1 callbacks, over its consumed registration IDs: the codec getters, attached Ed25519 verification, the point and key checks, the consumed-set status, a fresh ephemeral, encapsulation, the public identity conversion and ephemeral X25519. The static DH callback is never reached, because `PqxdhServerStaticDhSource.prefixImpl` answers it with a public reference. -/
def serverAux (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl (PqxdhServerRootPreparation.Spec Reader ScalarBytes Unit) (StateT (List Pqxdh.Bytes) ProbComp)
  | .decode raw => pure (codec.read1 raw)
  | .identity reader => pure (codec.identity reader)
  | .identityPoint identity => pure (checks.identityPoint identity)
  | .pqField reader => pure (codec.pqField reader)
  | .preField reader => pure (codec.preField reader)
  | .oneField reader => pure (codec.oneField reader)
  | .verify identity bytes => pure (setup.source.crypto.verify identity.toList bytes)
  | .registrationStatus rid => fun consumed =>
      pure (if rid ∈ consumed then pqxdh.RegistrationStatus.Consumed else .Fresh, consumed)
  | .reserveRegistration => pure checks.reserveRegistration
  | .parseDh point => pure (checks.x25519Point point)
  | .generate => StateT.lift (generateEphemeral setup)
  | .parseKem key => pure (checks.kemKey key)
  | .encapsulate key => StateT.lift (encapsulate setup key)
  | .publicConversion identity => pure ((setup.source.crypto.xpkConv identity.toList).bind toWord32)
  | .privateConversion => pure true
  | .staticDh _ => pure none
  | .ephemeralDh secret point => pure ((sourceScalarDh setup.source.crypto secret (peer point)).map rootArray)

/-- The Server's ordered Phase 1 prefix (decoding, verification, freshness, generation, encapsulation and DH1 to DH4) with the static DH as a public reference; it holds no Server seed. -/
noncomputable def serverPrefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) :
    StateT (List Pqxdh.Bytes) ProbComp (Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)) :=
  simulateQ (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain (serverAux setup codec checks) (fun _ => pure ()))
    (PqxdhServerRootPreparation.collect raw)

/-- The Server's binding: its identity public key and compiled-in identity key ID. -/
def binding (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) : pqxdh.ServerBinding :=
  ⟨rootArray publicValue.identity.ed25519, setup.serverKeyId⟩

/-- Family requests of Server session `index`: forwarded unchanged, and a root derivation is logged, with the family's reply, as a touch of that session. -/
def sessionFamily (index : Nat) : QueryImpl RootSpec (Game KemSK)
  | .inl coin => forwardFamily (.inl coin)
  | .inr (.sign message) => forwardFamily (.inr (.sign message))
  | .inr (.publicHmac key message) => forwardFamily (.inr (.publicHmac key message))
  | .inr (.derive message) => do
      let reply ← forwardFamily (.inr (.derive message))
      recordTouch (.session index message reply)
      pure reply

/-- Callbacks of the Server's root consumer: the family requests of session `index`, no-op erasures, and consumption of the registration ID. -/
def sessionImpl (index : Nat) : QueryImpl PqxdhServerRelatedRootConsumer.Spec (Game KemSK)
  | .inl query => sessionFamily index query
  | .inr .eraseShared => pure ()
  | .inr .eraseInput => pure ()
  | .inr (.consume rid) => modify fun state =>
      { state with server := { state.server with consumed := state.server.consumed ++ [absBytes rid.bytes] } }

/-- `get_shared_secret` (`server.rs:332-422`): the next session index is allocated, the Phase 1 prefix runs, the extracted `server_accept` path derives the root through one family request, and on success the registration ID is consumed and the pending token is stored under the session index, which is returned. -/
noncomputable def acceptOracle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) : Game KemSK (Option Nat) := do
  let state ← get
  let index := state.sessions
  let collected ← liftCoins ((serverPrefix setup codec checks raw).run state.server.consumed)
  set { state with sessions := index + 1, server := { state.server with consumed := collected.2 } }
  match collected.1 with
  | none => pure none
  | some input =>
      let returned ← simulateQ (sessionImpl index)
        (PqxdhServerRelatedRootConsumer.client (binding setup publicValue) input)
      match returned with
      | .ok (some token) => do
          modify fun current => { current with pending := Function.update current.pending index (some token) }
          pure (some index)
      | _ => pure none

/-- The Server's response-tail callbacks: the Beacon-identity check, the allocation outcomes, a no-op erasure and the Phase 2 writer. They are stateless for every auxiliary state. -/
def tailAux {A : Type} (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .checkIdentity identity => pure (checks.beaconIdentity identity)
  | .reservePeer => pure checks.reservePeer
  | .reservePlaintext length => pure (checks.reservePlaintext length)
  | .erase _ => pure ()
  | .write fields => pure (codec.write2 fields)

/-- The native response tail: real ratchet KDF, AEAD, BLAKE2b on the shared cache and the frame writer (`PqxdhRegistrationProtocolState.registrationImpl`), with the callbacks above. -/
noncomputable def nativeTail {A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.TailSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite (tailAux codec checks) ∘ₛ
    PqxdhServerRegistrationPublication.nativeAdapter

/-- The native response tail with seal logging: a successful seal callback appends its context to the auxiliary log; every answer is the native tail's. -/
noncomputable def tailImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.TailSpec
      (StateT (RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) ProbComp)
  | .inl (.inl request) => nativeTail setup codec checks (.inl (.inl request))
  | .inl (.inr input) => do
      let sealed ← nativeTail setup codec checks (.inl (.inr input))
      if sealed.isSome then
        modify fun state => (state.1 ++ [input.context], state.2)
      pure sealed
  | .inr query => nativeTail setup codec checks (.inr query)

/-- The Server state after a build: an ordinary result installs its state; a diagnostic result keeps the previous state and answers nothing. -/
def settle (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) →
    Option PqxdhServerRegistrationPublication.Response × PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)
  | .ok value => value
  | _ => (none, server)

/-- `build_registration_response` (`server.rs:424-502`): the pending token of `session` is consumed (the Rust token is moved), then the extracted builder assigns the next key ID, seals the sequence-one record under the stored root and writes Phase 2. Seals logged by the tail are added to the ghost under `session`. A session without a pending token answers nothing. -/
noncomputable def buildOracle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) :
    Game KemSK (Option PqxdhServerRegistrationPublication.Response) := do
  let state ← get
  match state.pending session with
  | none => pure none
  | some token => do
      let result ← liftCoins ((simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () state.server)).run
          ([], state.ctx))
      let settled := settle state.server result.1
      set { state with
        pending := Function.update state.pending session none
        server := settled.2
        ctx := result.2.2
        ghost := { state.ghost with seals := state.ghost.seals ++ result.2.1.map (fun context => (session, context)) } }
      pure settled.1

/-! ## Beacon finish -/

/-- The Beacon's Phase 2 callbacks: the codec getters, the public identity conversion, decapsulation with the Beacon's ML-KEM secret, X25519 with the one-time scalar and the identity seed, and a no-op erasure. The prekey is never used here: its two DH values are public references answered by `PqxdhPhase2GapDhSource.prefixImpl`, so the prekey pair callback answers nothing. -/
noncomputable def beaconAux (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response) ProbComp
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind toWord32)
  | .privateConversion () => pure (some ())
  | .decapsulate ciphertext secret => simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (Option.map rootArray <$> setup.kem.decaps secret (PqxdhPhase2InputBytes.ciphertext ciphertext))
  | .dhPair (.inl ()) _ => pure none
  | .dhPair (.inr scalar) point => pure ((sourceScalarDh setup.source.crypto scalar (peer point)).map rootArray)
  | .dhIdentity () point => pure ((setup.joint.staticDh beaconSeed (peer point)).map rootArray)
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

/-- The Beacon's Phase 2 callbacks as a stateless state computation. -/
noncomputable def beaconAuxUnit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response) (StateT Unit ProbComp) :=
  fun query => StateT.lift (beaconAux setup codec beaconSeed query)

/-- The Beacon's Phase 2 preparation with the prekey as a public reference (`PqxdhPhase2GapDhSource.prefixImpl`): decoding, conversions, decapsulation, the DH values and the admission test, as a stateless probabilistic computation. -/
noncomputable def beaconPrefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    StateT Unit ProbComp (Option (PqxdhPhase2DhMetadata.Prepared Response)) :=
  simulateQ (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain (beaconAuxUnit setup codec beaconSeed) (fun _ => pure ()))
    (PqxdhPhase2DhMetadata.prepare control identity oneTime kem raw)

/-- The Beacon's native tail callbacks: real ratchet KDF, BLAKE2b on the shared cache and AEAD opening, the fixed initial KDF and the application getter. The root callback is never reached, because the related-root tail derives the root through the family. -/
noncomputable def beaconNative (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response)
      (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp)
  | .inl query => RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) query
  | .inr (.root _) => pure none
  | .inr (.initial request) => pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request)
  | .inr (.application response) => pure (codec.application response)

/-- Family requests of the Beacon: forwarded unchanged, and its root derivation is logged as a Beacon touch. -/
def beaconFamily : QueryImpl RootSpec (Game KemSK)
  | .inl coin => forwardFamily (.inl coin)
  | .inr (.sign message) => forwardFamily (.inr (.sign message))
  | .inr (.publicHmac key message) => forwardFamily (.inr (.publicHmac key message))
  | .inr (.derive message) => do
      recordTouch (.beacon message)
      forwardFamily (.inr (.derive message))

/-- The Beacon's executable Phase 2 stage callbacks: the preparation with the prekey as a public reference, the family requests and the native tail on the shared cache. -/
noncomputable def stageImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed) :
    QueryImpl (PqxdhPhase2DhStage.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response) (Game KemSK)
  | .inl query => liftUnit (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain (beaconAuxUnit setup codec beaconSeed)
      (fun _ => pure ())) query
  | .inr (.inl query) => beaconFamily query
  | .inr (.inr query) => onCtx (beaconNative setup codec query)

/-- The fields a staged Beacon registration accepts. -/
def Accepted.ofStaged (staged : PqxdhBeaconPhase2Publication.Staged) : Accepted :=
  ⟨staged.authenticated.candidate.assigned_key_id, staged.opened.plaintext.drop 8, absBytes staged.associatedData⟩

/-- The accepted fields of a finish, present exactly when the finish returned a payload. -/
def acceptedOf (staged : Option PqxdhBeaconPhase2Publication.Staged) (output : Option Pqxdh.Bytes) : Option Accepted :=
  if output.isSome then staged.map Accepted.ofStaged else none

/-- The target Beacon's finish (`beacon.rs:402-510`): in the InitSent phase the executable preparation and related-root tail run (the root derivation is one family request, logged as the Beacon's touch), then the unchanged final checks `PqxdhBeaconPhase2Publication.finish` publish or abort; an acceptance freezes the ghost logs. In every other phase the finish answers nothing, so it is single-shot. -/
noncomputable def finishOracle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) :
    Game KemSK (Option Pqxdh.Bytes) := do
  let state ← get
  match state.beacon.beacon.phase with
  | .initSent control _ oneTime kem => do
      let staged ← simulateQ (stageImpl setup codec beaconSeed)
        (PqxdhPhase2DhStage.stage publicValue codec.frameRead control state.beacon.beacon.identity oneTime kem raw)
      let current ← get
      let result := PqxdhBeaconPhase2Publication.finish control current.beacon staged
      set { current with beacon := result.2, ghost := current.ghost.accept (acceptedOf staged result.1) }
      pure result.1
  | _ => pure none

/-! ## Public oracles and the handler -/

/-- The public HMAC: forwarded to the family, and logged as an adversary touch inside the table domain. -/
def hmacOracle (key : HmacBlock) (message : Pqxdh.Bytes) : Game KemSK HmacBlock := do
  if key = zeroSalt ∧ message.length = 192 then
    recordTouch (.adversary message)
  forwardFamily (.inr (.publicHmac key message))

/-- The BLAKE2b random oracle on the shared cache. -/
noncomputable def hashOracle (bytes : Pqxdh.Bytes) : Game KemSK CtxRomAuth.CtxDigest := fun state => do
  let result ← familyCoins ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.ctx)
  pure (result.1, { state with ctx := result.2 })

/-- The post-registration state of a Server session: the kernel installed by `publish`, and nothing else. -/
def revealKernel (keyId : Std.U64) (state : GameState KemSK) : Option ratchet.concrete.ConcreteRatchetKernel :=
  (state.server.server.peers keyId).map RawCtxServerRouting.Peer.kernel

/-- The experiment handler. Coins and public HMAC queries reach the family; accept, build, finish, BLAKE2b and reveal act on the game state. -/
noncomputable def authHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) : QueryImpl ServerAuthSpec (Game KemSK)
  | .inl coin => forwardFamily (.inl coin)
  | .inr (.accept raw) => acceptOracle setup codec checks publicValue raw
  | .inr (.build session payload) => buildOracle setup codec checks session payload
  | .inr (.finish raw) => finishOracle setup codec publicValue beaconSeed raw
  | .inr (.hmac key message) => hmacOracle key message
  | .inr (.hash bytes) => hashOracle bytes
  | .inr (.reveal keyId) => fun state => pure (revealKernel keyId state, state)

/-! ## Phase 1 and the games -/

/-- The target Beacon's public projection: its identity public key, the Gap-DH prekey for the prekey handle and the public key of the one-time scalar, and its ML-KEM public key. -/
def projection (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) : PqxdhLivePhase1Bundle.Public Unit (Unit ⊕ ScalarBytes) KemSK where
  index _ := 0
  identity _ := (setup.joint.publicKeys beaconSeed).ed25519
  dh
    | .inl () => publicValue.prekey
    | .inr scalar => setup.dh.publicKey scalar
  kem _ := kemPk

/-- The Beacon's Phase 1 callbacks: the one-time generator returns the sampled one-time scalar, signing requests are signed with the Beacon's identity seed, other identity-pool requests answer nothing, and the writer is the codec's. -/
def phase1Impl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (oneTime : ScalarBytes) : QueryImpl (PqxdhLivePhase1Bundle.Spec (Unit ⊕ ScalarBytes)) ProbComp
  | .inl () => pure (some (.inr oneTime))
  | .inr (.inl (.inl coin)) => (unifSpec.query coin : ProbComp _)
  | .inr (.inl (.inr .create)) => pure none
  | .inr (.inl (.inr (.service _ (.sign message)))) => pure (some (setup.joint.sign beaconSeed message))
  | .inr (.inl (.inr (.service _ (.staticDh _)))) => pure none
  | .inr (.inl (.inr (.reveal _))) => pure none
  | .inr (.inr bundle) => pure (codec.write1 bundle)

/-- The fresh target Beacon (`beacon.rs:59-80`): pinned to the Server's binding, with the prekey handle and the ML-KEM secret. -/
def freshBeacon (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge) (kemSk : KemSK) :
    RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK :=
  ⟨⟨(), setup.serverKeyId, rootArray publicValue.identity.ed25519,
    .fresh ⟨binding setup publicValue⟩ (.inl ()) kemSk⟩, 0⟩

/-- The Beacon's Phase 1 publication through the existing bundle program. -/
def phase1Run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    ProbComp (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) :=
  simulateQ (phase1Impl setup codec beaconSeed oneTime)
    (PqxdhLivePhase1Bundle.bundle (projection setup publicValue beaconSeed kemPk) (freshBeacon setup publicValue kemSk))

/-- The initial game state: an empty BLAKE2b cache, the fresh Server (`server.rs:148-167`), no pending token, the published Beacon, no session and an empty ghost. -/
def initialGameState (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) : GameState KemSK where
  ctx := ∅
  server := ⟨⟨rootArray publicValue.identity.ed25519, fun _ => none, ()⟩, setup.serverKeyId, ⟨setup.serverKeyId⟩, []⟩
  pending := fun _ => none
  beacon := beacon
  sessions := 0
  ghost := Ghost.empty

/-- The experiment body, which uses neither the Server seed nor the Beacon's prekey scalar: it samples the Beacon's identity seed, one-time scalar and ML-KEM key pair, publishes Phase 1, and runs the adversary against the handler. `revealed` is the negative control's Server seed. -/
noncomputable def body (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealed : Option IdentitySeed) (publicValue : PublicChallenge) :
    OracleComp RootSpec (GameState KemSK) := do
  let beaconSeed ← familyCoins sampleSeed
  let oneTime ← familyCoins PqxdhJointGapDh.sampleScalar
  let keys ← familyCoins (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let published ← familyCoins (phase1Run setup codec beaconSeed publicValue oneTime keys.1 keys.2)
  let input : AuthInput := ⟨publicValue.identity, setup.serverKeyId, published.1, revealed⟩
  Prod.snd <$> (simulateQ (authHandler setup codec checks publicValue beaconSeed) (adversary input)).run
    (initialGameState setup publicValue published.2)

/-- The full experiment: the Server seed and the Beacon's prekey scalar are sampled first, inside the game; the body runs under the Extract random-oracle family. The result keeps both secrets, the final game state and the family state for the analysis events. -/
noncomputable def gameState (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    ProbComp (IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State) := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar
  let result ← (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
      PqxdhJointDhExtractRoot.reduction)
    (body setup codec checks adversary (if revealSeed then some seed else none) publicValue)).run
      PqxdhJointDhExtractFamily.empty
  pure (seed, scalar, result.1, result.2)

/-! ## Events -/

/-- The message of the Beacon's first logged derivation. -/
def firstBeacon (touches : List Touch) : Option PqxdhJointDhExtractFamily.Message :=
  touches.findSome? fun
    | .beacon message => some message
    | _ => none

section Events
variable (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)

/-- The actual 192-byte root input of a family request, computed with the Server seed and the Beacon's prekey scalar, which only the experiment holds. -/
def rootInput (message : PqxdhJointDhExtractFamily.Message) : Option Pqxdh.Bytes :=
  PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message

/-- The root input of the Beacon's first logged derivation. -/
def beaconInput (touches : List Touch) : Option Pqxdh.Bytes :=
  (firstBeacon touches).bind (rootInput setup seed scalar)

/-- Partnering by identical root derivation: Server session `index` derived, before the snapshot, the Beacon's root input. -/
def Partner (snap : Snapshot) (index : Nat) : Prop :=
  ∃ message reply bytes, Touch.session index message reply ∈ snap.touches ∧
    rootInput setup seed scalar message = some bytes ∧ beaconInput setup seed scalar snap.touches = some bytes

/-- The fields a Server seal fixes: the target key ID, the payload after the 8-byte key-ID binding and the associated data. -/
def sealed (context : RawCtxSourceSend.SealContext) : Accepted :=
  ⟨context.targetId, context.plaintext.drop 8, context.associatedData⟩

/-- W1: the Beacon accepted and no Server session had derived its root input. -/
def W1 (ghost : Ghost) : Prop :=
  ∃ snap, ghost.acceptance = some snap ∧ ∀ index, ¬ Partner setup seed scalar snap index

/-- W2: the Beacon accepted, a partner exists, and no seal of any partner before the acceptance has the accepted key ID, payload and associated data. -/
def W2 (ghost : Ghost) : Prop :=
  ∃ snap, ghost.acceptance = some snap ∧ (∃ index, Partner setup seed scalar snap index) ∧
    ∀ index, Partner setup seed scalar snap index →
      ∀ context, (index, context) ∈ snap.seals → sealed context ≠ snap.accepted

/-- W3: two distinct partners at the acceptance (injective agreement fails). -/
def W3 (ghost : Ghost) : Prop :=
  ∃ snap, ghost.acceptance = some snap ∧
    ∃ i j, i ≠ j ∧ Partner setup seed scalar snap i ∧ Partner setup seed scalar snap j

/-- The winning event, frozen at the Beacon's acceptance. -/
def Win (ghost : Ghost) : Prop :=
  W1 setup seed scalar ghost ∨ W2 setup seed scalar ghost ∨ W3 setup seed scalar ghost

/-- Analysis event: the adversary queried the table at the Beacon's root input (final log). -/
def BadB (ghost : Ghost) : Prop :=
  ∃ bytes, beaconInput setup seed scalar ghost.touches = some bytes ∧ Touch.adversary bytes ∈ ghost.touches

/-- Narrowed collision: two distinct Server sessions derived the Beacon's root input (final log). -/
def CollB (ghost : Ghost) : Prop :=
  ∃ i j mi mj ri rj bytes, i ≠ j ∧ Touch.session i mi ri ∈ ghost.touches ∧ Touch.session j mj rj ∈ ghost.touches ∧
    beaconInput setup seed scalar ghost.touches = some bytes ∧
    rootInput setup seed scalar mi = some bytes ∧ rootInput setup seed scalar mj = some bytes

/-- The table input a touch reads: a derivation's actual root input, or the adversary's message. -/
def touchInput : Touch → Option Pqxdh.Bytes
  | .session _ message _ => rootInput setup seed scalar message
  | .beacon message => rootInput setup seed scalar message
  | .adversary bytes => some bytes

/-- The owner of the Beacon's table entry: the first touch at the Beacon's root input is session `j < Q` (owner `j`), the Beacon (owner `Q`) or the adversary (no owner); a session index `Q` or above has no owner. By convention the owner is the Beacon when its derivation has no root input, which a successful finish excludes in the real run. -/
def entryOwner (Q : Nat) (ghost : Ghost) : Option (Fin (Q + 1)) :=
  match beaconInput setup seed scalar ghost.touches with
  | none => some (Fin.last Q)
  | some bytes =>
      match ghost.touches.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes)) with
      | some (.session index _ _) => if bound : index < Q then some ⟨index, Nat.lt_succ_of_lt bound⟩ else none
      | some (.adversary _) => none
      | _ => some (Fin.last Q)

/-- The per-entry event `E_j`: W1 or W2 without the adversary's table query at the Beacon's input, without a session collision, and with owner `j`. -/
def EntryEvent (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost) : Prop :=
  (W1 setup seed scalar ghost ∨ W2 setup seed scalar ghost) ∧ ¬ BadB setup seed scalar ghost ∧
    ¬ CollB setup seed scalar ghost ∧ entryOwner setup seed scalar Q ghost = some j

end Events

/-- The DH1 coordinates of the table queries in a family history (zero key, 192 bytes), in order. -/
def romCandidates (history : PqxdhJointDhExtractFamily.History) : List DhOutput :=
  history.filterMap fun
    | .publicHmac key message _ =>
        if key = zeroSalt ∧ message.length = 192 then readDh 32 message else none
    | _ => none

/-- A candidate list truncated or padded with the zero value to a fixed width; the zero value never wins the Gap-DH game. -/
def padded (count : Nat) (values : List DhOutput) : List.Vector DhOutput count :=
  ⟨(values ++ List.replicate count zeroDh).take count, by simp⟩

/-- The Gap-DH scan event, read from the family history: the nonzero cross DH value DH1 is among the padded candidates. -/
def CandHit (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (qH : Nat)
    (history : PqxdhJointDhExtractFamily.History) : Prop :=
  ∃ value, setup.joint.staticDh seed (setup.dh.publicKey scalar) = some value ∧ value ≠ zeroDh ∧
    value ∈ (padded qH (romCandidates history)).toList

/-- The executable experiment: the winning event of the final ghost. -/
noncomputable def serverAuthGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp Bool := by
  classical
  exact (fun result => decide (Win setup result.1 result.2.1 result.2.2.1.ghost)) <$>
    gameState setup codec checks revealSeed adversary

/-- The session-collision game term: the probability of the narrowed collision in the executable experiment. -/
noncomputable def sessionCollGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) : ℝ :=
  (Pr{let result ← gameState setup codec checks false adversary}[CollB setup result.1 result.2.1 result.2.2.1.ghost]).toReal

/-! ## Accepted and sealed fields -/

/-- The accepted fields as the triple used by stage B9a. -/
def Accepted.fields (accepted : Accepted) : Std.U64 × Pqxdh.Bytes × Pqxdh.Bytes :=
  (accepted.keyId, accepted.payload, accepted.associatedData)

/-- The triple determines the accepted fields. -/
theorem fields_inj (left right : Accepted) : left.fields = right.fields ↔ left = right := by
  constructor
  · intro same
    cases left
    cases right
    simp only [Accepted.fields, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    rfl
  · intro same
    rw [same]

/-- A staged Beacon registration accepts exactly the B9a accepted fields. -/
theorem ofStaged_fields (staged : PqxdhBeaconPhase2Publication.Staged) :
    (Accepted.ofStaged staged).fields = PqxdhPhase2LocalMatching.acceptedFields staged :=
  rfl

/-- A Server seal fixes exactly the B9a sealed fields. -/
theorem sealed_fields (context : RawCtxSourceSend.SealContext) :
    (sealed context).fields = PqxdhPhase2LocalMatching.sealedFields context :=
  rfl

/-- The W2 comparison is the B9a comparison of sealed and accepted fields. -/
theorem sealed_eq_iff (context : RawCtxSourceSend.SealContext) (staged : PqxdhBeaconPhase2Publication.Staged) :
    sealed context = Accepted.ofStaged staged ↔
      PqxdhPhase2LocalMatching.sealedFields context = PqxdhPhase2LocalMatching.acceptedFields staged := by
  rw [← sealed_fields, ← ofStaged_fields, fields_inj]

/-! ## Generic simulation lemmas -/

section Generic
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}

/-- A reflexive and transitive relation that every handler step establishes between its pre- and post-states holds between the initial and final states of every simulation. -/
theorem run_rel (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) (R : σ → σ → Prop)
    (refl : ∀ state, R state state) (trans : ∀ a b c, R a b → R b c → R a c)
    (step : ∀ query state result, result ∈ support ((impl query).run state) → R state result.2)
    {α : Type} (oa : OracleComp spec₁ α) (state : σ) (result : α × σ)
    (supported : result ∈ support ((simulateQ impl oa).run state)) : R state result.2 := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact refl state
  | query_bind query next ih =>
      have split : result ∈ support (((simulateQ impl
          (OracleSpec.query query : OracleComp spec₁ (spec₁.Range query))).run state) >>=
            fun middle => (simulateQ impl (next middle.1)).run middle.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using supported
      obtain ⟨middle, first, rest⟩ := (mem_support_bind_iff _ _ _).1 split
      have first' : middle ∈ support ((impl query).run state) := by
        simpa [simulateQ_spec_query] using first
      exact trans _ _ _ (step query state middle first') (ih middle.1 middle.2 rest)

/-- A counter that each step raises by at most one on a `p`-query, and not at all otherwise, rises by at most the `p`-query bound over a simulation. -/
theorem run_count (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) (p : ι₁ → Prop) [DecidablePred p]
    (count : σ → Nat)
    (step : ∀ query state result, result ∈ support ((impl query).run state) →
      count result.2 ≤ count state + if p query then 1 else 0)
    {α : Type} (oa : OracleComp spec₁ α) (bound : Nat) (bounded : oa.IsQueryBoundP p bound) (state : σ)
    (result : α × σ) (supported : result ∈ support ((simulateQ impl oa).run state)) :
    count result.2 ≤ count state + bound := by
  induction oa using OracleComp.inductionOn generalizing state bound with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact Nat.le_add_right _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have split : result ∈ support (((simulateQ impl
          (OracleSpec.query query : OracleComp spec₁ (spec₁.Range query))).run state) >>=
            fun middle => (simulateQ impl (next middle.1)).run middle.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using supported
      obtain ⟨middle, first, rest⟩ := (mem_support_bind_iff _ _ _).1 split
      have first' : middle ∈ support ((impl query).run state) := by
        simpa [simulateQ_spec_query] using first
      have now := step query state middle first'
      have later := ih middle.1 _ (bounded.2 middle.1) middle.2 rest
      by_cases hp : p query
      · simp only [hp, ite_true] at now later
        have positive := bounded.1.resolve_left (not_not.mpr hp)
        omega
      · simp only [hp, ite_false] at now later
        omega

/-- Support of a bind in a state monad over oracle computations: every result comes from a first result and a continuation result. -/
theorem run_bind_support {α β : Type} (first : StateT σ (OracleComp spec₂) α)
    (next : α → StateT σ (OracleComp spec₂) β) (state : σ) (result : β × σ)
    (supported : result ∈ support ((first >>= next).run state)) :
    ∃ middle ∈ support (first.run state), result ∈ support ((next middle.1).run middle.2) := by
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  exact supported

end Generic

/-! ## Step lemmas for the building blocks -/

section Blocks

/-- A probabilistic computation leaves the game state unchanged. -/
theorem liftCoins_support {α : Type} (work : ProbComp α) (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((liftCoins work).run state)) : result.2 = state := by
  simp only [liftCoins, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Coin queries reach every value, so a lifted computation has no more outcomes than the computation itself. -/
theorem coins_support {α : Type} (work : ProbComp α) (value : α) (supported : value ∈ support (familyCoins work)) :
    value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure result =>
      simpa [familyCoins] using supported
  | query_bind query next ih =>
      simp only [familyCoins, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _, rest⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query _ _, ih reply rest⟩

/-- A probabilistic computation inside the game returns one of its own outcomes and leaves the state unchanged. -/
theorem liftCoins_mem {α : Type} (work : ProbComp α) (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((liftCoins work).run state)) : result.1 ∈ support work ∧ result.2 = state := by
  simp only [liftCoins, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨value, member, rfl⟩ := supported
  exact ⟨coins_support work value member, rfl⟩

/-- A forwarded family request leaves the game state unchanged. -/
theorem forward_support (query : RootSpec.Domain) (state : GameState KemSK)
    (result : RootSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((forwardFamily query).run state)) : result.2 = state := by
  simp only [forwardFamily, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Work on the shared cache changes only the cache. -/
theorem onCtx_support {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((onCtx work).run state)) : ∃ cache, result.2 = { state with ctx := cache } := by
  simp only [onCtx, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact ⟨_, rfl⟩

/-- Recording a touch appends it to the ghost's touch log. -/
theorem record_run (touch : Touch) (state : GameState KemSK) :
    (recordTouch touch).run state =
      pure ((), { state with ghost := { state.ghost with touches := state.ghost.touches ++ [touch] } }) :=
  rfl

/-- Lifted coins of a returned value are that value. -/
theorem liftCoins_pure {α : Type} (value : α) : (liftCoins (pure value) : Game KemSK α) = pure value := by
  funext state
  simp [liftCoins, familyCoins, StateT.lift]
  rfl

/-- Lifted coins distribute over bind. -/
theorem liftCoins_bind {α β : Type} (first : ProbComp α) (next : α → ProbComp β) :
    (liftCoins (first >>= next) : Game KemSK β) = liftCoins first >>= fun value => liftCoins (next value) := by
  funext state
  change (liftCoins (first >>= next)).run state = (liftCoins first >>= fun value => liftCoins (next value)).run state
  simp only [liftCoins, familyCoins, StateT.run_lift, StateT.run_bind, simulateQ_bind, bind_assoc, pure_bind]

/-- Lifting a stateless callback interpretation commutes with simulation: the simulated program is one lifted probabilistic computation. -/
theorem simulateQ_liftUnit {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (impl : QueryImpl spec (StateT Unit ProbComp)) (oa : OracleComp spec α) :
    simulateQ (liftUnit (KemSK := KemSK) impl) oa = liftCoins ((simulateQ impl oa).run' ()) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simp [liftCoins_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, ih]
      rw [liftUnit, ← liftCoins_bind]
      congr 1
      simp only [StateT.run'_eq, StateT.run_bind, map_bind, bind_map_left]

end Blocks

/-! ## Sub-handler steps -/

section SubHandlers

/-- The Server's root consumer for session `index`: when the local nonzero test fails it logs nothing; when it passes it logs exactly one touch of session `index` at the session's root request, with the family's reply; and a returned token carries that reply as its root and the reconstructed pending registration of the input. Only the consumed registration IDs and the touch log change. -/
theorem client_run (index : Nat) (serverBinding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (state : GameState KemSK)
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) × GameState KemSK)
    (supported : result ∈ support ((simulateQ (sessionImpl index)
      (PqxdhServerRelatedRootConsumer.client serverBinding input)).run state)) :
    ∃ consumed extra,
      result.2 = ({ state with server := { state.server with consumed := consumed }, ghost := { state.ghost with touches := state.ghost.touches ++ extra } }) ∧
      (¬ PqxdhServerRelatedRootInput.localNonzero input ∧ extra = [] ∨ PqxdhServerRelatedRootInput.localNonzero input ∧
        ∃ reply, extra = [Touch.session index (PqxdhServerRelatedRootInput.message input) reply]) ∧
      ∀ token, result.1 = ok (some token) → PqxdhServerRelatedRootInput.localNonzero input ∧
        extra = [Touch.session index (PqxdhServerRelatedRootInput.message input) (some token.root)] ∧
        token.pending = PqxdhServerClearedRoot.pending serverBinding input := by
  classical
  simp only [PqxdhServerRelatedRootConsumer.client, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨erased, erasedRun, supported⟩ := supported
  simp only [sessionImpl, StateT.run_pure, support_pure, Set.mem_singleton_iff] at erasedRun
  subst erasedRun
  by_cases valid : PqxdhServerRelatedRootInput.localNonzero input
  · simp only [valid, not_true_eq_false, ite_false, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at supported
    obtain ⟨derived, derivedRun, supported⟩ := supported
    simp only [sessionImpl, sessionFamily, StateT.run_bind, mem_support_bind_iff] at derivedRun
    obtain ⟨forwarded, forwardedRun, derivedRun⟩ := derivedRun
    have same := forward_support _ _ _ forwardedRun
    simp only [record_run, StateT.run_pure, support_pure, Set.mem_singleton_iff, same] at derivedRun
    obtain ⟨_, rfl, rfl⟩ := derivedRun
    obtain ⟨erasedInput, erasedInputRun, supported⟩ := supported
    simp only [sessionImpl, StateT.run_pure, support_pure, Set.mem_singleton_iff] at erasedInputRun
    subst erasedInputRun
    cases hreply : forwarded.1 with
    | none =>
        simp only [hreply, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        refine ⟨state.server.consumed, [Touch.session index (PqxdhServerRelatedRootInput.message input) none], rfl,
          Or.inr ⟨valid, none, rfl⟩, fun token found => ?_⟩
        simp at found
    | some root =>
        simp only [hreply, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
        obtain ⟨consumedRun, consumedMember, supported⟩ := supported
        simp only [sessionImpl] at consumedMember
        subst consumedMember
        subst supported
        refine ⟨_, [Touch.session index (PqxdhServerRelatedRootInput.message input) (some root)], rfl,
          Or.inr ⟨valid, some root, rfl⟩, fun token found => ?_⟩
        simp only [RustM.ok.injEq, Option.some.injEq] at found
        subst found
        exact ⟨valid, rfl, rfl⟩
  · simp only [valid, not_false_eq_true, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    subst supported
    refine ⟨state.server.consumed, [], by simp, Or.inl ⟨valid, rfl⟩, fun token found => ?_⟩
    simp at found

/-- A Beacon Phase 2 preparation that the Beacon's prefix reaches on some run. -/
def BeaconReached (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) : Prop :=
  ∃ final : Unit, (some pending, final) ∈
    support ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run ())

/-- Work on the shared cache only replaces the cache. -/
theorem ctxOnly_run {ι' : Type} {spec : OracleSpec ι'} {α : Type} (impl : QueryImpl spec (Game KemSK))
    (step : ∀ query state result, result ∈ support ((impl query).run state) →
      ∃ cache, result.2 = { state with ctx := cache })
    (oa : OracleComp spec α) (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ impl oa).run state)) :
    ∃ cache, result.2 = { state with ctx := cache } :=
  run_rel impl (fun before after => ∃ cache, after = { before with ctx := cache })
    (fun state => ⟨state.ctx, rfl⟩)
    (fun _ _ _ left right => by
      obtain ⟨first, rfl⟩ := left
      obtain ⟨second, rfl⟩ := right
      exact ⟨second, rfl⟩)
    step oa state result supported

/-- The Beacon's executable Phase 2 stage in the game: the preparation leaves the state unchanged. When the Beacon's prefix yields no preparation, the stage logs nothing and answers nothing; when it reaches a preparation, the stage logs exactly one Beacon touch, at the Beacon's root request for that preparation. Only the touch log and the shared cache change. -/
theorem stage_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option PqxdhBeaconPhase2Publication.Staged × GameState KemSK)
    (supported : result ∈ support ((simulateQ (stageImpl setup codec beaconSeed)
      (PqxdhPhase2DhStage.stage publicValue codec.frameRead control identity oneTime kem raw)).run state)) :
    ∃ cache extra,
      result.2 = ({ state with ctx := cache, ghost := { state.ghost with touches := state.ghost.touches ++ extra } }) ∧
      ((extra = [] ∧ result.1 = none ∧ ∃ final : Unit, (none, final) ∈
          support ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run ())) ∨ ∃ pending,
        BeaconReached setup codec beaconSeed control identity oneTime kem raw pending ∧
          extra = [Touch.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)]) := by
  simp only [PqxdhPhase2DhStage.stage, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, preparedRun, supported⟩ := supported
  rw [← QueryImpl.simulateQ_compose] at preparedRun
  have prefixEq : stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.prefixLift =
      liftUnit (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain (beaconAuxUnit setup codec beaconSeed)
        (fun _ => pure ())) := by
    funext query
    exact simulateQ_spec_query (stageImpl setup codec beaconSeed) _
  rw [prefixEq, simulateQ_liftUnit] at preparedRun
  obtain ⟨member, same⟩ := liftCoins_mem _ _ _ preparedRun
  rw [same] at supported
  cases hp : prepared.1 with
  | none =>
      have failed : ∃ final : Unit, (none, final) ∈
          support ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run ()) := by
        rw [hp, StateT.run'_eq, support_map] at member
        obtain ⟨⟨value, final⟩, run, eq⟩ := member
        simp only at eq
        subst eq
        exact ⟨final, run⟩
      simp only [hp, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨state.ctx, [], by simp, Or.inl ⟨rfl, rfl, failed⟩⟩
  | some pending =>
      have reached : BeaconReached setup codec beaconSeed control identity oneTime kem raw pending := by
        rw [hp, StateT.run'_eq, support_map] at member
        obtain ⟨⟨value, final⟩, run, eq⟩ := member
        simp only at eq
        subst eq
        exact ⟨final, run⟩
      simp only [hp] at supported
      rw [← QueryImpl.simulateQ_compose] at supported
      simp only [PqxdhPhase2DhRootConsumer.tail, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨rooted, rootRun, supported⟩ := supported
      rw [← QueryImpl.simulateQ_compose] at rootRun
      have rootEq : (stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.tailLift) ∘ₛ
          PqxdhPhase2DhRootConsumer.rootLift = beaconFamily := by
        funext query
        simp only [QueryImpl.apply_compose, PqxdhPhase2DhRootConsumer.rootLift, PqxdhPhase2DhStage.tailLift,
          simulateQ_spec_query]
        rfl
      rw [rootEq] at rootRun
      simp only [PqxdhPhase2DhRootConsumer.root, simulateQ_map, StateT.run_map, simulateQ_spec_query, support_map,
        Set.mem_image] at rootRun
      obtain ⟨derived, derivedRun, rfl⟩ := rootRun
      change derived ∈ support ((recordTouch (KemSK := KemSK)
        (Touch.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)) >>= fun _ =>
          forwardFamily (.inr (.derive (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)))).run
            state) at derivedRun
      rw [StateT.run_bind, record_run, pure_bind] at derivedRun
      have recorded := forward_support _ _ _ derivedRun
      cases hr : derived.1 with
      | none =>
          simp only [hr, Option.map_none, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨state.ctx, [Touch.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)],
            by simp only [recorded], Or.inr ⟨pending, reached, rfl⟩⟩
      | some value =>
          simp only [hr, Option.map_some] at supported
          rw [← QueryImpl.simulateQ_compose] at supported
          have nativeEq : (stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.tailLift) ∘ₛ
              PqxdhPhase2DhRootConsumer.nativeLift = fun query => onCtx (beaconNative setup codec query) := by
            funext query
            simp only [QueryImpl.apply_compose, PqxdhPhase2DhRootConsumer.nativeLift, PqxdhPhase2DhStage.tailLift,
              simulateQ_spec_query]
            rfl
          rw [nativeEq] at supported
          obtain ⟨cache, eq⟩ := ctxOnly_run _ (fun query state result supported =>
            onCtx_support _ _ _ supported) _ _ result supported
          exact ⟨cache, [Touch.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)],
            by rw [eq, recorded], Or.inr ⟨pending, reached, rfl⟩⟩

/-- A 32-byte word read from a byte string has exactly those bytes. -/
theorem toWord32_some (bytes : Pqxdh.Bytes) (word : Word32) (found : toWord32 bytes = some word) :
    absBytes word = bytes := by
  unfold toWord32 at found
  split at found
  · rename_i width
    cases found
    exact PqxdhRootTableInitialization.rootArray_bytes (⟨bytes, width⟩ : RootOutput)
  · cases found

/-- Every preparation that the Beacon's prefix reaches carries its actual selected references, the actual public conversion of the Server identity and a successful admission test. -/
theorem beaconReached_facts (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (reached : BeaconReached setup codec beaconSeed control identity oneTime kem raw pending) :
    PqxdhPhase2GapDhSource.References setup.beaconDomain pending.collected ∧
      setup.source.crypto.xpkConv (absBytes pending.collected.server) =
        some (absBytes pending.collected.serverConverted) ∧
      PqxdhPhase2DhMetadata.admitted control pending.collected = some pending.metadata := by
  obtain ⟨final, run⟩ := reached
  simp only [beaconPrefix, PqxdhPhase2DhMetadata.prepare, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at run
  obtain ⟨⟨collected, middle⟩, collectRun, eq⟩ := run
  cases collected with
  | none => simp at eq
  | some value =>
      cases ha : PqxdhPhase2DhMetadata.admitted control value with
      | none => simp [ha] at eq
      | some metadata =>
          simp only [ha, Option.bind_some, Option.map_some, Prod.mk.injEq, Option.some.injEq] at eq
          obtain ⟨rfl, _⟩ := eq
          refine ⟨PqxdhPhase2GapDhSource.collect_references setup.beaconDomain (beaconAuxUnit setup codec beaconSeed)
            (fun _ => pure ()) identity oneTime kem raw () middle value collectRun,
            PqxdhPhase2GapDhSource.collect_conversion setup.beaconDomain setup.source.crypto
              (beaconAuxUnit setup codec beaconSeed) ?_ (fun _ => pure ()) identity oneTime kem raw () middle value
              collectRun, ha⟩
          intro server initial converted after supported
          simp only [beaconAuxUnit, beaconAux, StateT.run_lift, pure_bind, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at supported
          obtain ⟨found, _⟩ := supported
          cases hconv : setup.source.crypto.xpkConv (absBytes server) with
          | none => simp [hconv] at found
          | some bytes =>
              simp only [hconv, Option.bind_some] at found
              rw [toWord32_some bytes converted found.symm]

end SubHandlers

/-! ## Phase 1 -/

section PhaseOne

/-- After Phase 1, if the target Beacon is in the InitSent phase, its control is pinned to the Server's binding. -/
theorem phase1_pinned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (result : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (supported : result ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk)) :
    ∀ control prekey other kem, result.2.beacon.phase = .initSent control prekey other kem →
      control.expected_server_binding = binding setup publicValue := by
  simp only [phase1Run, PqxdhLivePhase1Bundle.bundle, freshBeacon, simulateQ_bind, simulateQ_spec_query,
    mem_support_bind_iff] at supported
  obtain ⟨generated, _, supported⟩ := supported
  intro control prekey other kem phase
  cases generated with
  | none =>
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_none,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases phase
  | some generated =>
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_some,
        simulateQ_bind, mem_support_bind_iff] at supported
      obtain ⟨signed, _, supported⟩ := supported
      cases signed with
      | none =>
          simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          cases phase
      | some bundle =>
          simp only [PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning,
            PqxdhBeaconPhase1Publication.prepare, Option.map_some, simulateQ_bind, simulateQ_spec_query,
            mem_support_bind_iff] at supported
          obtain ⟨written, _, supported⟩ := supported
          cases written with
          | none =>
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              cases phase
          | some bytes =>
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              simp only [PqxdhBeaconPhase1Publication.publish, RawCtxBeaconLifecycle.Phase.initSent.injEq] at phase
              rw [← phase.1]
              rfl

end PhaseOne

/-! ## The seal log of the build tail -/

section SealLog
variable {A : Type}

/-- The shared-cache native primitives change only the cache, never the auxiliary state. -/
theorem nativeImpl_keeps (source : FixedHkdfSha512NoSaltSource) (query : RawCtxSourceOpen.NativeSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState A)
    (result : RawCtxSourceOpen.NativeSpec.Range query × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support
      ((RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run state)) :
    result.2.1 = state.1 := by
  rcases query with request | (bytes | input)
  · change result ∈ support ((RawCtxSourceHkdf.kdfImpl source request).run state) at supported
    rw [RawCtxSourceHkdf.kdf_step, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
  · change result ∈ support ((RawCtxSharedPrimitive.openingImpl source.crypto (.inl bytes)).run state) at supported
    simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  · change result ∈ support ((RawCtxSharedPrimitive.openingImpl source.crypto (.inr input)).run state) at supported
    simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]

/-- The mixed shared primitives with the functional AEAD and writer change only the cache. -/
theorem sharedImpl_keeps (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A)
    (result : RawCtxMixedOwner.NativeSpec.Range query × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support
      ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run state)) :
    result.2.1 = state.1 := by
  rw [RawCtxMixedShared.sharedImpl, QueryImpl.apply_compose] at supported
  exact run_rel _ (fun before after => after.1 = before.1) (fun _ => rfl)
    (fun first second third (left : second.1 = first.1) (right : third.1 = second.1) => right.trans left)
    (fun query state result supported => nativeImpl_keeps source query state result supported) _ state result supported

/-- Every native response-tail callback leaves the auxiliary state unchanged. -/
theorem nativeTail_keeps (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A)
    (result : PqxdhServerRegistrationPublication.TailSpec.Range query × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((nativeTail setup codec checks query).run state)) :
    result.2.1 = state.1 := by
  rw [nativeTail, QueryImpl.apply_compose] at supported
  refine run_rel _ (fun before after => after.1 = before.1) (fun _ => rfl)
    (fun first second third (left : second.1 = first.1) (right : third.1 = second.1) => right.trans left) ?_ _ state result supported
  intro query state result supported
  rcases query with request | request
  · change result ∈ support (((RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite
      (RawCtxSourceHkdf.kdfImpl setup.source) ∘ₛ RawCtxMixedOwner.sendLift) request).run state) at supported
    rw [QueryImpl.apply_compose] at supported
    exact run_rel _ (fun before after => after.1 = before.1) (fun _ => rfl)
      (fun first second third (left : second.1 = first.1) (right : third.1 = second.1) => right.trans left)
      (fun query state result supported => sharedImpl_keeps setup.source codec.frameWrite query state result supported)
      _ state result supported
  · change result ∈ support ((tailAux codec checks request).run state) at supported
    cases request <;> simp only [tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
      rw [supported]

/-- Each logging-tail step extends the seal log, by at most one context and only at a seal callback. -/
theorem tailImpl_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : PqxdhServerRegistrationPublication.TailSpec.Range query ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((tailImpl setup codec checks query).run state)) :
    ∃ extra, result.2.1 = state.1 ++ extra ∧
      extra.length ≤ if PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0 := by
  rcases query with (request | input) | request
  · exact ⟨[], by rw [nativeTail_keeps setup codec checks _ state result supported, List.append_nil], by simp⟩
  · simp only [tailImpl, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, first, rest⟩ := supported
    have kept := nativeTail_keeps setup codec checks _ state middle first
    by_cases present : middle.1.isSome
    · simp only [present, ite_true, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at rest
      refine ⟨[input.context], ?_, by simp [PqxdhServerRegistrationPublication.callKind]⟩
      rw [rest]
      simp only [kept]
    · simp only [present, Bool.false_eq_true, ite_false, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at rest
      refine ⟨[], ?_, by simp⟩
      rw [rest]
      simp only [kept, List.append_nil]
  · exact ⟨[], by rw [nativeTail_keeps setup codec checks _ state result supported, List.append_nil], by simp⟩

/-- A build tail logs at most one seal: the builder makes at most one seal callback (`build_bound`). -/
theorem build_log_length (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
        PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((simulateQ (tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run ([], cache))) :
    result.2.1.length ≤ 1 := by
  have counted := run_count (tailImpl setup codec checks)
    (fun query => PqxdhServerRegistrationPublication.callKind query = .seal) (fun state => state.1.length)
    (fun query state result supported => by
      obtain ⟨extra, eq, bound⟩ := tailImpl_log setup codec checks query state result supported
      rw [eq, List.length_append]
      omega)
    _ 1 (PqxdhServerRegistrationPublication.build_bound setup.source pending root payload () server .seal)
    ([], cache) result supported
  simpa using counted

end SealLog

/-! ## Build results -/

section BuildResults

/-- A trivial abstract ratchet. It only instantiates `PqxdhRootTableInitialization.initialize_refines`, whose conclusions used here do not depend on it. -/
def unitRatchet : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial Unit Unit Unit where
  kdfChain chain := chain
  kdfMsg chain := ⟨⟨chain.bytes⟩, ⟨⟨List.replicate 12 0#u8, by simp only [List.length_replicate]; rfl⟩⟩⟩
  enc _ _ _ := ()
  dec _ _ _ := some ()
  dec_enc _ _ _ := rfl

/-- The kernel that a Server build installs for root `root`. The Server's initial kernel for `root` has chain_0, the first half of the root's initializer (`Pqxdh.rootChains`), as its send chain. The installed kernel has the next chain of the ratchet step of chain_0 as its send chain, the initial receive chain and receive counters, send counter one, and empty receive slots. It therefore stores neither chain_0 nor the sequence-one message material, the material half of that step. -/
def Installed (source : FixedHkdfSha512NoSaltSource) (root : RootOutput)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) : Prop :=
  ∃ initial stepped,
    PqxdhRootTableInitialization.initialKernelRun source false root = ok initial ∧
    PqxdhInitialRatchetComplementarity.ChainBytesRefines initial.refined.send_chain
      (Pqxdh.rootChains source.crypto root.toList).1 ∧
    ratchet.concrete.ratchet_step_from_response
      (RawCtxSourceHkdf.response source.crypto ⟨initial.refined.send_chain.bytes, ratchet.SYM_RATCHET_INFO⟩) =
        ok stepped ∧
    kernel.refined.send_chain = stepped.chain ∧
    kernel.refined.receive_chain = initial.refined.receive_chain ∧
    kernel.refined.control.send_sequence.val = 1 ∧
    kernel.refined.control.receive_sequence = initial.refined.control.receive_sequence ∧
    kernel.refined.control.receive_cache = initial.refined.control.receive_cache ∧
    ∀ slot, slot < 50 → kernel.refined.receive_slots.val[slot]! = .None

/-- A kernel refining a fresh abstract ratchet with no skipped keys has empty receive slots. -/
theorem fresh_slots_empty {AD PT CT : Type} (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (refines : ratchet.concrete.KernelRefines cr kernel.refined.receive_chain ⟨kernel.refined.send_chain, 0⟩
      ⟨kernel.refined.receive_chain, 0, []⟩ kernel) :
    ∀ slot, slot < 50 → kernel.refined.receive_slots.val[slot]! = .None := by
  intro slot below
  by_cases inside : slot < kernel.refined.control.receive_cache.len.val
  · obtain ⟨_, _, member, _⟩ := refines.slotSound slot inside
    simp at member
  · exact refines.slotsAboveLenEmpty slot (Nat.le_of_not_lt inside) below

/-- Under any tail interpreter whose ratchet KDF answers with the real response, the first send of the Server's initial kernel for `root` returns an installed kernel for `root`. -/
theorem first_send_installed {σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PqxdhServerRegistrationPublication.TailSpec (StateT σ (OracleComp base)))
    (source : FixedHkdfSha512NoSaltSource)
    (kdf : ∀ request state result, result ∈ support ((impl (.inl (.inl request))).run state) →
      result.1 = RawCtxSourceHkdf.response source.crypto request)
    (root : RootOutput) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (initialized : PqxdhRootTableInitialization.initialKernelRun source false root = ok kernel)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (primitive : σ)
    (sent : (ratchet.concrete.ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × σ)
    (supported : sent ∈ support ((simulateQ impl (simulateQ PqxdhServerRegistrationPublication.sendLift
      (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel
        (PqxdhServerRegistrationPublication.firstContext candidate authenticated))))).run primitive)) :
    Installed source root sent.1.1 := by
  obtain ⟨initial, hrun, hsend, _, refines⟩ :=
    PqxdhRootTableInitialization.initialize_refines source unitRatchet false root
  have same : initial = kernel := RustM.ok.inj (hrun.symm.trans initialized)
  subst same
  have hzero := refines.sendSequence
  have hmax : initial.refined.control.send_sequence ≠ core.num.U64.MAX := by
    intro h
    have hv := congrArg UScalar.val h
    simp only [hzero] at hv
    contradiction
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at supported
  obtain ⟨pending, response, afterKdf, hentry, _, hinput, hinfo, hkdf, _, hadvanced, hseq, hrs, hrc, hrchain,
    hslots⟩ := RawCtxSourceSend.send_nonexhausted_support _ initial _ primitive hmax sent supported
  have hrequest : pending.request = ⟨initial.refined.send_chain.bytes, ratchet.SYM_RATCHET_INFO⟩ := by
    rw [← hinput, ← hinfo]
  simp only [QueryImpl.apply_compose, RawCtxSourceSend.adapter, PqxdhServerRegistrationPublication.sendLift,
    simulateQ_spec_query] at hkdf
  have hresponse : response = RawCtxSourceHkdf.response source.crypto pending.request := kdf _ _ _ hkdf
  obtain ⟨stepped, hstep, hresume⟩ := RawCtxSourceSend.resumeSend_fields pending response
  rw [hresponse, hrequest] at hstep
  refine ⟨initial, stepped, hrun, by simpa using hsend, hstep, ?_, hrchain, ?_, hrs, hrc, ?_⟩
  · rw [hadvanced, hresume]
  · rw [hseq, hzero]
  · rw [hslots]
    exact fresh_slots_empty unitRatchet initial refines

/-- Every result of a build tail, under any interpreter whose ratchet KDF is the real response, either answers nothing and keeps the Server state, or answers and publishes, at the candidate's key ID, an installed kernel for the build's root; the second case needs a non-empty payload. -/
theorem build_support {σ ι : Type} {base : OracleSpec ι} {Metadata PeerMetadata Consumed : Type}
    (impl : QueryImpl PqxdhServerRegistrationPublication.TailSpec (StateT σ (OracleComp base)))
    (source : FixedHkdfSha512NoSaltSource)
    (kdf : ∀ request state result, result ∈ support ((impl (.inl (.inl request))).run state) →
      result.1 = RawCtxSourceHkdf.response source.crypto request)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput)
    (payload : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (server : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (primitive : σ)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) × σ)
    (supported : result ∈ support ((simulateQ impl
      (PqxdhServerRegistrationPublication.build source pending root payload metadata server)).run primitive)) :
    result.1 = ok (none, server) ∨
      ∃ candidate kernel response, result.1 = ok (some response,
          PqxdhServerRegistrationPublication.publish server candidate kernel metadata) ∧
        Installed source root kernel ∧
        payload.getD PqxdhServerRegistrationPublication.registrationWitness ≠ [] := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok server.control
  simp only [PqxdhServerRegistrationPublication.build, hnext, PqxdhServerRegistrationPublication.continueRust] at supported
  cases next with
  | Err error =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact Or.inl (congrArg Prod.fst supported)
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        server.control pending ⟨server.server.identity, server.identityKeyId⟩
        (if (server.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
      simp only [hprepared] at supported
      cases prepared with
      | Err error =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          exact Or.inl (congrArg Prod.fst supported)
      | Ok candidate =>
          obtain ⟨kernel, hrun, _, _, _⟩ :=
            PqxdhRootTableInitialization.initialize_refines source unitRatchet false root
          have hinit : BeaconcryptCore.Refinement.ServerTransactionRefinement.initializeCandidate candidate
              (rootArray root)
              (PqxdhRootTableInitialization.initialResponse source.crypto) = ok kernel :=
            (PqxdhServerRegistrationPublication.candidate_initialization source candidate root).trans hrun
          obtain ⟨binding, hbinding, _⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
          simp only [PqxdhServerRegistrationPublication.candidateTail, hinit, hbinding,
            PqxdhServerRegistrationPublication.continueRust, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨valid, afterIdentity⟩, _, supported⟩ := supported
          cases valid
          · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            exact Or.inl (congrArg Prod.fst supported)
          simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨reserved, afterReserve⟩, _, supported⟩ := supported
          cases reserved
          · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            exact Or.inl (congrArg Prod.fst supported)
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at supported
          by_cases empty : (payload.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
          · simp only [empty, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            exact Or.inl (congrArg Prod.fst supported)
          simp only [empty, Bool.false_eq_true, ite_false] at supported
          split_ifs at supported with fits
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
            obtain ⟨⟨allocated, afterAllocate⟩, _, supported⟩ := supported
            cases allocated
            · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at supported
              exact Or.inl (congrArg Prod.fst supported)
            simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
              support_map, Set.mem_image] at supported
            obtain ⟨inner, innerSupported, rfl⟩ := supported
            obtain ⟨sent, afterSend, afterErase, hsent, _, rest⟩ :=
              PqxdhServerRegistrationPublication.afterInitialization_support impl candidate _ kernel metadata server
                afterAllocate inner innerSupported
            have installed := first_send_installed impl source kdf root kernel hrun candidate _ afterAllocate
              (sent, afterSend) hsent
            cases hs : sent.2 with
            | none =>
                rw [hs] at rest
                rw [rest]
                exact Or.inl rfl
            | some encrypted =>
                rw [hs] at rest
                obtain ⟨written, afterWrite, _, eq⟩ := rest
                rw [eq]
                cases written with
                | none => exact Or.inl rfl
                | some bytes =>
                    refine Or.inr ⟨candidate, sent.1, ⟨bytes, candidate.key_id⟩, rfl, installed, ?_⟩
                    intro nil
                    rw [nil] at empty
                    exact empty rfl
          · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
            exact Or.inl (congrArg Prod.fst supported)

/-- The logging response tail answers every ratchet KDF request with the real response. -/
theorem tailImpl_kdf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (request : ratchet.SymmetricRatchetKdfRequest)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : ratchet.RatchetKdfResponse × RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((tailImpl setup codec checks (.inl (.inl request))).run state)) :
    result.1 = RawCtxSourceHkdf.response setup.source.crypto request := by
  change result ∈ support ((nativeTail setup codec checks (.inl (.inl request))).run state) at supported
  simp only [nativeTail, QueryImpl.apply_compose, PqxdhServerRegistrationPublication.nativeAdapter,
    RawCtxSourceSeal.nativeAdapter, simulateQ_spec_query, PqxdhRegistrationProtocolState.registrationImpl,
    RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter] at supported
  change result ∈ support ((RawCtxSourceHkdf.kdfImpl setup.source request).run state) at supported
  rw [RawCtxSourceHkdf.kdf_step, support_pure, Set.mem_singleton_iff] at supported
  rw [supported]

end BuildResults

/-! ## The game invariant -/

section Invariant

/-- The Beacon is in the InitSent phase, the only phase in which its finish runs. -/
def InitSent (state : GameState KemSK) : Prop :=
  ∃ control prekey oneTime kem, state.beacon.beacon.phase = .initSent control prekey oneTime kem

/-- Origin of a session touch: the message of the Server's root request for a Phase 1 input that carries its actual reached static-DH reference and passed the local nonzero test. -/
def SessionOrigin (Reader : Type) (setup : Setup baseSpec KemSK) (message : PqxdhJointDhExtractFamily.Message) : Prop :=
  ∃ input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding,
    message = PqxdhServerRelatedRootInput.message input ∧
      PqxdhServerStaticDhSource.References setup.serverDomain input ∧ PqxdhServerRelatedRootInput.localNonzero input

/-- Origin of a Beacon touch: the message of the Beacon's root request for a preparation that carries its actual selected references and the actual public conversion of the Server identity, and passed the admission test under a control pinned to the Server's binding. -/
def BeaconOrigin (Response : Type) (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (message : PqxdhJointDhExtractFamily.Message) : Prop :=
  ∃ (collected : PqxdhPhase2GapDhSource.Inputs Response) (metadata : PqxdhBeaconPhase2Shared.Metadata)
    (control : pqxdh.BeaconInitSent),
    message = PqxdhJointDhExtractRoot.beaconMessage publicValue collected ∧
      PqxdhPhase2GapDhSource.References setup.beaconDomain collected ∧
      setup.source.crypto.xpkConv (absBytes collected.server) = some (absBytes collected.serverConverted) ∧
      control.expected_server_binding = binding setup publicValue ∧
      PqxdhPhase2DhMetadata.admitted control collected = some metadata

/-- Invariant of every reached game state. The snapshot is a prefix of the logs; its touch log ends with the Beacon's single touch, with no Beacon touch before it (the finish is atomic); and each of its seals has a session touch that carries a root. Every session touch belongs to an allocated session, all touches of a session agree, and every session touch and every Beacon touch has its origin. Every seal belongs to an allocated session with a touch that carries a root, and no session has two seals. Every pending token belongs to an allocated, unsealed session, carries the reply of that session's root request as its root, and the reconstructed pending registration of that session's input. Every installed Server kernel is an installed kernel for some root. In the InitSent phase the Beacon's control is pinned to the Server's binding and no Beacon touch has been logged. -/
structure GameInv (Reader Response : Type) (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (state : GameState KemSK) : Prop where
  frozen : ∀ snap, state.ghost.acceptance = some snap →
    snap.touches <+: state.ghost.touches ∧ snap.seals <+: state.ghost.seals
  atomic : ∀ snap, state.ghost.acceptance = some snap →
    ∃ before message, snap.touches = before ++ [Touch.beacon message] ∧ ∀ other, Touch.beacon other ∉ before
  frozenSealed : ∀ snap, state.ghost.acceptance = some snap →
    ∀ entry ∈ snap.seals, ∃ message root, Touch.session entry.1 message (some root) ∈ snap.touches
  touched : ∀ index message reply, Touch.session index message reply ∈ state.ghost.touches → index < state.sessions
  sessionOnce : ∀ index message reply message' reply', Touch.session index message reply ∈ state.ghost.touches →
    Touch.session index message' reply' ∈ state.ghost.touches → message = message' ∧ reply = reply'
  sessionOrigin : ∀ index message reply, Touch.session index message reply ∈ state.ghost.touches →
    SessionOrigin Reader setup message
  beaconOrigin : ∀ message, Touch.beacon message ∈ state.ghost.touches → BeaconOrigin Response setup publicValue message
  sealedBelow : ∀ entry ∈ state.ghost.seals, entry.1 < state.sessions
  sealTouched : ∀ entry ∈ state.ghost.seals,
    ∃ message root, Touch.session entry.1 message (some root) ∈ state.ghost.touches
  sealOnce : (state.ghost.seals.map Prod.fst).Nodup
  pendingBelow : ∀ index token, state.pending index = some token → index < state.sessions
  pendingFresh : ∀ index token, state.pending index = some token → index ∉ state.ghost.seals.map Prod.fst
  pendingRoot : ∀ index token, state.pending index = some token →
    ∃ input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding,
      Touch.session index (PqxdhServerRelatedRootInput.message input) (some token.root) ∈ state.ghost.touches ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
      PqxdhServerStaticDhSource.References setup.serverDomain input ∧ PqxdhServerRelatedRootInput.localNonzero input
  peers : ∀ keyId peer, state.server.server.peers keyId = some peer → ∃ root, Installed setup.source root peer.kernel
  pinned : ∀ control prekey oneTime kem, state.beacon.beacon.phase = .initSent control prekey oneTime kem →
    control.expected_server_binding = binding setup publicValue
  clean : InitSent state → ∀ message, Touch.beacon message ∉ state.ghost.touches

/-- How a handler step may change the ghost: the logs only grow, a recorded acceptance stays, and the session counter does not decrease. -/
structure Grows (before after : GameState KemSK) : Prop where
  touches : before.ghost.touches <+: after.ghost.touches
  seals : before.ghost.seals <+: after.ghost.seals
  acceptance : ∀ snap, before.ghost.acceptance = some snap → after.ghost.acceptance = some snap
  sessions : before.sessions ≤ after.sessions

/-- `Grows` is reflexive. -/
theorem Grows.refl (state : GameState KemSK) : Grows state state :=
  ⟨List.prefix_refl _, List.prefix_refl _, fun _ found => found, le_refl _⟩

/-- `Grows` is transitive. -/
theorem Grows.trans {first second third : GameState KemSK} (left : Grows first second)
    (right : Grows second third) : Grows first third :=
  ⟨left.touches.trans right.touches, left.seals.trans right.seals,
    fun snap found => right.acceptance snap (left.acceptance snap found), left.sessions.trans right.sessions⟩

/-- The initial state after any Phase 1 run satisfies the invariant. -/
theorem inv_initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (supported : published ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk)) :
    GameInv Reader Response setup publicValue (initialGameState setup publicValue published.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    phase1_pinned setup codec beaconSeed publicValue oneTime kemPk kemSk published supported, ?_⟩ <;>
    simp [initialGameState, Ghost.empty]

/-- Recording an acceptance leaves the touch log unchanged. -/
theorem Ghost.accept_touches (ghost : Ghost) (accepted : Option Accepted) :
    (ghost.accept accepted).touches = ghost.touches := by
  cases accepted with
  | none => rfl
  | some accepted => cases h : ghost.acceptance <;> simp [Ghost.accept, h]

/-- Recording an acceptance leaves the seal log unchanged. -/
theorem Ghost.accept_seals (ghost : Ghost) (accepted : Option Accepted) :
    (ghost.accept accepted).seals = ghost.seals := by
  cases accepted with
  | none => rfl
  | some accepted => cases h : ghost.acceptance <;> simp [Ghost.accept, h]

/-- A recorded acceptance is never overwritten. -/
theorem Ghost.accept_keeps (ghost : Ghost) (accepted : Option Accepted) (snap : Snapshot)
    (found : ghost.acceptance = some snap) : (ghost.accept accepted).acceptance = some snap := by
  cases accepted with
  | none => exact found
  | some accepted => simp [Ghost.accept, found]

/-- After recording an acceptance, the snapshot is the old one or freezes the current logs. -/
theorem Ghost.accept_frozen (ghost : Ghost) (accepted : Option Accepted) (snap : Snapshot)
    (found : (ghost.accept accepted).acceptance = some snap) :
    ghost.acceptance = some snap ∨ (snap.touches = ghost.touches ∧ snap.seals = ghost.seals) := by
  cases accepted with
  | none => exact Or.inl found
  | some accepted =>
      cases h : ghost.acceptance with
      | none =>
          simp only [Ghost.accept, h, Option.some.injEq] at found
          subst found
          exact Or.inr ⟨rfl, rfl⟩
      | some old =>
          simp only [Ghost.accept, h] at found
          exact Or.inl found

/-- An acceptance recorded before is the one after any further recording. -/
theorem Ghost.accept_old (ghost : Ghost) (accepted : Option Accepted) (old snap : Snapshot)
    (before : ghost.acceptance = some old) (found : (ghost.accept accepted).acceptance = some snap) : snap = old := by
  rw [Ghost.accept_keeps ghost accepted old before] at found
  exact (Option.some.inj found).symm

/-- A newly recorded acceptance freezes the current logs with the accepted fields. -/
theorem Ghost.accept_new (ghost : Ghost) (accepted : Option Accepted) (snap : Snapshot)
    (found : (ghost.accept accepted).acceptance = some snap) (empty : ghost.acceptance = none) :
    ∃ fields, accepted = some fields ∧ snap = ⟨fields, ghost.touches, ghost.seals⟩ := by
  cases accepted with
  | none => simp [Ghost.accept, empty] at found
  | some fields =>
      simp only [Ghost.accept, empty, Option.some.injEq] at found
      exact ⟨fields, rfl, found.symm⟩

/-- The final checks leave the Beacon aborted or established, never in the InitSent phase. -/
theorem finish_phase {I D K : Type} (control : pqxdh.BeaconInitSent) (beacon : RawCtxBeaconLifecycle.State I D K)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    ∀ control' prekey oneTime kem,
      (PqxdhBeaconPhase2Publication.finish control beacon staged).2.beacon.phase ≠ .initSent control' prekey oneTime kem := by
  intro control' prekey oneTime kem
  cases staged with
  | none => simp [PqxdhBeaconPhase2Publication.finish, PqxdhBeaconPhase2Preparation.abort]
  | some staged =>
      simp only [PqxdhBeaconPhase2Publication.finish]
      split_ifs <;> simp [PqxdhBeaconPhase2Preparation.abort, PqxdhBeaconPhase2Publication.publish]

/-- No acceptance without a staged registration. -/
theorem acceptedOf_none (output : Option Pqxdh.Bytes) : acceptedOf none output = none := by
  simp [acceptedOf]

end Invariant

/-! ## Oracle steps -/

section OracleSteps
variable {setup : Setup baseSpec KemSK} {publicValue : PublicChallenge}

/-- Allocating a session and logging at most one touch of it, with its origin, keeps the invariant. -/
theorem inv_accept_touch (state : GameState KemSK) (consumed : List Pqxdh.Bytes) (extra : List Touch)
    (invariant : GameInv Reader Response setup publicValue state)
    (shape : extra = [] ∨ ∃ (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
      (reply : Option RootOutput),
      extra = [Touch.session state.sessions (PqxdhServerRelatedRootInput.message input) reply] ∧
        PqxdhServerStaticDhSource.References setup.serverDomain input ∧ PqxdhServerRelatedRootInput.localNonzero input) :
    GameInv Reader Response setup publicValue ({ state with sessions := state.sessions + 1, server := { state.server with consumed := consumed }, ghost := { state.ghost with touches := state.ghost.touches ++ extra } }) := by
  have newSession : ∀ touch ∈ extra, ∀ index message reply, touch = Touch.session index message reply →
      index = state.sessions ∧ SessionOrigin Reader setup message := by
    intro touch member index message reply eq
    rcases shape with rfl | ⟨input, other, rfl, references, valid⟩
    · simp at member
    · simp only [List.mem_singleton] at member
      subst member
      simp only [Touch.session.injEq] at eq
      obtain ⟨rfl, rfl, rfl⟩ := eq
      exact ⟨rfl, input, rfl, references, valid⟩
  have noBeacon : ∀ message, Touch.beacon message ∉ extra := by
    intro message member
    rcases shape with rfl | ⟨input, other, rfl, _⟩
    · simp at member
    · simp at member
  have single : ∀ index message reply message' reply', Touch.session index message reply ∈ extra →
      Touch.session index message' reply' ∈ extra → message = message' ∧ reply = reply' := by
    intro index message reply message' reply' first second
    rcases shape with rfl | ⟨input, other, rfl, _⟩
    · simp at first
    · simp only [List.mem_singleton, Touch.session.injEq] at first second
      exact ⟨first.2.1.trans second.2.1.symm, first.2.2.trans second.2.2.symm⟩
  refine ⟨?_, invariant.atomic, invariant.frozenSealed, ?_, ?_, ?_, ?_, ?_, ?_, invariant.sealOnce, ?_,
    invariant.pendingFresh, ?_, invariant.peers, invariant.pinned, ?_⟩
  · intro snap found
    obtain ⟨touchesPrefix, sealsPrefix⟩ := invariant.frozen snap found
    exact ⟨touchesPrefix.trans (List.prefix_append _ _), sealsPrefix⟩
  · intro index message reply member
    rcases List.mem_append.mp member with old | new
    · exact Nat.lt_succ_of_lt (invariant.touched index message reply old)
    · rw [(newSession _ new index message reply rfl).1]
      exact Nat.lt_succ_self _
  · intro index message reply message' reply' first second
    rcases List.mem_append.mp first with old | new <;> rcases List.mem_append.mp second with old' | new'
    · exact invariant.sessionOnce index message reply message' reply' old old'
    · have below := invariant.touched index message reply old
      have same := (newSession _ new' index message' reply' rfl).1
      omega
    · have below := invariant.touched index message' reply' old'
      have same := (newSession _ new index message reply rfl).1
      omega
    · exact single index message reply message' reply' new new'
  · intro index message reply member
    rcases List.mem_append.mp member with old | new
    · exact invariant.sessionOrigin index message reply old
    · exact (newSession _ new index message reply rfl).2
  · intro message member
    rcases List.mem_append.mp member with old | new
    · exact invariant.beaconOrigin message old
    · exact absurd new (noBeacon message)
  · intro entry member
    exact Nat.lt_succ_of_lt (invariant.sealedBelow entry member)
  · intro entry member
    obtain ⟨message, reply, found⟩ := invariant.sealTouched entry member
    exact ⟨message, reply, List.mem_append_left _ found⟩
  · intro index token found
    exact Nat.lt_succ_of_lt (invariant.pendingBelow index token found)
  · intro index token found
    obtain ⟨input, touched, rest⟩ := invariant.pendingRoot index token found
    exact ⟨input, List.mem_append_left _ touched, rest⟩
  · intro initSent message member
    rcases List.mem_append.mp member with old | new
    · exact invariant.clean initSent message old
    · exact noBeacon message new

/-- Storing a pending token for an allocated, unsealed session whose touch carries the token's root keeps the invariant. -/
theorem inv_add_pending (state : GameState KemSK) (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (invariant : GameInv Reader Response setup publicValue state) (below : index < state.sessions)
    (fresh : index ∉ state.ghost.seals.map Prod.fst)
    (origin : ∃ input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding,
      Touch.session index (PqxdhServerRelatedRootInput.message input) (some token.root) ∈ state.ghost.touches ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
      PqxdhServerStaticDhSource.References setup.serverDomain input ∧ PqxdhServerRelatedRootInput.localNonzero input) :
    GameInv Reader Response setup publicValue ({ state with pending := Function.update state.pending index (some token) }) := by
  refine ⟨invariant.frozen, invariant.atomic, invariant.frozenSealed, invariant.touched, invariant.sessionOnce,
    invariant.sessionOrigin, invariant.beaconOrigin, invariant.sealedBelow, invariant.sealTouched, invariant.sealOnce,
    ?_, ?_, ?_, invariant.peers, invariant.pinned, invariant.clean⟩
  · intro other value found
    dsimp only at found ⊢
    by_cases same : other = index
    · rw [same]
      exact below
    · rw [Function.update_of_ne same] at found
      exact invariant.pendingBelow other value found
  · intro other value found
    dsimp only at found ⊢
    by_cases same : other = index
    · rw [same]
      exact fresh
    · rw [Function.update_of_ne same] at found
      exact invariant.pendingFresh other value found
  · intro other value found
    dsimp only at found ⊢
    by_cases same : other = index
    · subst same
      simp only [Function.update_self, Option.some.injEq] at found
      subst found
      exact origin
    · rw [Function.update_of_ne same] at found
      exact invariant.pendingRoot other value found

/-- A Server accept keeps the invariant, only extends the logs, allocates exactly one session index and leaves the Beacon unchanged. -/
theorem accept_step (codec : Codec Reader Response) (checks : Checks) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    (GameInv Reader Response setup publicValue state → GameInv Reader Response setup publicValue result.2) ∧
      Grows state result.2 ∧ result.2.sessions = state.sessions + 1 ∧ result.2.beacon = state.beacon := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨prefixMember, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨fun invariant => ?_, ⟨List.prefix_refl _, List.prefix_refl _, fun _ found => found, Nat.le_succ _⟩,
        rfl, rfl⟩
      simpa using inv_accept_touch state collected.1.2 [] invariant (Or.inl rfl)
  | some input =>
      have references : PqxdhServerStaticDhSource.References setup.serverDomain input := by
        have member : (some input, collected.1.2) ∈ support ((serverPrefix setup codec checks raw).run
            state.server.consumed) := by
          rw [← hc]
          exact prefixMember
        exact PqxdhServerStaticDhSource.collect_references setup.serverDomain (serverAux setup codec checks)
          (fun _ => pure ()) raw _ _ input member
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, shape, tokens⟩ := client_run state.sessions (binding setup publicValue) input _
        returned derived
      have afterInv : GameInv Reader Response setup publicValue state →
          GameInv Reader Response setup publicValue returned.2 := fun invariant => by
        rw [eq]
        simpa using inv_accept_touch state consumed extra invariant (by
          rcases shape with ⟨_, empty⟩ | ⟨valid, reply, rfl⟩
          · exact Or.inl empty
          · exact Or.inr ⟨input, reply, rfl, references, valid⟩)
      have afterGrows : Grows state returned.2 := by
        rw [eq]
        exact ⟨List.prefix_append _ _, List.prefix_refl _, fun _ found => found, Nat.le_succ _⟩
      have sessionsEq : returned.2.sessions = state.sessions + 1 := by rw [eq]
      have beaconEq : returned.2.beacon = state.beacon := by rw [eq]
      rcases returned with ⟨outcome, after⟩
      dsimp only at afterInv afterGrows sessionsEq beaconEq tokens eq
      rcases outcome with (_ | token) | error | _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨afterInv, afterGrows, sessionsEq, beaconEq⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        refine ⟨fun invariant => ?_, ⟨afterGrows.touches, afterGrows.seals, afterGrows.acceptance,
          afterGrows.sessions⟩, sessionsEq, beaconEq⟩
        obtain ⟨valid, extraEq, pendingEq⟩ := tokens token rfl
        have inner := afterInv invariant
        have seals : after.ghost.seals = state.ghost.seals := by rw [eq]
        refine inv_add_pending after state.sessions token inner (by rw [sessionsEq]; exact Nat.lt_succ_self _) ?_ ?_
        · intro member
          rw [seals] at member
          obtain ⟨entry, entryMember, entryEq⟩ := List.mem_map.mp member
          have below := invariant.sealedBelow entry entryMember
          omega
        · refine ⟨input, ?_, pendingEq, references, valid⟩
          rw [eq, extraEq]
          exact List.mem_append_right _ (List.mem_singleton_self _)
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨afterInv, afterGrows, sessionsEq, beaconEq⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨afterInv, afterGrows, sessionsEq, beaconEq⟩

/-- A Server build keeps the invariant, adds at most one seal and only under its session, and leaves the session counter and the Beacon unchanged. -/
theorem build_step (codec : Codec Reader Response) (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    (GameInv Reader Response setup publicValue state → GameInv Reader Response setup publicValue result.2) ∧
      Grows state result.2 ∧ result.2.sessions = state.sessions ∧ result.2.beacon = state.beacon ∧
      ∃ log : List RawCtxSourceSend.SealContext, log.length ≤ 1 ∧
        result.2.ghost.seals = state.ghost.seals ++ log.map (fun context => (session, context)) := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨id, Grows.refl _, rfl, rfl, [], by simp, by simp⟩
  | some token =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      obtain ⟨tailMember, same⟩ := liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      have logLength := build_log_length setup codec checks token.pending token.root payload state.server state.ctx
        tail.1 tailMember
      have cases := build_support (tailImpl setup codec checks) setup.source (tailImpl_kdf setup codec checks)
        token.pending token.root payload () state.server ([], state.ctx) tail.1 tailMember
      refine ⟨fun invariant => ?_, ⟨List.prefix_refl _, List.prefix_append _ _, fun _ found => found, le_refl _⟩,
        rfl, rfl, tail.1.2.1, logLength, rfl⟩
      have below := invariant.pendingBelow session token hp
      have fresh := invariant.pendingFresh session token hp
      obtain ⟨input, touchedRoot, _⟩ := invariant.pendingRoot session token hp
      dsimp only
      refine ⟨?_, invariant.atomic, invariant.frozenSealed, invariant.touched, invariant.sessionOnce,
        invariant.sessionOrigin, invariant.beaconOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, invariant.pinned,
        invariant.clean⟩
      · intro snap found
        obtain ⟨touchesPrefix, sealsPrefix⟩ := invariant.frozen snap found
        exact ⟨touchesPrefix, sealsPrefix.trans (List.prefix_append _ _)⟩
      · intro entry member
        rcases List.mem_append.mp member with old | new
        · exact invariant.sealedBelow entry old
        · obtain ⟨context, _, rfl⟩ := List.mem_map.mp new
          exact below
      · intro entry member
        rcases List.mem_append.mp member with old | new
        · exact invariant.sealTouched entry old
        · obtain ⟨context, _, rfl⟩ := List.mem_map.mp new
          exact ⟨_, _, touchedRoot⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨invariant.sealOnce, ?_, ?_⟩
        · simp only [List.map_map, Function.comp_def]
          have short := logLength
          generalize tail.1.2.1 = log at short ⊢
          rcases log with _ | ⟨first, _ | ⟨second, rest⟩⟩
          · exact List.nodup_nil
          · exact List.nodup_singleton _
          · simp at short
        · intro left leftMember right rightMember
          simp only [List.map_map, Function.comp_def, List.mem_map] at rightMember
          obtain ⟨_, _, rfl⟩ := rightMember
          intro eq
          subst eq
          exact fresh leftMember
      · intro index other found
        dsimp only at found
        by_cases same : index = session
        · subst same
          simp at found
        · rw [Function.update_of_ne same] at found
          exact invariant.pendingBelow index other found
      · intro index other found
        dsimp only at found
        by_cases same : index = session
        · subst same
          simp at found
        · rw [Function.update_of_ne same] at found
          intro member
          rw [List.map_append, List.mem_append] at member
          rcases member with old | new
          · exact invariant.pendingFresh index other found old
          · simp only [List.map_map, Function.comp_def, List.mem_map] at new
            obtain ⟨_, _, eq⟩ := new
            exact same eq.symm
      · intro index other found
        dsimp only at found
        by_cases same : index = session
        · subst same
          simp at found
        · rw [Function.update_of_ne same] at found
          exact invariant.pendingRoot index other found
      · intro keyId peer found
        dsimp only at found
        rcases cases with unchanged | ⟨candidate, kernel, response, published, installed, _⟩
        · simp only [unchanged, settle] at found
          exact invariant.peers keyId peer found
        · simp only [published, settle] at found
          by_cases same : keyId = candidate.key_id
          · subst same
            rw [(PqxdhServerRegistrationPublication.publish_fields state.server candidate kernel ()).1] at found
            cases found
            exact ⟨token.root, installed⟩
          · rw [(PqxdhServerRegistrationPublication.publish_fields state.server candidate kernel ()).2.2.2.2 keyId same]
              at found
            exact invariant.peers keyId peer found

/-- The target Beacon's finish keeps the invariant, only extends the logs, writes the acceptance at most once, and leaves the Beacon outside the InitSent phase; outside that phase it changes nothing. -/
theorem finish_step (codec : Codec Reader Response) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Pqxdh.Bytes × GameState KemSK)
    (supported : result ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state)) :
    (GameInv Reader Response setup publicValue state → GameInv Reader Response setup publicValue result.2) ∧
      Grows state result.2 ∧ result.2.sessions = state.sessions ∧ ¬ InitSent result.2 ∧
      (¬ InitSent state → result.2 = state) := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      have initSent : InitSent state := ⟨control, prekey, oneTime, kem, hphase⟩
      simp only [hphase, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, stageRun, supported⟩ := supported
      obtain ⟨cache, extra, stagedEq, shape⟩ := stage_run setup codec beaconSeed publicValue control
        state.beacon.beacon.identity oneTime kem raw state staged stageRun
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, _, rfl, rfl⟩ := supported
      rcases staged with ⟨stagedValue, stagedState⟩
      dsimp only at stagedEq shape ⊢
      subst stagedEq
      dsimp only
      have noSession : ∀ touch ∈ extra, ∀ index message reply, touch ≠ Touch.session index message reply := by
        intro touch member index message reply eq
        subst eq
        rcases shape with ⟨rfl, _, _⟩ | ⟨pending, _, rfl⟩ <;> simp at member
      refine ⟨fun invariant => ?_, ⟨?_, ?_, fun snap found => Ghost.accept_keeps _ _ snap found, le_refl _⟩, rfl,
        ?_, fun inactive => absurd initSent inactive⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, invariant.pendingBelow, ?_, ?_, invariant.peers, ?_, ?_⟩
        · intro snap found
          rw [Ghost.accept_touches, Ghost.accept_seals]
          rcases Ghost.accept_frozen _ _ snap found with old | ⟨touchesEq, sealsEq⟩
          · obtain ⟨touchesPrefix, sealsPrefix⟩ := invariant.frozen snap old
            exact ⟨touchesPrefix.trans (List.prefix_append _ _), sealsPrefix⟩
          · rw [touchesEq, sealsEq]
            exact ⟨List.prefix_refl _, List.prefix_refl _⟩
        · intro snap found
          cases hold : state.ghost.acceptance with
          | some old =>
              have same := Ghost.accept_old { state.ghost with touches := state.ghost.touches ++ extra } _ old snap
                hold found
              subst same
              exact invariant.atomic _ hold
          | none =>
              obtain ⟨fields, acceptedEq, snapEq⟩ := Ghost.accept_new _ _ snap found hold
              subst snapEq
              rcases shape with ⟨_, rfl, _⟩ | ⟨pending, _, rfl⟩
              · rw [acceptedOf_none] at acceptedEq
                cases acceptedEq
              · exact ⟨state.ghost.touches, _, rfl, invariant.clean initSent⟩
        · intro snap found
          cases hold : state.ghost.acceptance with
          | some old =>
              have same := Ghost.accept_old { state.ghost with touches := state.ghost.touches ++ extra } _ old snap
                hold found
              subst same
              exact invariant.frozenSealed _ hold
          | none =>
              obtain ⟨fields, _, snapEq⟩ := Ghost.accept_new _ _ snap found hold
              subst snapEq
              intro entry member
              obtain ⟨message, reply, touched⟩ := invariant.sealTouched entry member
              exact ⟨message, reply, List.mem_append_left _ touched⟩
        · intro index message reply member
          rw [Ghost.accept_touches] at member
          rcases List.mem_append.mp member with old | new
          · exact invariant.touched index message reply old
          · exact absurd rfl (noSession _ new index message reply)
        · intro index message reply message' reply' first second
          rw [Ghost.accept_touches] at first second
          rcases List.mem_append.mp first with old | new
          · rcases List.mem_append.mp second with old' | new'
            · exact invariant.sessionOnce index message reply message' reply' old old'
            · exact absurd rfl (noSession _ new' index message' reply')
          · exact absurd rfl (noSession _ new index message reply)
        · intro index message reply member
          rw [Ghost.accept_touches] at member
          rcases List.mem_append.mp member with old | new
          · exact invariant.sessionOrigin index message reply old
          · exact absurd rfl (noSession _ new index message reply)
        · intro message member
          rw [Ghost.accept_touches] at member
          rcases List.mem_append.mp member with old | new
          · exact invariant.beaconOrigin message old
          · rcases shape with ⟨rfl, _, _⟩ | ⟨pending, reached, rfl⟩
            · simp at new
            · simp only [List.mem_singleton, Touch.beacon.injEq] at new
              subst new
              obtain ⟨references, conversion, admitted⟩ := beaconReached_facts setup codec beaconSeed control _ _ _ raw
                pending reached
              exact ⟨pending.collected, pending.metadata, control, rfl, references, conversion,
                invariant.pinned control prekey oneTime kem hphase, admitted⟩
        · rw [Ghost.accept_seals]
          exact invariant.sealedBelow
        · intro entry member
          rw [Ghost.accept_seals] at member
          rw [Ghost.accept_touches]
          obtain ⟨message, reply, touched⟩ := invariant.sealTouched entry member
          exact ⟨message, reply, List.mem_append_left _ touched⟩
        · rw [Ghost.accept_seals]
          exact invariant.sealOnce
        · rw [Ghost.accept_seals]
          exact invariant.pendingFresh
        · intro index token found
          rw [Ghost.accept_touches]
          obtain ⟨input, touched, rest⟩ := invariant.pendingRoot index token found
          exact ⟨input, List.mem_append_left _ touched, rest⟩
        · exact fun control' prekey' oneTime' kem' phase =>
            absurd phase (finish_phase control state.beacon stagedValue control' prekey' oneTime' kem')
        · rintro ⟨control', prekey', oneTime', kem', phase⟩
          exact absurd phase (finish_phase control state.beacon stagedValue control' prekey' oneTime' kem')
      · rw [Ghost.accept_touches]
        exact List.prefix_append _ _
      · rw [Ghost.accept_seals]
      · rintro ⟨control', prekey', oneTime', kem', phase⟩
        exact absurd phase (finish_phase control state.beacon stagedValue control' prekey' oneTime' kem')
  | fresh control prekey kem =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨id, Grows.refl _, rfl, ?_, fun _ => rfl⟩
      rintro ⟨_, _, _, _, phase⟩
      rw [hphase] at phase
      cases phase
  | freshWithCoins control prekey oneTime kem =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨id, Grows.refl _, rfl, ?_, fun _ => rfl⟩
      rintro ⟨_, _, _, _, phase⟩
      rw [hphase] at phase
      cases phase
  | established control associatedData kernel =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨id, Grows.refl _, rfl, ?_, fun _ => rfl⟩
      rintro ⟨_, _, _, _, phase⟩
      rw [hphase] at phase
      cases phase
  | aborted control =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨id, Grows.refl _, rfl, ?_, fun _ => rfl⟩
      rintro ⟨_, _, _, _, phase⟩
      rw [hphase] at phase
      cases phase

/-- Logging an adversary table query keeps the invariant and only extends the touch log. -/
theorem inv_adversary_touch (state : GameState KemSK) (bytes : Pqxdh.Bytes)
    (invariant : GameInv Reader Response setup publicValue state) :
    GameInv Reader Response setup publicValue ({ state with ghost := { state.ghost with touches := state.ghost.touches ++ [Touch.adversary bytes] } }) := by
  refine ⟨?_, invariant.atomic, invariant.frozenSealed, ?_, ?_, ?_, ?_, invariant.sealedBelow, ?_, invariant.sealOnce,
    invariant.pendingBelow, invariant.pendingFresh, ?_, invariant.peers, invariant.pinned, ?_⟩
  · intro snap found
    obtain ⟨touchesPrefix, sealsPrefix⟩ := invariant.frozen snap found
    exact ⟨touchesPrefix.trans (List.prefix_append _ _), sealsPrefix⟩
  · intro index message reply member
    rcases List.mem_append.mp member with old | new
    · exact invariant.touched index message reply old
    · simp at new
  · intro index message reply message' reply' first second
    rcases List.mem_append.mp first with old | new
    · rcases List.mem_append.mp second with old' | new'
      · exact invariant.sessionOnce index message reply message' reply' old old'
      · simp at new'
    · simp at new
  · intro index message reply member
    rcases List.mem_append.mp member with old | new
    · exact invariant.sessionOrigin index message reply old
    · simp at new
  · intro message member
    rcases List.mem_append.mp member with old | new
    · exact invariant.beaconOrigin message old
    · simp at new
  · intro entry member
    obtain ⟨message, reply, touched⟩ := invariant.sealTouched entry member
    exact ⟨message, reply, List.mem_append_left _ touched⟩
  · intro index token found
    obtain ⟨input, touched, rest⟩ := invariant.pendingRoot index token found
    exact ⟨input, List.mem_append_left _ touched, rest⟩
  · intro initSent message member
    rcases List.mem_append.mp member with old | new
    · exact invariant.clean initSent message old
    · simp at new

/-- A public HMAC query keeps the invariant, only extends the touch log, and leaves the session counter and the Beacon unchanged. -/
theorem hmac_step (key : HmacBlock) (message : Pqxdh.Bytes) (state : GameState KemSK)
    (result : HmacBlock × GameState KemSK) (supported : result ∈ support ((hmacOracle key message).run state)) :
    (GameInv Reader Response setup publicValue state → GameInv Reader Response setup publicValue result.2) ∧
      Grows state result.2 ∧ result.2.sessions = state.sessions ∧ result.2.beacon = state.beacon := by
  simp only [hmacOracle] at supported
  split_ifs at supported
  · obtain ⟨middle, first, rest⟩ := run_bind_support _ _ _ _ supported
    rw [record_run, support_pure, Set.mem_singleton_iff] at first
    subst first
    rw [forward_support _ _ _ rest]
    exact ⟨inv_adversary_touch state message, ⟨List.prefix_append _ _, List.prefix_refl _, fun _ found => found,
      le_refl _⟩, rfl, rfl⟩
  · rw [forward_support _ _ _ supported]
    exact ⟨id, Grows.refl _, rfl, rfl⟩

/-- A BLAKE2b query changes only the shared cache. -/
theorem hashOracle_step (bytes : Pqxdh.Bytes) (state : GameState KemSK) (result : CtxRomAuth.CtxDigest × GameState KemSK)
    (supported : result ∈ support ((hashOracle bytes).run state)) : ∃ cache, result.2 = { state with ctx := cache } := by
  simp only [hashOracle, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact ⟨_, rfl⟩

/-- Every handler step keeps the invariant, only extends the logs, raises the session counter by at most one and only at an accept, never enters the InitSent phase, and changes the Beacon only at a finish. -/
theorem authHandler_step (codec : Codec Reader Response) (checks : Checks) (beaconSeed : IdentitySeed)
    (query : ServerAuthSpec.Domain) (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    (GameInv Reader Response setup publicValue state → GameInv Reader Response setup publicValue result.2) ∧
      Grows state result.2 ∧ result.2.sessions ≤ state.sessions + (if IsAcceptQuery query then 1 else 0) ∧
      (¬ InitSent state → ¬ InitSent result.2) ∧
      ((∀ raw, query ≠ .inr (.finish raw)) → result.2.beacon = state.beacon) := by
  have inactive : ∀ after : GameState KemSK, after.beacon = state.beacon → ¬ InitSent state → ¬ InitSent after :=
    fun after same stateInactive afterInit => stateInactive (by
      obtain ⟨control, prekey, oneTime, kem, phase⟩ := afterInit
      exact ⟨control, prekey, oneTime, kem, by rw [← same]; exact phase⟩)
  rcases query with coin | query
  · have same := forward_support _ _ _ supported
    rw [same]
    exact ⟨id, Grows.refl _, Nat.le_add_right _ _, id, fun _ => rfl⟩
  cases query with
  | accept raw =>
      obtain ⟨invariant, grows, sessions, beacon⟩ := accept_step codec checks raw state result supported
      exact ⟨invariant, grows, by simp [IsAcceptQuery, sessions], inactive _ beacon, fun _ => beacon⟩
  | build session payload =>
      obtain ⟨invariant, grows, sessions, beacon, _⟩ := build_step codec checks session payload state result
        supported
      exact ⟨invariant, grows, by simp [IsAcceptQuery, sessions], inactive _ beacon, fun _ => beacon⟩
  | finish raw =>
      obtain ⟨invariant, grows, sessions, after, _⟩ := finish_step codec beaconSeed raw state result supported
      exact ⟨invariant, grows, by simp [IsAcceptQuery, sessions], fun _ => after,
        fun notFinish => absurd rfl (notFinish raw)⟩
  | hmac key message =>
      obtain ⟨invariant, grows, sessions, beacon⟩ := hmac_step key message state result supported
      exact ⟨invariant, grows, by simp [IsAcceptQuery, sessions], inactive _ beacon, fun _ => beacon⟩
  | hash bytes =>
      obtain ⟨cache, eq⟩ := hashOracle_step bytes state result supported
      rw [eq]
      refine ⟨fun invariant => ?_, ⟨List.prefix_refl _, List.prefix_refl _, fun _ found => found, le_refl _⟩,
        by simp [IsAcceptQuery], inactive _ rfl, fun _ => rfl⟩
      exact ⟨invariant.frozen, invariant.atomic, invariant.frozenSealed, invariant.touched, invariant.sessionOnce,
        invariant.sessionOrigin, invariant.beaconOrigin, invariant.sealedBelow, invariant.sealTouched,
        invariant.sealOnce, invariant.pendingBelow, invariant.pendingFresh, invariant.pendingRoot, invariant.peers,
        invariant.pinned, invariant.clean⟩
  | reveal keyId =>
      simp only [authHandler] at supported
      rw [supported]
      exact ⟨id, Grows.refl _, Nat.le_add_right _ _, id, fun _ => rfl⟩

end OracleSteps

/-! ## Reachable states -/

section Reachable

/-- Along any adversary run, the invariant is kept and the ghost only grows. -/
theorem run_inv (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) {α : Type} (oa : OracleComp ServerAuthSpec α)
    (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) oa).run state)) :
    (GameInv Reader Response setup publicValue state → GameInv Reader Response setup publicValue result.2) ∧
      Grows state result.2 :=
  run_rel (authHandler setup codec checks publicValue beaconSeed)
    (fun before after => (GameInv Reader Response setup publicValue before →
      GameInv Reader Response setup publicValue after) ∧ Grows before after)
    (fun state => ⟨id, Grows.refl state⟩)
    (fun _ _ _ left right => ⟨right.1 ∘ left.1, left.2.trans right.2⟩)
    (fun query state result supported =>
      ⟨(authHandler_step codec checks beaconSeed query state result supported).1,
        (authHandler_step codec checks beaconSeed query state result supported).2.1⟩)
    oa state result supported

/-- Along an adversary run with at most `Q` accepts, at most `Q` session indices are allocated. -/
theorem run_sessions (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) {α : Type} (oa : OracleComp ServerAuthSpec α)
    (Q : Nat) (bounded : oa.IsQueryBoundP IsAcceptQuery Q) (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) oa).run state)) :
    result.2.sessions ≤ state.sessions + Q :=
  run_count (authHandler setup codec checks publicValue beaconSeed) IsAcceptQuery (fun state => state.sessions)
    (fun query state result supported =>
      (authHandler_step (Reader := Reader) (Response := Response) codec checks beaconSeed query state result
        supported).2.2.1)
    oa Q bounded state result supported

/-- Along any adversary run from a state outside the InitSent phase, the Beacon stays outside it. -/
theorem run_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) {α : Type} (oa : OracleComp ServerAuthSpec α)
    (state : GameState KemSK) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) oa).run state))
    (inactive : ¬ InitSent state) : ¬ InitSent result.2 :=
  run_rel (authHandler setup codec checks publicValue beaconSeed)
    (fun before after => ¬ InitSent before → ¬ InitSent after)
    (fun _ => id) (fun _ _ _ left right => right ∘ left)
    (fun query state result supported =>
      (authHandler_step (Reader := Reader) (Response := Response) (publicValue := publicValue) codec checks
        beaconSeed query state result supported).2.2.2.1)
    oa state result supported inactive

/-- Every state that any adversary program reaches from the initial state of a Phase 1 run satisfies the invariant; this covers every state at which the handler answers a query. -/
theorem reachable_inv (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (phase1 : published ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk))
    {α : Type} (oa : OracleComp ServerAuthSpec α) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) oa).run
      (initialGameState setup publicValue published.2))) :
    GameInv Reader Response setup publicValue result.2 :=
  (run_inv setup codec checks publicValue beaconSeed oa _ result supported).1
    (inv_initial setup codec beaconSeed publicValue oneTime kemPk kemSk published phase1)

/-- Every final state of the body satisfies the invariant, and has at most `Q` sessions when the adversary makes at most `Q` accepts. -/
theorem body_reachable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealed : Option IdentitySeed) (publicValue : PublicChallenge)
    (final : GameState KemSK) (supported : final ∈ support (body setup codec checks adversary revealed publicValue)) :
    GameInv Reader Response setup publicValue final ∧ ∀ Q qH qHash, AuthBudget adversary Q qH qHash → final.sessions ≤ Q := by
  simp only [body, mem_support_bind_iff, support_map, Set.mem_image] at supported
  obtain ⟨beaconSeed, _, oneTime, _, keys, _, published, publishedMember, result, run, rfl⟩ := supported
  refine ⟨reachable_inv setup codec checks publicValue beaconSeed oneTime keys.1 keys.2 published
    (coins_support _ _ publishedMember) _ result run, ?_⟩
  intro Q qH qHash budget
  have bound := run_sessions setup codec checks publicValue beaconSeed _ Q (budget.accept _) _ result run
  simpa [initialGameState] using bound

/-- Every final state of the experiment satisfies the invariant for the public challenge of its two secrets, and has at most `Q` sessions under the budget. -/
theorem gameState_reachable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary)) :
    GameInv Reader Response setup (PqxdhJointGapDh.challenge setup.joint setup.dh result.1 result.2.1) result.2.2.1 ∧
      ∀ Q qH qHash, AuthBudget adversary Q qH qHash → result.2.2.1.sessions ≤ Q := by
  simp only [gameState, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, scalar, _, run, member, rfl⟩ := supported
  apply body_reachable setup codec checks adversary _ _ run.1
  apply OracleComp.support_simulateQ_run'_subset (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh
    seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ member

end Reachable

/-! ## Support lemmas -/

section Support

/-- The acceptance snapshot is a prefix of the final logs on every run of the experiment: nothing is removed from the logs after the Beacon accepts. -/
theorem snapshot_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary))
    (snap : Snapshot) (found : result.2.2.1.ghost.acceptance = some snap) :
    snap.touches <+: result.2.2.1.ghost.touches ∧ snap.seals <+: result.2.2.1.ghost.seals :=
  (gameState_reachable setup codec checks revealSeed adversary result supported).1.frozen snap found

/-- `Win` reads only the write-once acceptance snapshot: two ghosts with the same snapshot win together. -/
theorem win_frozen (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (left right : Ghost) (same : left.acceptance = right.acceptance) :
    Win setup seed scalar left ↔ Win setup seed scalar right := by
  simp only [Win, W1, W2, W3, same]

/-- The Beacon's first logged derivation is unchanged when touches are appended after it. -/
theorem firstBeacon_prefix (touches later : List Touch) (message : PqxdhJointDhExtractFamily.Message)
    (found : firstBeacon touches = some message) (grown : touches <+: later) : firstBeacon later = some message := by
  obtain ⟨rest, rfl⟩ := grown
  unfold firstBeacon at found ⊢
  rw [List.findSome?_append, found]
  rfl

/-- A log whose first part has no Beacon touch has its next Beacon touch as the first one. -/
theorem firstBeacon_after (before rest : List Touch) (message : PqxdhJointDhExtractFamily.Message)
    (clean : ∀ other, Touch.beacon other ∉ before) : firstBeacon (before ++ Touch.beacon message :: rest) = some message := by
  unfold firstBeacon
  rw [List.findSome?_append]
  have none : before.findSome? (fun
      | .beacon message => some message
      | _ => none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro touch member
    cases touch with
    | beacon other => exact absurd member (clean other)
    | session => rfl
    | adversary => rfl
  rw [none]
  rfl

/-- The Beacon's root input is unchanged when touches are appended after its first derivation. -/
theorem beaconInput_prefix (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (touches later : List Touch) (bytes : Pqxdh.Bytes)
    (found : beaconInput setup seed scalar touches = some bytes) (grown : touches <+: later) :
    beaconInput setup seed scalar later = some bytes := by
  unfold beaconInput at found ⊢
  cases first : firstBeacon touches with
  | none => simp [first] at found
  | some message => rw [firstBeacon_prefix touches later message first grown]; simpa [first] using found

/-- Two partners at the acceptance are a narrowed session collision, given that the snapshot's touches are a prefix of the final log. -/
theorem w3_collB (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (ghost : Ghost)
    (isPrefix : ∀ snap, ghost.acceptance = some snap → snap.touches <+: ghost.touches)
    (w3 : W3 setup seed scalar ghost) : CollB setup seed scalar ghost := by
  obtain ⟨snap, found, i, j, ne, ⟨mi, ri, bi, ti, hi, si⟩, ⟨mj, rj, bj, tj, hj, sj⟩⟩ := w3
  have grown := isPrefix snap found
  have same : bj = bi := Option.some.inj (sj.symm.trans si)
  subst same
  exact ⟨i, j, mi, mj, ri, rj, bj, ne, grown.subset ti, grown.subset tj,
    beaconInput_prefix setup seed scalar _ _ bj si grown, hi, hj⟩

/-- The finish is atomic: on every run, the snapshot's touch log ends with the Beacon's single touch and has no Beacon touch before it, and that touch is the Beacon's first touch in the snapshot and in the final log. -/
theorem snapshot_atomic (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary))
    (snap : Snapshot) (found : result.2.2.1.ghost.acceptance = some snap) :
    ∃ before message, snap.touches = before ++ [Touch.beacon message] ∧ (∀ other, Touch.beacon other ∉ before) ∧
      firstBeacon snap.touches = some message ∧ firstBeacon result.2.2.1.ghost.touches = some message := by
  have invariant := (gameState_reachable setup codec checks revealSeed adversary result supported).1
  obtain ⟨before, message, eq, clean⟩ := invariant.atomic snap found
  have first : firstBeacon snap.touches = some message := by
    rw [eq]
    exact firstBeacon_after before [] message clean
  exact ⟨before, message, eq, clean, first, firstBeacon_prefix _ _ message first (invariant.frozen snap found).1⟩

/-- On every run, every seal belongs to a session with a touch that carries a derived root, in the final logs and in the acceptance snapshot. That the seal was made under that root is a property of the run, left to the key-level stage. -/
theorem seal_touched (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary)) :
    (∀ entry ∈ result.2.2.1.ghost.seals, ∃ message root,
        Touch.session entry.1 message (some root) ∈ result.2.2.1.ghost.touches) ∧
      ∀ snap, result.2.2.1.ghost.acceptance = some snap →
        ∀ entry ∈ snap.seals, ∃ message root, Touch.session entry.1 message (some root) ∈ snap.touches :=
  ⟨(gameState_reachable setup codec checks revealSeed adversary result supported).1.sealTouched,
    (gameState_reachable setup codec checks revealSeed adversary result supported).1.frozenSealed⟩

/-- Every pending token, at every state that an adversary program reaches from the initial state, carries the reply of its session's root request as its root and the reconstructed pending registration of that session's input. -/
theorem pending_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (phase1 : published ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk))
    {α : Type} (oa : OracleComp ServerAuthSpec α) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) oa).run
      (initialGameState setup publicValue published.2)))
    (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned) (found : result.2.pending index = some token) :
    ∃ input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding,
      Touch.session index (PqxdhServerRelatedRootInput.message input) (some token.root) ∈ result.2.ghost.touches ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
      PqxdhServerStaticDhSource.References setup.serverDomain input ∧ PqxdhServerRelatedRootInput.localNonzero input :=
  (reachable_inv setup codec checks publicValue beaconSeed oneTime kemPk kemSk published phase1 oa result
    supported).pendingRoot index token found

/-- No session ever has two seals on a run of the experiment: a build consumes its pending token and seals at most once. -/
theorem seal_once_per_session (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary)) :
    (result.2.2.1.ghost.seals.map Prod.fst).Nodup :=
  (gameState_reachable setup codec checks revealSeed adversary result supported).1.sealOnce

/-- A build consumes the session's pending token, whatever its outcome (`build_registration_response` takes the Rust token by value). -/
theorem build_consumes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    result.2.pending session = none := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
      exact hp
  | some token =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      simp

/-- A state reveal returns only an installed kernel: at every state that an adversary program reaches from the initial state, and so at every answered reveal, the revealed kernel is an installed kernel for some root. Its send chain is the next chain of the step of chain_0, its receive chain and receive counters are the initial ones, its send counter is one and its receive slots are empty, so it stores neither chain_0 nor the sequence-one message material. -/
theorem reveal_post_registration (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (phase1 : published ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk))
    {α : Type} (oa : OracleComp ServerAuthSpec α) (result : α × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) oa).run
      (initialGameState setup publicValue published.2)))
    (keyId : Std.U64) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (revealed : revealKernel keyId result.2 = some kernel) :
    ∃ root, Installed setup.source root kernel := by
  simp only [revealKernel, Option.map_eq_some_iff] at revealed
  obtain ⟨peer, found, rfl⟩ := revealed
  exact (reachable_inv (Reader := Reader) (Response := Response) setup codec checks publicValue beaconSeed oneTime
    kemPk kemSk published phase1 oa result supported).peers keyId peer found

/-- A reveal at the final state of the experiment returns only an installed kernel. -/
theorem reveal_gameState (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary))
    (keyId : Std.U64) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (revealed : revealKernel keyId result.2.2.1 = some kernel) :
    ∃ root, Installed setup.source root kernel := by
  simp only [revealKernel, Option.map_eq_some_iff] at revealed
  obtain ⟨peer, found, rfl⟩ := revealed
  exact (gameState_reachable setup codec checks revealSeed adversary result supported).1.peers keyId peer found

/-- Outside the InitSent phase the finish answers nothing and changes nothing. -/
theorem finish_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (inactive : ∀ control prekey oneTime kem, state.beacon.beacon.phase ≠ .initSent control prekey oneTime kem) :
    (finishOracle setup codec publicValue beaconSeed raw).run state = pure (none, state) := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind]
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem => exact absurd hphase (inactive control prekey oneTime kem)
  | fresh => rfl
  | freshWithCoins => rfl
  | established => rfl
  | aborted => rfl

/-- The finish is single-shot (`beacon.rs:403-406, 488-491, 493-502`): after a finish, every state that any adversary program reaches has every finish inactive, answering nothing and changing nothing. -/
theorem finish_single_shot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (first : Option Pqxdh.Bytes × GameState KemSK)
    (supported : first ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state))
    {α : Type} (oa : OracleComp ServerAuthSpec α) (later : α × GameState KemSK)
    (laterSupported : later ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) oa).run
      first.2))
    (next : Pqxdh.Bytes) :
    (finishOracle setup codec publicValue beaconSeed next).run later.2 = pure (none, later.2) := by
  have afterFinish := (finish_step (Reader := Reader) (Response := Response) (setup := setup)
    (publicValue := publicValue) codec beaconSeed raw state first supported).2.2.2.1
  have inactive := run_inactive setup codec checks publicValue beaconSeed oa first.2 later laterSupported afterFinish
  exact finish_inactive setup codec publicValue beaconSeed next later.2
    (fun control prekey oneTime kem phase => inactive ⟨control, prekey, oneTime, kem, phase⟩)

/-- With an empty payload the builder rejects before its seal: it makes no seal callback (`server.rs:459-462`). -/
theorem empty_seal_bound {Metadata PeerMetadata Consumed : Type} (source : FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (metadata : PeerMetadata)
    (server : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    (PqxdhServerRegistrationPublication.build source pending root (some []) metadata server).IsQueryBoundP
      (fun query => PqxdhServerRegistrationPublication.callKind query = .seal) 0 := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok server.control
  simp only [PqxdhServerRegistrationPublication.build, hnext, PqxdhServerRegistrationPublication.continueRust]
  cases next with
  | Err => exact isQueryBoundP_pure _ _ _
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        server.control pending ⟨server.server.identity, server.identityKeyId⟩
        (if (server.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
      simp only [hprepared]
      cases prepared with
      | Err => exact isQueryBoundP_pure _ _ _
      | Ok candidate =>
          obtain ⟨kernel, hinit, _⟩ :=
            PqxdhServerRegistrationPublication.candidate_initial_state source unitRatchet candidate root
          simp only [PqxdhServerRegistrationPublication.candidateTail, hinit,
            PqxdhServerRegistrationPublication.continueRust, Option.getD_some, List.isEmpty_nil, ite_true]
          rw [isQueryBoundP_query_bind_iff]
          refine ⟨Or.inl (by simp [PqxdhServerRegistrationPublication.callKind,
            PqxdhServerRegistrationPublication.auxKind]), fun valid => ?_⟩
          cases valid
          · exact isQueryBoundP_pure _ _ _
          · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            rw [isQueryBoundP_query_bind_iff]
            refine ⟨Or.inl (by simp [PqxdhServerRegistrationPublication.callKind,
              PqxdhServerRegistrationPublication.auxKind]), fun reserved => ?_⟩
            cases reserved <;> exact isQueryBoundP_pure _ _ _

/-- A build with an empty payload answers nothing and seals nothing; its token is still consumed (`build_consumes`), as in Rust, where the derivation has already happened in the accept. -/
theorem empty_payload (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session (some [])).run state)) :
    result.1 = none ∧ result.2.ghost.seals = state.ghost.seals := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
      exact ⟨rfl, rfl⟩
  | some token =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      obtain ⟨tailMember, _⟩ := liftCoins_mem _ _ _ lifted
      simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      have noLog := run_count (tailImpl setup codec checks)
        (fun query => PqxdhServerRegistrationPublication.callKind query = .seal) (fun state => state.1.length)
        (fun query state result supported => by
          obtain ⟨extra, eq, bound⟩ := tailImpl_log setup codec checks query state result supported
          rw [eq, List.length_append]
          omega)
        _ 0 (empty_seal_bound setup.source token.pending token.root () _) _ tail.1 tailMember
      simp only [List.length_nil, Nat.add_zero, Nat.le_zero, List.length_eq_zero_iff] at noLog
      refine ⟨?_, by simp [noLog]⟩
      rcases build_support (tailImpl setup codec checks) setup.source (tailImpl_kdf setup codec checks) token.pending
        token.root (some []) () _ _ tail.1 tailMember with unchanged | ⟨_, _, _, _, _, nonempty⟩
      · simp [unchanged, settle]
      · exact absurd rfl nonempty

end Support

/-! ## Partnering by identical root derivation -/

section Partnering

/-- Every input the Server's Phase 1 prefix reaches carries the actual reached static-DH reference: the prekey from the verified bundle, publicly admitted. -/
theorem session_references (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (consumed final : List Pqxdh.Bytes)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (reached : (some input, final) ∈ support ((serverPrefix setup codec checks raw).run consumed)) :
    PqxdhServerStaticDhSource.References setup.serverDomain input :=
  PqxdhServerStaticDhSource.collect_references setup.serverDomain (serverAux setup codec checks) (fun _ => pure ())
    raw consumed final input reached

/-- The root input of a Server session's derivation is the root input of the extracted `server_accept` on the session's concrete inputs, computed with the Server seed (`PqxdhServerRelatedRootInput.accept_success`). -/
theorem session_root_input (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (references : PqxdhServerStaticDhSource.References setup.serverDomain input)
    (valid : PqxdhServerRelatedRootInput.localNonzero input) (control : pqxdh.ServerState)
    (serverBinding : pqxdh.ServerBinding) :
    ∃ pending, PqxdhServerRelatedRootInput.accept control serverBinding
        (PqxdhServerStaticDhSource.concreteInputs setup.joint seed input) = ok (.Ok (control, pending)) ∧
      rootInput setup seed scalar (PqxdhServerRelatedRootInput.message input) =
        some (absBytes pending.root_key_input.bytes) := by
  obtain ⟨pending, accepted, _, rooted, _⟩ := PqxdhServerRelatedRootInput.accept_success setup.source.crypto
    setup.joint setup.dh setup.serverDomain setup.secretOfSeed setup.wiring seed scalar input references valid
    control serverBinding
  exact ⟨pending, accepted, rooted⟩

/-- The root input of the Beacon's derivation is the root input of the extracted Beacon builder on the Beacon's concrete inputs, computed with the prekey scalar (`PqxdhJointDhExtractRoot.beacon_source`). -/
theorem beacon_root_input (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (collected : PqxdhPhase2GapDhSource.Inputs Response)
    (references : PqxdhPhase2GapDhSource.References setup.beaconDomain collected)
    (converted : peer collected.serverConverted = (setup.joint.publicKeys seed).convertedX25519)
    (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input
      (PqxdhPhase2GapDhSource.concreteInputs setup.dh scalar collected).finishInputs.shared_secrets = ok (.Ok root)) :
    rootInput setup seed scalar
        (PqxdhJointDhExtractRoot.beaconMessage (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) collected) =
      some (absBytes root.bytes) :=
  PqxdhJointDhExtractRoot.beacon_source setup.dh setup.beaconDomain seed scalar collected references converted root built

/-- Partnering compares extracted root inputs, at the level of inputs: for a Server input with its reached reference that passed the local nonzero test, and a Beacon preparation with its references, the pinned conversion and a successful extracted builder, the extracted `server_accept` succeeds, and the two derivations have the same root input exactly when the two extracted 192-byte root inputs are equal. The key ID plays no part. -/
theorem root_inputs_iff (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (serverReferences : PqxdhServerStaticDhSource.References setup.serverDomain input)
    (valid : PqxdhServerRelatedRootInput.localNonzero input) (control : pqxdh.ServerState)
    (serverBinding : pqxdh.ServerBinding)
    (collected : PqxdhPhase2GapDhSource.Inputs Response)
    (beaconReferences : PqxdhPhase2GapDhSource.References setup.beaconDomain collected)
    (converted : peer collected.serverConverted = (setup.joint.publicKeys seed).convertedX25519)
    (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input
      (PqxdhPhase2GapDhSource.concreteInputs setup.dh scalar collected).finishInputs.shared_secrets = ok (.Ok root)) :
    ∃ pending, PqxdhServerRelatedRootInput.accept control serverBinding
        (PqxdhServerStaticDhSource.concreteInputs setup.joint seed input) = ok (.Ok (control, pending)) ∧
      ((∃ bytes, rootInput setup seed scalar (PqxdhServerRelatedRootInput.message input) = some bytes ∧
          rootInput setup seed scalar (PqxdhJointDhExtractRoot.beaconMessage
            (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) collected) = some bytes) ↔
        absBytes pending.root_key_input.bytes = absBytes root.bytes) := by
  obtain ⟨pending, accepted, serverRoot⟩ :=
    session_root_input setup seed scalar input serverReferences valid control serverBinding
  refine ⟨pending, accepted, ?_⟩
  rw [serverRoot, beacon_root_input setup seed scalar collected beaconReferences converted root built]
  constructor
  · rintro ⟨bytes, left, right⟩
    exact (Option.some.inj left).trans (Option.some.inj right).symm
  · intro equal
    exact ⟨_, rfl, by rw [equal]⟩

/-- Partnering by identical root derivation, on every run of the experiment: for a session touch in the acceptance snapshot there are the session's reached Server input and the Beacon's reached preparation, whose root request is the snapshot's first Beacon touch, with a successful extracted Beacon builder; for every Server control, the extracted `server_accept` of the session succeeds, and the session is a partner exactly when its extracted 192-byte root input equals the Beacon's. Every hypothesis of `root_inputs_iff` is discharged on the run. -/
theorem partner_iff_root_input (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary))
    (snap : Snapshot) (found : result.2.2.1.ghost.acceptance = some snap)
    (index : Nat) (message : PqxdhJointDhExtractFamily.Message) (reply : Option RootOutput)
    (touched : Touch.session index message reply ∈ snap.touches) :
    ∃ (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
      (collected : PqxdhPhase2GapDhSource.Inputs Response) (root : pqxdh.RootKeyInput),
      message = PqxdhServerRelatedRootInput.message input ∧
      firstBeacon snap.touches = some (PqxdhJointDhExtractRoot.beaconMessage
        (PqxdhJointGapDh.challenge setup.joint setup.dh result.1 result.2.1) collected) ∧
      pqxdh.build_root_key_input
        (PqxdhPhase2GapDhSource.concreteInputs setup.dh result.2.1 collected).finishInputs.shared_secrets =
          ok (.Ok root) ∧
      ∀ control, ∃ pending, PqxdhServerRelatedRootInput.accept control
          (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh result.1 result.2.1))
          (PqxdhServerStaticDhSource.concreteInputs setup.joint result.1 input) = ok (.Ok (control, pending)) ∧
        (Partner setup result.1 result.2.1 snap index ↔ absBytes pending.root_key_input.bytes = absBytes root.bytes) := by
  have invariant := (gameState_reachable (Reader := Reader) (Response := Response) setup codec checks revealSeed
    adversary result supported).1
  have grown := (invariant.frozen snap found).1
  obtain ⟨input, rfl, serverReferences, valid⟩ := invariant.sessionOrigin index message reply (grown.subset touched)
  obtain ⟨before, beaconTouch, snapEq, clean⟩ := invariant.atomic snap found
  have first : firstBeacon snap.touches = some beaconTouch := by
    rw [snapEq]
    exact firstBeacon_after before [] beaconTouch clean
  have beaconMember : Touch.beacon beaconTouch ∈ result.2.2.1.ghost.touches :=
    grown.subset (by rw [snapEq]; exact List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨collected, metadata, control, rfl, beaconReferences, conversion, pinnedControl, admitted⟩ :=
    invariant.beaconOrigin _ beaconMember
  have pin : absBytes control.expected_server_binding.identity_public_key =
      (setup.joint.publicKeys result.1).ed25519.toList := by
    rw [pinnedControl]
    simp only [binding, PqxdhJointGapDh.challenge, PqxdhRootTableInitialization.rootArray_bytes]
  have converted := PqxdhPhase2DhMetadata.pinned_conversion setup.source.crypto setup.joint setup.secretOfSeed
    setup.wiring result.1 control collected metadata pin admitted conversion
  have known := (PqxdhPhase2DhMetadata.admitted_fields control collected metadata admitted).2.1
  have nonzero := (PqxdhPhase2DhMetadata.source_nonzero setup.dh setup.beaconDomain result.2.1 collected
    beaconReferences).mpr known
  obtain ⟨root, built, _⟩ := (build_root_key_input_abs
    (PqxdhPhase2GapDhSource.concreteInputs setup.dh result.2.1 collected).finishInputs.shared_secrets).1 nonzero
  refine ⟨input, collected, root, rfl, first, built, fun control' => ?_⟩
  obtain ⟨pending, accepted, serverRoot⟩ := session_root_input setup result.1 result.2.1 input serverReferences valid
    control' (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh result.1 result.2.1))
  have beaconRoot := beacon_root_input setup result.1 result.2.1 collected beaconReferences converted root built
  have beaconBytes : beaconInput setup result.1 result.2.1 snap.touches = some (absBytes root.bytes) := by
    rw [beaconInput, first]
    exact beaconRoot
  refine ⟨pending, accepted, ⟨?_, ?_⟩⟩
  · rintro ⟨other, otherReply, bytes, otherTouched, otherRoot, beaconOther⟩
    obtain ⟨same, _⟩ := invariant.sessionOnce index other otherReply _ reply (grown.subset otherTouched)
      (grown.subset touched)
    subst same
    rw [serverRoot] at otherRoot
    rw [beaconBytes] at beaconOther
    exact (Option.some.inj otherRoot).trans (Option.some.inj beaconOther).symm
  · intro equal
    exact ⟨_, reply, _, touched, serverRoot, by rw [beaconBytes, equal]⟩

end Partnering

/-! ## Decomposition of the winning event -/

section Decomposition

/-- Without the adversary's table query at the Beacon's input, and with every session index below `Q`, the Beacon's table entry has an owner. -/
theorem owner_some (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (Q : Nat)
    (ghost : Ghost) (sessions : Nat)
    (touched : ∀ index message reply, Touch.session index message reply ∈ ghost.touches → index < sessions)
    (bounded : sessions ≤ Q) (clean : ¬ BadB setup seed scalar ghost) :
    ∃ j, entryOwner setup seed scalar Q ghost = some j := by
  unfold entryOwner
  cases hb : beaconInput setup seed scalar ghost.touches with
  | none => exact ⟨_, rfl⟩
  | some bytes =>
      have present : ∃ touch ∈ ghost.touches, touchInput setup seed scalar touch = some bytes := by
        unfold beaconInput at hb
        rw [Option.bind_eq_some_iff] at hb
        obtain ⟨message, found, rooted⟩ := hb
        unfold firstBeacon at found
        obtain ⟨touch, member, hit⟩ := List.exists_of_findSome?_eq_some found
        cases touch with
        | beacon other =>
            simp only [Option.some.injEq] at hit
            subst hit
            exact ⟨_, member, rooted⟩
        | session index other reply => simp at hit
        | adversary other => simp at hit
      dsimp only
      cases hf : ghost.touches.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes)) with
      | none =>
          obtain ⟨touch, member, fits⟩ := present
          have := List.find?_eq_none.mp hf touch member
          simp [fits] at this
      | some touch =>
          have member := List.mem_of_find?_eq_some hf
          have fits := List.find?_some hf
          simp only [decide_eq_true_eq] at fits
          cases touch with
          | session index message reply =>
              have below := touched index message reply member
              have bound : index < Q := Nat.lt_of_lt_of_le below bounded
              exact ⟨⟨index, Nat.lt_succ_of_lt bound⟩, by simp [bound]⟩
          | beacon message => exact ⟨_, rfl⟩
          | adversary other =>
              simp only [touchInput, Option.some.injEq] at fits
              subst fits
              exact absurd ⟨other, hb, member⟩ clean

/-- The first touch at the Beacon's root input, in a log that extends an atomic snapshot, lies in the snapshot's part up to and including the Beacon's touch. -/
theorem find_atomic (predicate : Touch → Bool) (before rest : List Touch) (message : PqxdhJointDhExtractFamily.Message)
    (fits : predicate (Touch.beacon message) = true) :
    ∃ touch, (before ++ [Touch.beacon message]).find? predicate = some touch ∧
      ((before ++ [Touch.beacon message]) ++ rest).find? predicate = some touch := by
  have present : ((before ++ [Touch.beacon message]).find? predicate).isSome := by
    rw [List.find?_isSome]
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fits⟩
  obtain ⟨touch, found⟩ := Option.isSome_iff_exists.mp present
  refine ⟨touch, found, ?_⟩
  rw [List.find?_append, found]
  rfl

/-- If the owner of the Beacon's table entry is the Beacon, no Server session is a partner at the acceptance: every session touch in the atomic snapshot precedes the Beacon's touch. -/
theorem owner_beacon_ghost (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (Q : Nat)
    (ghost : Ghost) (snap : Snapshot) (isPrefix : snap.touches <+: ghost.touches) (before : List Touch)
    (beaconTouch : PqxdhJointDhExtractFamily.Message) (snapEq : snap.touches = before ++ [Touch.beacon beaconTouch])
    (clean : ∀ other, Touch.beacon other ∉ before)
    (owned : entryOwner setup seed scalar Q ghost = some (Fin.last Q)) (index : Nat) :
    ¬ Partner setup seed scalar snap index := by
  rintro ⟨message, reply, bytes, touched, rooted, beaconSnap⟩
  obtain ⟨rest, finalEq⟩ := isPrefix
  have beaconFinal := beaconInput_prefix setup seed scalar _ _ bytes beaconSnap ⟨rest, finalEq⟩
  rw [snapEq] at touched
  have inBefore : Touch.session index message reply ∈ before := by
    rcases List.mem_append.mp touched with inside | last
    · exact inside
    · simp at last
  have present : (before.find? fun touch => decide (touchInput setup seed scalar touch = some bytes)).isSome := by
    rw [List.find?_isSome]
    exact ⟨_, inBefore, by simp [touchInput, rooted]⟩
  obtain ⟨touch, found⟩ := Option.isSome_iff_exists.mp present
  have finalFound : ghost.touches.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes)) =
      some touch := by
    rw [← finalEq, snapEq, List.find?_append, List.find?_append, found]
    rfl
  unfold entryOwner at owned
  rw [beaconFinal] at owned
  dsimp only at owned
  rw [finalFound] at owned
  have member := List.mem_of_find?_eq_some found
  cases touch with
  | session other otherMessage otherReply =>
      simp only at owned
      split at owned
      · simp only [Option.some.injEq, Fin.ext_iff, Fin.val_last] at owned
        omega
      · cases owned
  | beacon other => exact clean other member
  | adversary other => cases owned

/-- If the owner of the Beacon's table entry is session `j` below `Q`, that session is a partner at the acceptance: its touch at the Beacon's root input precedes the Beacon's touch, so it lies in the atomic snapshot. -/
theorem owner_session_ghost (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (Q : Nat)
    (ghost : Ghost) (snap : Snapshot) (isPrefix : snap.touches <+: ghost.touches) (before : List Touch)
    (beaconTouch : PqxdhJointDhExtractFamily.Message) (snapEq : snap.touches = before ++ [Touch.beacon beaconTouch])
    (clean : ∀ other, Touch.beacon other ∉ before) (j : Fin (Q + 1))
    (owned : entryOwner setup seed scalar Q ghost = some j) (session : j.val < Q) :
    Partner setup seed scalar snap j.val := by
  obtain ⟨rest, finalEq⟩ := isPrefix
  have firstSnap : firstBeacon snap.touches = some beaconTouch := by
    rw [snapEq]
    exact firstBeacon_after before [] beaconTouch clean
  have firstFinal := firstBeacon_prefix _ _ beaconTouch firstSnap ⟨rest, finalEq⟩
  unfold entryOwner at owned
  cases hb : beaconInput setup seed scalar ghost.touches with
  | none =>
      rw [hb] at owned
      simp only [Option.some.injEq] at owned
      subst owned
      simp at session
  | some bytes =>
      rw [hb] at owned
      dsimp only at owned
      have beaconRoot : rootInput setup seed scalar beaconTouch = some bytes := by
        rw [beaconInput, firstFinal] at hb
        exact hb
      obtain ⟨touch, found, finalFound⟩ := find_atomic
        (fun touch => decide (touchInput setup seed scalar touch = some bytes)) before rest beaconTouch
        (by simp [touchInput, beaconRoot])
      rw [← finalEq, snapEq, finalFound] at owned
      have member := List.mem_of_find?_eq_some found
      have fits := List.find?_some found
      simp only [decide_eq_true_eq] at fits
      cases touch with
      | session other message reply =>
          simp only at owned
          split at owned
          · simp only [Option.some.injEq] at owned
            subst owned
            refine ⟨message, reply, bytes, by rw [snapEq]; exact member, fits, ?_⟩
            rw [beaconInput, firstSnap]
            exact beaconRoot
          · cases owned
      | beacon other =>
          simp only [Option.some.injEq] at owned
          subst owned
          simp at session
      | adversary other => cases owned

/-- On every run with an acceptance, if the owner of the Beacon's table entry is the Beacon, no Server session is a partner; so the winning event can only be `W1`. -/
theorem owner_beacon_no_partner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary))
    (Q : Nat) (snap : Snapshot) (found : result.2.2.1.ghost.acceptance = some snap)
    (owned : entryOwner setup result.1 result.2.1 Q result.2.2.1.ghost = some (Fin.last Q)) (index : Nat) :
    ¬ Partner setup result.1 result.2.1 snap index := by
  have invariant := (gameState_reachable (Reader := Reader) (Response := Response) setup codec checks revealSeed
    adversary result supported).1
  obtain ⟨before, beaconTouch, snapEq, clean⟩ := invariant.atomic snap found
  exact owner_beacon_ghost setup result.1 result.2.1 Q _ snap (invariant.frozen snap found).1 before beaconTouch
    snapEq clean owned index

/-- On every run with an acceptance, if the owner of the Beacon's table entry is session `j` below `Q`, that session is a partner; so the winning event cannot be `W1`. -/
theorem owner_session_partner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary))
    (Q : Nat) (snap : Snapshot) (found : result.2.2.1.ghost.acceptance = some snap) (j : Fin (Q + 1))
    (owned : entryOwner setup result.1 result.2.1 Q result.2.2.1.ghost = some j) (session : j.val < Q) :
    Partner setup result.1 result.2.1 snap j.val := by
  have invariant := (gameState_reachable (Reader := Reader) (Response := Response) setup codec checks revealSeed
    adversary result supported).1
  obtain ⟨before, beaconTouch, snapEq, clean⟩ := invariant.atomic snap found
  exact owner_session_ghost setup result.1 result.2.1 Q _ snap (invariant.frozen snap found).1 before beaconTouch
    snapEq clean j owned session

/-- On every run, if the owner of the Beacon's table entry is the Beacon, the winning event is `W1` alone: an acceptance has no partner, so neither `W2` nor `W3` holds. -/
theorem owner_beacon_only_w1 (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary)) (Q : Nat)
    (owned : entryOwner setup result.1 result.2.1 Q result.2.2.1.ghost = some (Fin.last Q)) :
    ¬ W2 setup result.1 result.2.1 result.2.2.1.ghost ∧ ¬ W3 setup result.1 result.2.1 result.2.2.1.ghost := by
  constructor
  · rintro ⟨snap, found, ⟨index, partner⟩, _⟩
    exact owner_beacon_no_partner (Reader := Reader) (Response := Response) setup codec checks revealSeed adversary
      result supported Q snap found owned index partner
  · rintro ⟨snap, found, i, _, _, partner, _⟩
    exact owner_beacon_no_partner (Reader := Reader) (Response := Response) setup codec checks revealSeed adversary
      result supported Q snap found owned i partner

/-- On every run, if the owner of the Beacon's table entry is a session below `Q`, the winning event is not `W1`. -/
theorem owner_session_not_w1 (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary)
    (result : IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support (gameState setup codec checks revealSeed adversary)) (Q : Nat) (j : Fin (Q + 1))
    (owned : entryOwner setup result.1 result.2.1 Q result.2.2.1.ghost = some j) (session : j.val < Q) :
    ¬ W1 setup result.1 result.2.1 result.2.2.1.ghost := by
  rintro ⟨snap, found, none⟩
  exact none j.val (owner_session_partner (Reader := Reader) (Response := Response) setup codec checks revealSeed
    adversary result supported Q snap found j owned session)

/-- The winning event splits into the adversary's table query at the Beacon's input, the narrowed session collision, and the per-entry events, given the snapshot prefix and a session bound. -/
theorem win_cases (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (Q : Nat)
    (ghost : Ghost) (sessions : Nat)
    (isPrefix : ∀ snap, ghost.acceptance = some snap → snap.touches <+: ghost.touches)
    (touched : ∀ index message reply, Touch.session index message reply ∈ ghost.touches → index < sessions)
    (bounded : sessions ≤ Q) (win : Win setup seed scalar ghost) :
    BadB setup seed scalar ghost ∨ CollB setup seed scalar ghost ∨
      ∃ j ∈ (Finset.univ : Finset (Fin (Q + 1))), EntryEvent setup seed scalar Q j ghost := by
  by_cases bad : BadB setup seed scalar ghost
  · exact Or.inl bad
  by_cases coll : CollB setup seed scalar ghost
  · exact Or.inr (Or.inl coll)
  refine Or.inr (Or.inr ?_)
  have main : W1 setup seed scalar ghost ∨ W2 setup seed scalar ghost := by
    rcases win with w1 | w2 | w3
    · exact Or.inl w1
    · exact Or.inr w2
    · exact absurd (w3_collB setup seed scalar ghost isPrefix w3) coll
  obtain ⟨j, found⟩ := owner_some setup seed scalar Q ghost sessions touched bounded bad
  exact ⟨j, Finset.mem_univ j, main, bad, coll, found⟩

/-- Game decomposition (step 2 of the hybrid chain): under the query budget, the winning probability is at most the probability of the adversary's table query at the Beacon's input, plus the narrowed session collision, plus the sum over the `Q + 1` table owners of the per-entry events. -/
theorem win_le_games (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) :
    Pr{let x ← serverAuthGame setup codec checks revealSeed adversary}[x = true] ≤
      Pr{let result ← gameState setup codec checks revealSeed adversary}[BadB setup result.1 result.2.1 result.2.2.1.ghost] +
        Pr{let result ← gameState setup codec checks revealSeed adversary}[CollB setup result.1 result.2.1 result.2.2.1.ghost] +
        ∑ j : Fin (Q + 1), Pr{let result ← gameState setup codec checks revealSeed adversary}[EntryEvent setup result.1 result.2.1 Q j result.2.2.1.ghost] := by
  classical
  unfold serverAuthGame
  rw [prEvent_map]
  refine le_trans (prEvent_mono_of_support _ _ (fun result : IdentitySeed × ScalarBytes × GameState KemSK ×
      PqxdhJointDhExtractFamily.State =>
      BadB setup result.1 result.2.1 result.2.2.1.ghost ∨ (CollB setup result.1 result.2.1 result.2.2.1.ghost ∨
        ∃ j ∈ (Finset.univ : Finset (Fin (Q + 1))), EntryEvent setup result.1 result.2.1 Q j result.2.2.1.ghost)) ?_) ?_
  · intro result supported win
    obtain ⟨invariant, sessionBound⟩ := gameState_reachable setup codec checks revealSeed adversary result supported
    exact win_cases setup result.1 result.2.1 Q result.2.2.1.ghost result.2.2.1.sessions
      (fun snap found => (invariant.frozen snap found).1) invariant.touched (sessionBound Q qH qHash budget)
      (by simpa using win)
  · refine le_trans (prEvent_or_le (gameState setup codec checks revealSeed adversary) _ _) ?_
    rw [add_assoc]
    exact add_le_add le_rfl (le_trans (prEvent_or_le (gameState setup codec checks revealSeed adversary) _ _)
      (add_le_add le_rfl (prEvent_exists_finset_le (Finset.univ : Finset (Fin (Q + 1)))
        (gameState setup codec checks revealSeed adversary) _)))

end Decomposition

/-! ## Erasing the derived roots from the ghost -/

section Erasure

/-- Forget the family reply, the derived root, of a session touch. -/
def eraseTouch : Touch → Touch
  | .session index message _ => .session index message none
  | touch => touch

/-- Forget every session reply in a snapshot. -/
def eraseSnap (snap : Snapshot) : Snapshot := { snap with touches := snap.touches.map eraseTouch }

/-- Forget every session reply in the ghost, including the snapshot. -/
def eraseGhost (ghost : Ghost) : Ghost :=
  ⟨ghost.touches.map eraseTouch, ghost.seals, ghost.acceptance.map eraseSnap⟩

/-- Erasing replies keeps the Beacon's first touch. -/
theorem firstBeacon_erase (touches : List Touch) : firstBeacon (touches.map eraseTouch) = firstBeacon touches := by
  induction touches with
  | nil => rfl
  | cons touch rest ih =>
      cases touch <;> simp_all [firstBeacon, eraseTouch]

/-- Erasing replies keeps the Beacon's root input. -/
theorem beaconInput_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (touches : List Touch) :
    beaconInput setup seed scalar (touches.map eraseTouch) = beaconInput setup seed scalar touches := by
  simp [beaconInput, firstBeacon_erase]

/-- Erasing the reply keeps the table input a touch reads. -/
theorem touchInput_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (touch : Touch) :
    touchInput setup seed scalar (eraseTouch touch) = touchInput setup seed scalar touch := by
  cases touch <;> rfl

/-- A session touches a message before erasure exactly when it does after erasure, for some reply. -/
theorem session_mem_erase (touches : List Touch) (index : Nat) (message : PqxdhJointDhExtractFamily.Message) :
    (∃ reply, Touch.session index message reply ∈ touches.map eraseTouch) ↔
      ∃ reply, Touch.session index message reply ∈ touches := by
  constructor
  · rintro ⟨reply, member⟩
    obtain ⟨touch, inside, eq⟩ := List.mem_map.mp member
    cases touch with
    | session i m r =>
        simp only [eraseTouch, Touch.session.injEq] at eq
        obtain ⟨rfl, rfl, _⟩ := eq
        exact ⟨r, inside⟩
    | beacon m => simp [eraseTouch] at eq
    | adversary b => simp [eraseTouch] at eq
  · rintro ⟨reply, member⟩
    exact ⟨none, List.mem_map.mpr ⟨_, member, rfl⟩⟩

/-- Erasing replies keeps the adversary touches. -/
theorem adversary_mem_erase (touches : List Touch) (bytes : Pqxdh.Bytes) :
    Touch.adversary bytes ∈ touches.map eraseTouch ↔ Touch.adversary bytes ∈ touches := by
  constructor
  · intro member
    obtain ⟨touch, inside, eq⟩ := List.mem_map.mp member
    cases touch <;> simp_all [eraseTouch]
  · intro member
    exact List.mem_map.mpr ⟨_, member, rfl⟩

/-- Erasing replies keeps partnering. -/
theorem partner_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (snap : Snapshot) (index : Nat) :
    Partner setup seed scalar (eraseSnap snap) index ↔ Partner setup seed scalar snap index := by
  simp only [Partner, eraseSnap, beaconInput_erase]
  constructor
  · rintro ⟨message, reply, bytes, member, root, beacon⟩
    obtain ⟨reply', inside⟩ := (session_mem_erase snap.touches index message).1 ⟨reply, member⟩
    exact ⟨message, reply', bytes, inside, root, beacon⟩
  · rintro ⟨message, reply, bytes, member, root, beacon⟩
    obtain ⟨reply', inside⟩ := (session_mem_erase snap.touches index message).2 ⟨reply, member⟩
    exact ⟨message, reply', bytes, inside, root, beacon⟩

/-- Erasing the derived roots keeps the winning event. -/
theorem win_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (ghost : Ghost) :
    Win setup seed scalar (eraseGhost ghost) ↔ Win setup seed scalar ghost := by
  cases h : ghost.acceptance with
  | none => simp [Win, W1, W2, W3, eraseGhost, h]
  | some snap =>
      have p := partner_erase setup seed scalar snap
      simp only [Win, W1, W2, W3, eraseGhost, h, Option.map_some, Option.some.injEq, exists_eq_left', p]
      rfl

/-- Erasing the derived roots keeps the adversary's table query at the Beacon's input. -/
theorem badB_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (ghost : Ghost) :
    BadB setup seed scalar (eraseGhost ghost) ↔ BadB setup seed scalar ghost := by
  simp only [BadB, eraseGhost, beaconInput_erase, adversary_mem_erase]

/-- Erasing the derived roots keeps the narrowed session collision. -/
theorem collB_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (ghost : Ghost) :
    CollB setup seed scalar (eraseGhost ghost) ↔ CollB setup seed scalar ghost := by
  simp only [CollB, eraseGhost, beaconInput_erase]
  constructor
  · rintro ⟨i, j, mi, mj, ri, rj, bytes, ne, ti, tj, rest⟩
    obtain ⟨ri', ti'⟩ := (session_mem_erase ghost.touches i mi).1 ⟨ri, ti⟩
    obtain ⟨rj', tj'⟩ := (session_mem_erase ghost.touches j mj).1 ⟨rj, tj⟩
    exact ⟨i, j, mi, mj, ri', rj', bytes, ne, ti', tj', rest⟩
  · rintro ⟨i, j, mi, mj, ri, rj, bytes, ne, ti, tj, rest⟩
    obtain ⟨ri', ti'⟩ := (session_mem_erase ghost.touches i mi).2 ⟨ri, ti⟩
    obtain ⟨rj', tj'⟩ := (session_mem_erase ghost.touches j mj).2 ⟨rj, tj⟩
    exact ⟨i, j, mi, mj, ri', rj', bytes, ne, ti', tj', rest⟩

/-- Erasing the derived roots keeps the owner of the Beacon's table entry. -/
theorem entryOwner_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (Q : Nat)
    (ghost : Ghost) : entryOwner setup seed scalar Q (eraseGhost ghost) = entryOwner setup seed scalar Q ghost := by
  unfold entryOwner
  simp only [eraseGhost, beaconInput_erase]
  cases beaconInput setup seed scalar ghost.touches with
  | none => rfl
  | some bytes =>
      dsimp only
      rw [List.find?_map]
      have same : ((fun touch => decide (touchInput setup seed scalar touch = some bytes)) ∘ eraseTouch) =
          fun touch => decide (touchInput setup seed scalar touch = some bytes) := by
        funext touch
        simp [touchInput_erase]
      rw [same]
      cases ghost.touches.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes)) with
      | none => rfl
      | some touch => cases touch <;> rfl

/-- Erasing the derived roots keeps every per-entry event. -/
theorem entryEvent_erase (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (Q : Nat)
    (j : Fin (Q + 1)) (ghost : Ghost) :
    EntryEvent setup seed scalar Q j (eraseGhost ghost) ↔ EntryEvent setup seed scalar Q j ghost := by
  have w12 : (W1 setup seed scalar (eraseGhost ghost) ∨ W2 setup seed scalar (eraseGhost ghost)) ↔
      (W1 setup seed scalar ghost ∨ W2 setup seed scalar ghost) := by
    cases h : ghost.acceptance with
    | none => simp [W1, W2, eraseGhost, h]
    | some snap =>
        have p := partner_erase setup seed scalar snap
        simp only [W1, W2, eraseGhost, h, Option.map_some, Option.some.injEq, exists_eq_left', p]
        rfl
  simp only [EntryEvent, w12, badB_erase, collB_erase, entryOwner_erase]

end Erasure

/-! ## Interfaces for later stages -/

section Interfaces

/-- Under the Extract random-oracle family, lifted coins run the computation itself and leave the family state unchanged. -/
theorem rom_coins (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) {α : Type} (work : ProbComp α) (state : PqxdhJointDhExtractFamily.State) :
    (simulateQ (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
      (familyCoins work)).run state = (fun value => (value, state)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp [familyCoins]
  | query_bind query next ih =>
      simp only [familyCoins, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at ih ⊢
      rw [(PqxdhExtractRomFamily.rom_forward hmac joint dh seed scalar).1 query]
      change ((unifSpec.query query : ProbComp _) >>= fun reply =>
        (simulateQ (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
          (simulateQ (fun query => (RootSpec.query (.inl query) : OracleComp RootSpec _)) (next reply))).run state) = _
      simp only [ih, map_bind]

/-- Forget the auxiliary state of a shared primitive state. -/
def forgetAux {A : Type} (state : RawCtxSharedPrimitive.SharedState A) : RawCtxSharedPrimitive.SharedState Unit :=
  ((), state.2)

/-- The shared-cache native primitives act on the cache alone: forgetting the auxiliary state commutes with every step. -/
theorem nativeImpl_forget {A : Type} (source : FixedHkdfSha512NoSaltSource) (query : RawCtxSourceOpen.NativeSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState A) :
    Prod.map id forgetAux <$>
        (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run state =
      (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run (forgetAux state) := by
  rcases query with request | (bytes | input)
  · change Prod.map id forgetAux <$> (RawCtxSourceHkdf.kdfImpl source request).run state =
      (RawCtxSourceHkdf.kdfImpl source request).run (forgetAux state)
    rw [RawCtxSourceHkdf.kdf_step, RawCtxSourceHkdf.kdf_step, map_pure]
    rfl
  · change Prod.map id forgetAux <$> (RawCtxSharedPrimitive.openingImpl source.crypto (.inl bytes)).run state =
      (RawCtxSharedPrimitive.openingImpl source.crypto (.inl bytes)).run (forgetAux state)
    simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, map_bind, map_pure]
    rfl
  · change Prod.map id forgetAux <$> (RawCtxSharedPrimitive.openingImpl source.crypto (.inr input)).run state =
      (RawCtxSharedPrimitive.openingImpl source.crypto (.inr input)).run (forgetAux state)
    simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, map_pure]
    rfl

/-- The mixed shared primitives act on the cache alone. -/
theorem sharedImpl_forget {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A) :
    Prod.map id forgetAux <$>
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run state =
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run
        (forgetAux state) := by
  simp only [RawCtxMixedShared.sharedImpl, QueryImpl.apply_compose]
  exact map_run_simulateQ_eq_of_query_map_eq _ _ forgetAux (fun query state => nativeImpl_forget source query state)
    _ state

/-- The native response tail acts on the cache alone. -/
theorem nativeTail_forget {A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A) :
    Prod.map id forgetAux <$> (nativeTail setup codec checks query).run state =
      (nativeTail setup codec checks query).run (forgetAux state) := by
  simp only [nativeTail, QueryImpl.apply_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ forgetAux (fun query state => ?_) _ state
  rcases query with request | request
  · change Prod.map id forgetAux <$> ((RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) ∘ₛ RawCtxMixedOwner.sendLift) request).run state =
      ((RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) ∘ₛ RawCtxMixedOwner.sendLift) request).run (forgetAux state)
    simp only [QueryImpl.apply_compose]
    exact map_run_simulateQ_eq_of_query_map_eq _ _ forgetAux
      (fun query state => sharedImpl_forget setup.source codec.frameWrite query state) _ state
  · change Prod.map id forgetAux <$> (tailAux codec checks request).run state =
      (tailAux codec checks request).run (forgetAux state)
    cases request <;> simp only [tailAux, StateT.run_pure, map_pure] <;> rfl

/-- The seal log is pure instrumentation: forgetting it, the logging tail is the native tail `PqxdhRegistrationProtocolState.registrationImpl` under the builder's native adapter. This is the form in which the Server-send factorization of stage S is stated; that lemma (`server_send_factor`, a forward reference) lives in the spike and is to be added by stage B8b. -/
theorem tail_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {α : Type}
    (work : OracleComp PqxdhServerRegistrationPublication.TailSpec α)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    Prod.map id forgetAux <$> (simulateQ (tailImpl setup codec checks) work).run state =
      (simulateQ (PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite (tailAux codec checks))
        (simulateQ PqxdhServerRegistrationPublication.nativeAdapter work)).run (forgetAux state) := by
  rw [← QueryImpl.simulateQ_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ forgetAux (fun query state => ?_) work state
  rcases query with (request | input) | request
  · exact nativeTail_forget setup codec checks _ state
  · change _ = (nativeTail setup codec checks (.inl (.inr input))).run (forgetAux state)
    rw [← nativeTail_forget setup codec checks (.inl (.inr input)) state]
    simp only [tailImpl, StateT.run_bind, map_bind]
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun sealed => ?_
    by_cases present : sealed.1.isSome
    · simp only [present, ite_true, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, map_pure]
      rfl
    · simp only [present, Bool.false_eq_true, ite_false, StateT.run_pure, map_pure]
      rfl
  · exact nativeTail_forget setup codec checks _ state

/-- The Beacon's native tail inside the game has the ordinary AEAD opening branch required by stage B9a's `consumer_opening`. -/
theorem beaconNative_ordinary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    PqxdhPhase2LocalMatching.OrdinaryOpen setup.source.crypto
      (fun query => (onCtx (beaconNative setup codec (.inl query)) : Game KemSK _)) := by
  intro input state result supported
  simp only [onCtx, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have native := coins_support _ _ member
  change inner ∈ support ((RawCtxSharedPrimitive.openingImpl setup.source.crypto (.inr input)).run
    ((), state.ctx)) at native
  simp only [RawCtxSharedPrimitive.openingImpl, StateT.run, support_pure, Set.mem_singleton_iff] at native
  rw [native]

end Interfaces

end BeaconcryptCore.Computational.PqxdhServerAuthExperiment

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.fields_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.fields_inj

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.ofStaged_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.ofStaged_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sealed_fields' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sealed_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sealed_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sealed_eq_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_count

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_bind_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_bind_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.coins_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.coins_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_mem

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.forward_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.forward_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.onCtx_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.onCtx_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.record_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.record_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.liftCoins_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.simulateQ_liftUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.simulateQ_liftUnit

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.client_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.client_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.ctxOnly_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.ctxOnly_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.stage_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.stage_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.toWord32_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.toWord32_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconReached_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconReached_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.phase1_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.phase1_pinned

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeImpl_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeImpl_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sharedImpl_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sharedImpl_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeTail_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeTail_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.tailImpl_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.tailImpl_log

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_log_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_log_length

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.fresh_slots_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.fresh_slots_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.first_send_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.first_send_installed

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.tailImpl_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.tailImpl_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Grows.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Grows.refl

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Grows.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Grows.trans

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_touches' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_touches

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_seals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_keeps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_frozen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_frozen

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_old' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_old

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_new' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.Ghost.accept_new

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_phase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.acceptedOf_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.acceptedOf_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_accept_touch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_accept_touch

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_add_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_add_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.accept_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.accept_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_adversary_touch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.inv_adversary_touch

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.hmac_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.hmac_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.hashOracle_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.hashOracle_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.authHandler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.authHandler_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_inv

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_sessions

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.run_inactive

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.reachable_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.reachable_inv

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.body_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.body_reachable

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.gameState_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.gameState_reachable

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.snapshot_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.snapshot_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_frozen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_frozen

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.firstBeacon_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.firstBeacon_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.firstBeacon_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.firstBeacon_after

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconInput_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconInput_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.w3_collB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.w3_collB

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.snapshot_atomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.snapshot_atomic

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.seal_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.seal_touched

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.pending_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.pending_root

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.seal_once_per_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.seal_once_per_session

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.build_consumes

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.reveal_post_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.reveal_post_registration

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.reveal_gameState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.reveal_gameState

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_inactive

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_single_shot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.finish_single_shot

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.empty_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.empty_seal_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.empty_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.empty_payload

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.session_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.session_references

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.session_root_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.session_root_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beacon_root_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beacon_root_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.root_inputs_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.root_inputs_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.partner_iff_root_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.partner_iff_root_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_some

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.find_atomic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.find_atomic

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_beacon_ghost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_beacon_ghost

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_session_ghost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_session_ghost

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_beacon_no_partner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_beacon_no_partner

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_session_partner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_session_partner

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_beacon_only_w1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_beacon_only_w1

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_session_not_w1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.owner_session_not_w1

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_le_games' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_le_games

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.firstBeacon_erase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.firstBeacon_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconInput_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconInput_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.touchInput_erase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.touchInput_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.session_mem_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.session_mem_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.adversary_mem_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.adversary_mem_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.partner_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.partner_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.win_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.badB_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.badB_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.collB_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.collB_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.entryOwner_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.entryOwner_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.entryEvent_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.entryEvent_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.rom_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.rom_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeImpl_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeImpl_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sharedImpl_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.sharedImpl_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeTail_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.nativeTail_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.tail_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.tail_native

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconNative_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthExperiment.beaconNative_ordinary
