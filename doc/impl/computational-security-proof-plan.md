<!-- SPDX-License-Identifier: 0BSD -->

# Computational-security proof implementation plan

## Status and decision policy

This is a proposed implementation plan written against the `proof` branch at commit `ff12e813a1f4b7ee6f6e86db573dc796eb1d7154`.

The maintained [integration evaluation](computational-security-proof-integration.md) records the implemented four-scenario ProVerif suite, bounded hidden-ROM CTX binding and privacy hops, the one-session one-record SSProve ideal protocol games, the attacker-facing bounded protocol-ROM reduction, standalone hybrid-combiner, one-step erasure-conditioned ratchet, record-integrity event/collision hops, the exact one-bit fresh-guess bound, the active-quantum attacks, and the remaining work.

Except where that evaluation explicitly records a completed milestone, nothing in this planning document is a current security claim, a completed proof, or permission to change the protocol, wire format, persistence format, or public APIs.

The implementation MUST stop at every decision gate identified below and obtain an explicit choice before taking a branch that changes the protocol or materially changes the assumptions or scope of the final theorem.

The default proof architecture deliberately does not duplicate deterministic facts already proved from extracted Rust in F*.
SSProve will prove probabilistic games, reductions, advantage bounds, and randomized package invariants, while F* remains authoritative for the existing exact byte-layout and deterministic state-transition facts.
The result will therefore be a reviewed cross-prover composition unless a separate decision requires a closed theorem in one proof assistant.

## Objective

Add a computational proof backend for beaconcrypt that reuses the production-used [`beaconcrypt-protocol-core`](../../beaconcrypt-core/README.md), hax extraction, the existing F* theorems, and the current formal-proof infrastructure as far as practical.

The proof suite will establish properties of beaconcrypt's composition and state machine rather than re-proving the implementations of Ed25519, X25519, ML-KEM-768, HKDF-SHA-512, ChaCha20-Poly1305-IETF, BLAKE2b-512, or the random-number generator.

The intended positive results are:

- Computational CTX misattribution resistance for the complete beaconcrypt protected payload, reduced to BLAKE2b-512 collision resistance through the existing F* collision-witness theorem.
- Computational pseudorandomness of the hidden registration channel initializer under an explicit collection of primitive assumptions and freshness conditions.
- The correctly oriented registration agreement property: an honest beacon commit has one unique matching earlier server commit.
- Established-session record confidentiality and injective authenticity for both directions under active network control, including public sequence numbers, sender identifiers, and lengths.
- Replay rejection, peer separation, session separation, and direction separation under the actual stateful receive semantics.
- Probabilistic non-reuse of a `(message key, nonce)` pair across every send allocation or seal invocation within the theorem's authoritative state lineage, including attempts that later fail, with explicit collision events and query bounds.
- Ratchet-current-state forward secrecy for material that has been consumed and erased from the modeled live ratchet state, under precisely stated reveal and persistence conditions and without silently allowing later long-term or pending-registration compromise.
- A conditional refinement from the volatile one-owner theorem to a conforming rollback-resistant `SnapshotStore`, if persistence remains in the first proof suite.

The intended negative results are equally important:

- A server commit does not imply a later beacon commit because the response can be dropped or replaced.
- Registration does not give the server explicit beacon key confirmation; a later authenticated beacon-to-server record is the earliest existing protocol event that can provide it.
- Cached skipped receive keys are exposed by a current-state reveal until they are consumed.
- A live symmetric-ratchet chain reveals future traffic material, so beaconcrypt does not provide post-compromise security.
- A revealed or retained pre-consumption snapshot containing an ancestor chain, a duplicated checkpoint restoration, a fork, or a rollback invalidates the corresponding strong erasure or non-reuse premise.
- An arbitrary valid self-signed beacon registration proves key ownership or origin, not application authorization, current liveness, or correct task routing.

## Non-goals

- Do not verify primitive implementations, assembly, libsodium, the operating system RNG, the Rust compiler, hax, F*, Coq/Rocq, SSProve, ProVerif, or machine code.
- Do not assume a monolithic statement such as “PQXDH is secure”; expose the exact primitive games and composition assumptions used by each beaconcrypt theorem.
- Do not port CTX transcript injectivity, little-endian encoding, ratchet array manipulation, or other already-proved deterministic F* facts into SSProve merely to have the same fact in two kernels.
- Do not describe symbolic ProVerif results as computational reductions or replace the existing ProVerif regression suite.
- Do not claim active post-quantum security while Ed25519 and X25519 remain authentication and key-agreement components.
- Do not claim physical erasure, side-channel resistance, panic freedom, crash atomicity, or rollback prevention from an abstract state-erasure theorem.
- Do not silently model a cleaner protocol than production, including independent identity keys, independent initial and step KDFs, atomic failed receives, whole-bundle signatures, or mutual registration confirmation, unless production is changed first.
- Do not treat local Rust return metadata as wire data or conflate an assigned receiver identifier with the sender identifier serialized in a `CryptoFrame`.

## Existing baseline and prerequisites

The maintained [formal-verification analysis](../formal-verification-analysis.md) and [trust-boundary inventory](../../beaconcrypt-core/proofs/trusted-boundary.md) are the baseline for all new claims.

The existing proof assets are:

- Hax-generated F* for selected `protocol-core` functions, plus handwritten lemmas for commitment construction, PQXDH control and layout, and the concrete ratchet.
- F* proofs of the exact 229-byte CTX transcript, complete six-field injectivity, and `ctx_distinct_openings_imply_hash_collision` for arbitrary pure hash and open functions in [`Commitment.Lemmas.fst`](../../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst).
- F* proofs of PQXDH root-input and associated-data layout, conditional equal-root composition, complementary initial ratchet directions, and deterministic commit-state relationships in [`Pqxdh.Lemmas.fst`](../../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst).
- F* proofs of exact ratchet KDF requests and output partitions, reachability, cache capacity, failed-open retention, retry, consumption, replay, and conditional restoration in [`Ratchet.Lemmas.fst`](../../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst).
- A ProVerif active-attacker model, compromise scenarios, failed-active-receive scenarios, reachability checks, and CTX/no-CTX negative controls.
- A locked proof shell and proof entry points in the [`protocol-core` Makefile](../../beaconcrypt-core/Makefile).

The implemented integration extends the locked proof shell with Rocq 9.0.0, SSProve 0.2.4, and MathComp 2.4.0 and checks the Rocq and SSProve identities alongside hax 0.3.7, F*, Z3, and ProVerif.
The exploratory planning probe made hax 0.3.7 emit SSProve `.v` files for selected commitment, PQXDH, and concrete-ratchet items, but those generated files remain non-acceptance evidence because they were not compiled and import the unsafe hax prelude described in the integration evaluation.
The remaining direct-extraction feasibility work MUST reproduce generation inside the locked repository shell and compile the result without hand-editing generated files.

At planning time, the standalone inventory baseline had pre-existing reviewed-hash drift and CI did not invoke `check-inventory`; repairing that baseline and adding an explicit CI job were prerequisites for the computational backend.
That prerequisite is now implemented: the reviewed inventory covers the four-modality ProVerif controls and all repository-owned SSProve sources, the standalone check passes, and the formal-verification matrix invokes `check-inventory` independently from generated-proof checks.
The implemented SSProve target writes compiled output under repository `target/formal-verification/ssprove/`, while its handwritten source and generated proof sources remain under `proofs/` and stay inventoried. Future computational backends MUST preserve that source/output separation.

## Proof architecture

The proof suite will use the following division of responsibility:

```text
production-used protocol-core Rust
        |
        +---- hax -> F*       deterministic layouts, transitions, and source-level invariants
        |
        +---- hax -> SSProve  executable pure core operations used by probabilistic packages
        |
        +---- hax -> ProVerif symbolic active-attacker regression model
        |
production adapters and wire/primitive calls
        |
        +---- reviewed refinement contracts and integration tests

SSProve handwritten layer
        |
        +---- primitive package interfaces and assumption games
        +---- real protocol packages around extracted core operations
        +---- ideal packages, game hops, reductions, bad-event accounting, and final bounds
```

The SSProve backend will have two real-protocol layers:

1. `RealExtracted` packages call hax-generated definitions for every core operation that the feasibility phase can compile and use directly.
2. `RealSpec` packages present a concise game-oriented interface and are related to `RealExtracted` by package equivalences or by explicit F*-backed deterministic contracts.

The ideal packages will express the security property rather than a second implementation of beaconcrypt.
They will replace one primitive or protocol capability at a time so every hop has an explicit reduction or a statistically bounded bad event.

If a production-relevant deterministic operation cannot be used from hax-generated SSProve code, the implementation MUST choose one of these reviewed outcomes:

- Move a minimal dependency-free pure helper into `protocol-core`, use it in production, extract it, and add the corresponding F* and Rust tests.
- Treat the operation as an explicit F*-backed deterministic contract with an adapter-refinement obligation in the inventory.
- Stop and request a scope decision if neither route is proportionate.

Handwriting a cleaner SSProve “real protocol” while merely asserting that it resembles production is not an acceptable fallback.

## Cross-prover contract boundary

F* theorems cannot be mechanically imported as Coq/Rocq proof terms.
The baseline design will therefore make every reused deterministic result an explicit parameter to the SSProve theorem and record how the parameter is discharged outside the Coq/Rocq kernel.

For CTX, the SSProve development will define a module type or record such as `CtxCollisionWitness` whose field states the same pointwise implication as the existing F* theorem.
The generic SSProve reduction will quantify over an implementation of that contract and prove the probability statement for every implementation satisfying it.
The trust-boundary inventory will map that premise to `build_commitment_transcript`, the hax selectors, `production_commitment_input_is_injective`, and `ctx_distinct_openings_imply_hash_collision`.
No Coq/Rocq `Axiom` is needed, and no claim will suggest that Coq/Rocq checked the F* proof.

The same method will be used for deterministic ratchet and PQXDH obligations.
The initial contract ledger will contain at least these entries:

| Contract | Required deterministic fact | Existing discharge evidence |
| --- | --- | --- |
| `DC-CTX-ENCODING` | The production 229-byte transcript has the exact fixed fields and is injective in `(K, N, AD, T, seq, sender_id)`. | `production_commitment_input_is_injective` and its supporting F* layout lemmas. |
| `DC-CTX-WITNESS` | Two distinct accepted explanations of one fixed protected payload yield two distinct equal-hash transcripts. | `ctx_distinct_openings_imply_hash_collision`. |
| `DC-PQXDH-ROOT-INPUT` | The core builds the exact 192-byte `0xff^32 || DH1 || DH2 || DH3 || DH4 || ML-KEM-SS` root input and rejects any all-zero DH component. | PQXDH root-input layout and zero-DH F* lemmas. |
| `DC-PQXDH-ROOT-EQUALITY` | Under the explicit `honest_shared_secrets` equal-DH/equal-KEM premises, the two roles build equal root inputs, and applying one fixed pure derivation to equal inputs gives equal roots. | PQXDH honest-role input-equality and conditional common-fixed-root F* lemmas; this contract does not prove DH, ML-KEM, or HKDF semantics. |
| `DC-PQXDH-AD` | Associated data contains the exact server identity, beacon identity, `PQXDH_INFO`, and `SYM_RATCHET_INFO` in the proved order. | PQXDH associated-data F* lemmas. |
| `DC-PQXDH-TRANSITION` | Core success and abort transitions preserve the intended identities, identifiers, authenticated binding, and candidate-to-committed typestate relationships. | PQXDH transition and honest-run F* lemmas. |
| `AR-REGISTRATION-ORDER` | The production adapter parses and verifies Phase 1, checks replay freshness, performs ephemeral/KEM/DH computation, core acceptance, and root HKDF, then consumes the replay identifier before returning caller-owned pending output; response-ratchet derivation, encryption, serialization, and peer/counter publication happen later. | Adapter source review, integration tests, and trust-inventory correspondence; this ordering is not proved by the F* core lemmas. |
| `DC-RATCHET-REQUEST` | Each core ratchet step supplies the exact live 32-byte input and production label and partitions output as key, next chain, and nonce. | `symmetric_ratchet_kdf_request_is_exact` and `ratchet_step_uses_exact_chain_and_partition`. |
| `DC-RATCHET-DIRECTIONS` | One agreed root produces complementary beacon/server chains and equal opposite-direction material at each sequence. | `concrete_initial_kernels_are_complementary`, `concrete_initial_kernels_are_reachable`, and `concrete_directional_materials_agree`. |
| `DC-RATCHET-STATE` | Admission, the 50-entry bound, advancement, lookup, failed-open retention, successful consumption, replay rejection, and callback results have the proved exact state effects. | Concrete reachability and open/finish F* lemmas. |
| `DC-RESTORE` | Restoration publishes a reachable state only under canonical chain and cached-material provenance premises. | Conditional restoration F* lemmas plus the separately reviewed persistence adapter contract. |

Each ledger entry MUST eventually name the exact theorem, exact Rust item, exact generated module, representations on both sides, and residual trust.
The ledger belongs in the maintained trust-boundary document rather than in an untracked design note.

SSProve will still need native deterministic lemmas about its own package state, oracle logs, event histories, table lookup, and game transformations.
Those facts are not duplicates of F* source-level layout proofs because they relate randomized packages across adversarial calls.
Every new deterministic Coq/Rocq lemma MUST be classified either as package reasoning or as a deliberate duplicate requested for single-kernel assurance.

The final documentation MUST distinguish these assurance levels:

- `F* checked`: a deterministic property of selected hax-extracted Rust.
- `SSProve checked`: a probabilistic game, reduction, equivalence, or bound conditional on named interfaces and contracts.
- `Cross-prover composed`: an SSProve premise discharged by a named F* theorem plus reviewed representation correspondence.
- `Adapter/deployment assumption`: a property outside both extracted boundaries.
- `Single-kernel closed`: available only if every deterministic premise is reproved or imported through a separately justified proof-producing bridge.

## Computational model

### Principals, sessions, and state

The games will be finite but parameterized by adversary query bounds, a maximum application plaintext length `L_max`, and exact maximum encoded handshake and frame sizes so they represent arbitrary polynomially bounded executions rather than one fixed trace and satisfy SSProve's finite-type requirements.
They will maintain explicit tables for server identities, honest beacon identities, attacker-owned beacon identities, caller-owned pending registration outputs, committed sessions, per-direction ratchets, consumed registration identifiers, sent records, accepted records, corruptions, snapshot disclosures, and event history.
Application messages will be bounded nonempty byte strings with public length leakage; allocation failure, out-of-memory behavior, and resource exhaustion outside the explicit bounds are operational availability concerns rather than cryptographic-game events.

An honest beacon is configured with exactly one pinned pair `(server Ed25519 public key, numeric server key ID)`.
An honest server may accept arbitrary correctly self-signed attacker-owned beacon registrations, because beaconcrypt registration is not an authorization mechanism.
Application task routing remains an explicit environmental premise: tasking for an honest beacon is not intentionally routed to an attacker-owned registered identity.
Positive agreement and non-reuse theorems also assume one authoritative honest state instance per identity and lineage; cloning an honest server or beacon state is an explicit fork handled by counterexample games or by the separate persistence refinement.

An optional caller-supplied server identity seed is an honest provisioned secret only when the game setup requires it to be unpredictable, correctly sized, and unique in the relevant identity population.
Reusing a seed, supplying a low-entropy seed, or disclosing it is not modeled as uniform honest key generation and must invalidate the corresponding freshness condition.

Each session handle will identify both parties, both identity public keys, the server identity key ID, the server-assigned beacon key ID, the exact parsed Phase-1 and Phase-2 public fields, the complete internal key-schedule transcript, the derived root, associated data, initial directional chains, the protected record and sequence that completes beacon registration, and the relevant commit events.
Numeric identifiers alone are not session identities.
The secret root-KDF input alone is not the matching conversation transcript.
All `u64` send, receive, server-ID, and assigned-ID counters will retain production's exact exhaustion and rejection behavior; the proof may derive that a configured query bound cannot reach exhaustion, but it may not replace checked non-wrapping transitions with modular arithmetic.

### Adversary interface

The active classical adversary will control delivery, loss, replay, reordering, duplication, modification, and synthesis of all public protocol messages.
The initial oracle set will include operations equivalent to:

- Create an honest server and obtain its public identity and numeric server identifier.
- Create an honest beacon pinned to a chosen honest server and obtain its public registration bundle.
- Create or submit arbitrary attacker-owned self-signed registration bundles.
- Deliver a Phase-1 bundle to a server and receive either failure or a public Phase-2 response.
- Deliver a Phase-2 response to an honest beacon and observe success or failure.
- Ask an established honest endpoint to encrypt a nonempty message.
- Deliver arbitrary frames to an established endpoint and observe public success or failure and any returned plaintext permitted by the game.
- Issue challenge, reveal, corruption, and snapshot queries allowed by the particular security game.

Oracle definitions MUST expose the real failure behavior and state changes.
In particular, an admitted future receive may advance the live chain and populate the cache before authentication, and an authentication failure retains that advanced state.

### Public leakage

The model will expose all production-public values, including identity public keys, Phase-1 and Phase-2 wire fields, server and assigned beacon numeric identifiers, registration failure or success, `CryptoFrame` sender ID, sequence number, protected-payload length, ciphertext core, base AEAD tag, outer CTX value, and message timing and ordering chosen by the adversary.

The serialized `CryptoFrame.keyId` is always the sender identifier.
Rust `Encrypted.key_id` is local return metadata naming the target and is not a serialized wire field.
In a registration response, the outer `KexResponse.keyId` publicly assigns the receiving beacon identifier, while the inner initial `CryptoFrame.keyId` identifies the server sender.
The outer assignment becomes authenticated to the beacon only because the same little-endian value is included in the successfully opened initial plaintext binding.

### Registration replay and commit events

The server replay identifier is the semantic concatenation of the decoded beacon Ed25519 identity public-key bytes and the decoded, signature-verified one-time X25519 public-key bytes; it does not include the signed buffer or signature bytes.
The server consumes that identifier after successful Phase-1 verification and key derivation, before the response is necessarily constructed or committed.
The game MUST preserve the resulting denial-of-service behavior when later response construction fails.

`ServerCommit` will be emitted only when the response has been encrypted and serialized and the successful high-level transition publishes its next counter and established peer state.
`BeaconCommit` will be emitted only after the beacon verifies the pinned server public key, derives the candidate ratchet, opens an admitted server-to-beacon record, checks the inner server sender ID, authenticates the little-endian assigned-ID prefix against the outer assignment, and publishes its established state.
Current production does not require that opened registration record to have sequence 1: from a fresh candidate receive ratchet it may authenticate an admissible future sequence within the 50-entry window, retaining skipped earlier receive keys.
The computational model MUST preserve this behavior unless decision D9 approves a production sequence-1 check.

The matching relation for agreement MUST include at least both identities, both numeric identifiers, the parsed Phase-1 fields, the Phase-2 key-establishment fields, the complete internal root transcript, derived root or equivalent session identifier, associated data, and direction assignment.
Under current admissible-sequence behavior, the protected payload and sequence that complete registration need only match a genuine server send in that committed session and need not equal the `appCipherText` originally serialized in the server's Phase-2 response.
If D9 adds a sequence-1 requirement, the stronger matching relation will require the exact original Phase-2 `appCipherText` and its sequence-1 send as well as the key-establishment fields.

### Reveal taxonomy and freshness

The model will not use a single ambiguous `Corrupt` oracle.
It will distinguish:

- `RevealRatchetCurrent(session, direction)`: live chain, counters, and cached receive material for one direction.
- `RevealEndpointCurrent(endpoint)`: all currently retained endpoint secrets, including every live session and cached key.
- `RevealLongTermIdentity(endpoint)`: signing and any static-DH secret material.
- `RevealRegistrationSecrets(beacon)`: current prekey, one-time, and ML-KEM secret material while those values still exist.
- `RevealPendingRegistration(handle)`: a caller-owned server `RegistrationOutput`, including the derived root and pending control token, plus any explicitly modeled live server ephemeral or KEM temporary if the game permits compromise inside an otherwise atomic oracle call.
- `RevealProvisionedSeed(endpoint)`: an application-supplied identity seed retained outside the endpoint.
- `RevealSnapshot(snapshot)`: the full plaintext serialized state represented by that snapshot or checkpoint export.
- `ForkOrRollback(lineage)`: an explicit violation used by negative persistence games rather than hidden inside an ordinary reveal.

Every positive theorem will define freshness from the exact reveal history and challenge time.
The theorem will state whether erasure is logical model erasure, current live-state absence, or a stronger deployment assumption.
Secret getters, copied values, update snapshots, complete checkpoints, debugging output, or caller-retained buffers count as secret retained state; they invalidate a particular erasure premise when they contain the challenged material or an ancestor chain from which it is derivable, or when they enable a forbidden fork or rollback.

### Partnering and test stages

The games will define partnering and test eligibility separately for four states:

- A server session after `ServerCommit` but before any evidence that the beacon received the response; this state may be eligible for a carefully defined secrecy test but not for mutual explicit authentication.
- A beacon session after `BeaconCommit`, which has authenticated the server through the successfully opened registration-completing protected record and has one unique matching prior server commit under the agreement theorem.
- A matching committed pair in the game history, even though the production server has not yet observed beacon key confirmation.
- A server session after accepting the first later authenticated beacon-to-server record, which is the first existing-protocol state eligible for server-side explicit key confirmation.

Attacker-owned peers are never challenge partners for an honest AKE or channel-initializer game.
Every challenge oracle will name which state it accepts and will reject sessions made stale by the exact reveal history; no baseline oracle returns a raw root or chain.

## Planned theorem suite

### CTX misattribution

Define `G_ctx_misattribution` so the adversary returns one fixed protected payload `C || T || U` and two semantically distinct explanations that both pass the production outer check and the same deterministic AEAD-open function.
The reduction will run that adversary, invoke the `DC-CTX-WITNESS` contract on a successful output, and return the two distinct 229-byte transcripts as a BLAKE2b collision.

The target theorem shape is:

```text
Adv_ctx_misattribution_beaconcrypt(A)
  <= Adv_collision_BLAKE2b512(B_A)
```

The theorem MUST contain no ChaCha20-Poly1305 term because the pointwise witness deliberately permits base-AEAD multi-openings.
It MUST account for the reduction's hash queries and construction overhead, although a machine-checked wall-clock cost theorem is required only if the feasibility phase confirms an appropriate SSProve cost model.

The existing F* transcript injectivity and collision-witness results MUST NOT be reproved for this baseline theorem.
A separate optional Coq/Rocq proof may be added later only as an explicitly labeled independent cross-check or to satisfy a single-kernel requirement.

### CTX record-security preservation

CTX binding and preservation of the base AEAD's privacy and integrity are separate claims.
Collision resistance suffices for the misattribution reduction, but it does not by itself show that publishing `BLAKE2b512(K || N || AD || T || seq || sender)` preserves either record secrecy or ordinary ciphertext integrity.
A contrived collision-resistant function could leak the record key, after which an adversary could both distinguish plaintexts and create ordinary valid forgeries without producing a two-opening collision.

The first record-security theorem MUST therefore either use a selected classical random-oracle, transformed-nAE, or precisely defined secret-input leakage assumption that covers both privacy and integrity preservation; use another explicitly defined standard-model assumption; or leave both preservation claims out of scope.
If a protocol redesign is selected, the theorem MUST target the changed production construction and the old construction's preservation claims must remain clearly conditional.

### Registration origin and agreement

The field-wise origin theorem will state that every accepted typed prekey, one-time-key, and PQ-key field verifies under the advertised signing identity and, under the signature assumption, originated in some signing action by that identity holder.
That weaker theorem does not require a one-bundle premise, but it does not prove that fields signed across multiple honest bundles belong to one coherent initiation.
A separate whole-bundle coherence or unique-initiation theorem requires the selected bundle-multiplicity rule from D6.
Neither theorem implies application authorization, liveness, possession of every advertised private key, or completed key agreement.

The main agreement theorem will bound the probability that an uncompromised honest beacon emits `BeaconCommit` without one unique matching earlier `ServerCommit`.
The converse will not be a theorem.
A negative control MUST exhibit a trace in which a server commits and the adversary drops the response, leaving the beacon uncommitted.
If current admissible-sequence behavior is preserved, this theorem matches the key-establishment session fields and separately requires the registration-completing protected payload to have a genuine prior server-send event in that session; it does not claim byte-for-byte agreement with the originally serialized Phase-2 response.
If D9 adds a sequence-1 check, the theorem may use the stronger exact-response matching relation.

Beacon-side agreement is authenticated by successful opening of a server record under the candidate registration channel, not by a server signature.
Its reduction MUST compose authenticated root derivation with that record's AEAD integrity and the selected CTX integrity-preservation assumption; BLAKE2b collision resistance alone handles only the separate same-payload misattribution branch and is insufficient if the published hash leaks the record key.

Server-side explicit beacon key confirmation will be a separate property tied either to the first successfully accepted later beacon-to-server record or to a chosen protocol change.

### Registration channel-initializer pseudorandomness

Define a hidden channel-initializer hybrid for server-committed unconfirmed sessions, beacon-committed sessions, and matching committed pairs wherever each notion is meaningful.
The hybrid replaces the real root and initial chains with uniform values and uses the selected world consistently for the initial protected response and all later records; it does not return a raw root or chain to the adversary.
A conventional exported-session-key `Test` is not the baseline because beaconcrypt exports no such key and a returned real root or chain could be checked against the public initial ciphertext unless a new domain-separated export key or an equally precise restriction were introduced.
The game will preserve arbitrary attacker-owned registrations, concurrent honest sessions, registration replay attempts, response loss, and all public session metadata.

The proof will expand the four DH values, ML-KEM shared secret, exact padded root transcript, root HKDF, initial two-chain expansion, and role assignment rather than assuming a secure composite `PQXDH` oracle.
The final bound will name the exact signature, related-key or separated-key, DH, ML-KEM, root-HKDF, randomness, and collision terms used by the hops.

### Established-session record confidentiality

Before composing with registration, prove an established-session theorem for a pair initialized with fresh matching directional chains.
The left/right challenge will require nonempty equal-length messages and will reveal the sender identifier, sequence number, length, complete protected payload, and all other production-public metadata.
The adversary may interleave sends, invalid and valid deliveries, out-of-order frames, replays, and activity for other peers and sessions.

The decryption restrictions around the challenge frame MUST be stated in the game rather than left implicit.
The theorem will include the ratchet key-evolution assumption, the exact active nonce-based AEAD notion needed by the chosen decryption interface—normally privacy plus integrity or one explicit combined nAE/CCA-style game—the selected CTX privacy-preservation assumption, and explicit chain/input/output collision events.
Associated data repeats when the same identity pair establishes more than one session, so cross-session and direction separation are computational consequences of distinct authenticated roots and chains plus collision bounds, not deterministic consequences of associated data alone.

### Established-session record authenticity and attribution

Define an injective acceptance game in which the adversary wins if an honest receiver accepts a semantic parsed frame without one unique matching honest send of the exact protected payload `C || T || U`, semantic frame fields, peer, session, direction, sequence, sender identity, associated-data context, and plaintext.
This is semantic parsed-frame authenticity, not uniqueness of a Cap'n Proto byte serialization.
Separate ordinary ciphertext forgery from same-payload multi-explanation or context-misattribution events so the final bound applies AEAD integrity, the selected CTX integrity-preservation assumption, and CTX collision resistance to the right cases.

The theorem MUST cover replay, peer separation, session separation, direction separation, and the exact failure-retains-state behavior.
Successful acceptance consumes the selected receive record; a second delivery of the same accepted frame must fail in the same authoritative lineage.

### Ratchet non-reuse

Prove that two distinct successful send allocations or AEAD-seal invocations within the theorem's authoritative lineage do not repeat the complete `(message key, nonce)` pair except on an explicit probabilistic collision event.
The quantified allocations include attempts whose seal callback, response construction, frame serialization, publication, or return later fails, because the ratchet advances and consumes send material independently of eventual publication.
The proof need not claim global nonce uniqueness when the property required by ChaCha20-Poly1305 is pair uniqueness under the relevant key.

The probabilistic bad-event ledger MUST cover initial-root collisions, live-chain input collisions, output collisions, direction or session collisions, and random-identifier collisions where relevant.
`SingleAuthoritativeLineage` and `NoForkOrRollback` are explicit structural theorem premises, not probabilistic cryptographic bad events.
Fork and rollback yield deterministic attacks when allowed and belong in counterexample games unless a deployment model separately supplies and justifies a failure probability.
Under an ideal 256-bit chain treatment, the chain-input collision term is expected to dominate the wider key-and-nonce collision term, but the repository MUST report only the exact bound produced by the chosen games.

### Forward secrecy and expected compromise attacks

Prove a ratchet-current-state forward-secrecy game for records whose send or receive material has been successfully consumed and is absent from all modeled live ratchet state before the reveal.
The theorem MUST distinguish sender-side consumed material, receiver-side consumed material, cached skipped receive material, and live future chain state.
This first capstone permits only the specified later ratchet-current reveal and excludes later long-term identity, provisioned-seed, registration-secret, and pending-registration-output reveals.
Allowing those later reveals requires a separate registration/AKE forward-secrecy and erasure theorem before end-to-end composition.

Add executable negative games that demonstrate:

- A current receive-state reveal exposes every retained skipped key.
- A live-chain reveal compromises future records because the symmetric ratchet has no post-compromise recovery input.
- Retaining an earlier snapshot defeats the corresponding erasure premise.
- Forking or rolling back the same state can repeat canonical ratchet material.

Negative games are required regression artifacts, not prose-only caveats.

### Persistence refinement

The primary cryptographic theorem will assume one affine volatile owner, no retained or revealed relevant ancestor snapshot, and no fork or rollback.
Persistence, if included, will be a separate conditional refinement through an ideal store package with linearizable durable compare-and-swap, current-head integrity and provenance, rollback resistance, one current lineage, and loser fencing.

The theorem will explicitly exclude the C, Go, and Python checkpoint helpers from the strong store premise because importing the same checkpoint more than once can fork state and importing an old checkpoint can roll it back.
All full snapshots and inert per-peer ratchet snapshots remain secret state even when they cannot directly create a second Rust `RatchetManager`.
A current post-consumption snapshot protected by a conforming store does not by itself reveal an old record key, while a disclosed or retained pre-consumption snapshot containing an ancestor chain does defeat the corresponding erasure premise.

### End-to-end composition

Only after registration and established-session record theorems are complete will the development replace the ideal established-channel initializer with the real registration package.
The initial capstone will have a symbolic shape such as:

```text
Adv_record_beaconcrypt(A)
  <= c_sig * Adv_signature
   + c_joint_id * Adv_joint_identity
   + c_dh * Adv_dh
   + c_kem * Adv_mlkem
   + c_root * Adv_root_hkdf
   + c_ratchet * Adv_ratchet_kdf
   + c_aead_priv * Adv_aead_privacy
   + c_aead_auth * Adv_aead_integrity
   + c_ctx_priv * Adv_ctx_privacy_preservation
   + c_ctx_int * Adv_ctx_integrity_preservation
   + c_ctx_bind * Adv_blake2b_collision
   + Pr[BadRoots or BadChains or BadOutputs]
```

This formula is a planning schema, not a claimed bound.
It is conditional on explicit `SingleAuthoritativeLineage` and `NoForkOrRollback` premises rather than assigning those structural violations a cryptographic probability.
The checked proof MUST produce the actual coefficients, oracle-query relationships, freshness predicate, and bad-event definitions, and it SHOULD split privacy, authenticity, agreement, and forward secrecy into separate readable capstones instead of publishing one opaque sum.

## Primitive package interfaces and assumptions

Primitive packages will expose only the operations used by beaconcrypt and the oracles required by the selected assumption games.
They will not embed the desired beaconcrypt theorem as a primitive assumption.

| Primitive or boundary | Real interface to model | Required proof treatment |
| --- | --- | --- |
| Randomness and provisioned seeds | Identity generation, optional caller-supplied server identity seeds, beacon X25519 prekey and one-time keys, beacon ML-KEM keypair generation, server ephemeral X25519 keys, ML-KEM encapsulation coins, and any game coins. | Independent fresh or otherwise explicitly distributed sampling, failure behavior, and collision events; call-site labels are proof bookkeeping rather than a claim that production RNG calls are cryptographically domain-separated, and provisioned seeds require explicit unpredictability, uniqueness, reuse, and reveal premises rather than being treated as fresh RNG output. |
| Ed25519 | Key generation, signing, and verification of the current Phase-1 fields. | Multi-user EUF-CMA or the exact stronger notion required by bundle handling; implementation correctness remains trusted. |
| Ed25519-to-X25519 conversion | Conversion of the same identity material used for signatures into static DH material. | Blocking decision between distinct production keys and a bespoke joint/related-key assumption; independent signature and DH games are not silently composable for the current correlation. |
| X25519 | Public-key derivation, four role-ordered DH computations, arbitrary attacker-supplied 32-byte public strings, libsodium's exact all-zero-output failure behavior, and any accepted aliases or noncanonical encodings. | Correctness plus the exact computational DH-style assumptions required by the active AKE hops; do not replace the production byte interface with an ideal prime-order-group API that silently excludes accepted or rejected production inputs. |
| ML-KEM-768 | Key generation, encapsulation, decapsulation, public key, ciphertext, and shared secret. | Correctness and the chosen multi-user IND-CCA or other precisely justified KEM notion. |
| Joint HKDF-SHA-512 | The same `Extract(None, input)` and variable-info/variable-length `Expand` implementation handles the 192-byte hybrid root transcript with `PQXDH_INFO` and 32-byte root or chain inputs with `SYM_RATCHET_INFO`, returning 32, 64, or 76 bytes as requested. | Use one joint variable-input, variable-info, prefix-consistent package unless a proved domain-separation hop justifies replacements; include a hybrid-combiner/extractor game robust to adversarially chosen or correlated other root components, plus key evolution, revealed-next-chain, backtracking, and chain-input-collision reasoning. |
| ChaCha20-Poly1305-IETF | Seal and open with the exact key, nonce, associated data, and transmitted base tag. | Nonce-based privacy and ciphertext integrity under the proven key/nonce discipline; key commitment is not assumed. |
| BLAKE2b-512 | Unkeyed 229-byte-to-64-byte CTX operation. | Collision resistance for binding and a separately chosen transformed-AEAD, RO, or secret-input assumption for both privacy and ordinary integrity preservation. |
| Cap'n Proto and adapter parsing | Phase-1, Phase-2, and `CryptoFrame` field parsing and serialization. | Deterministic refinement contracts and tests, or new production-used pure core helpers; not a cryptographic assumption. |
| Snapshot store | Load and compare-and-swap over a protected current lineage. | Optional ideal package and separately reviewed production refinement; no cryptographic protection is provided by snapshot bytes themselves. |

Primitive advantage notation, oracle restrictions, multi-user lifting, query counts, and reduction loss MUST be centralized in one SSProve interface module so individual protocol proofs cannot quietly use inconsistent notions.

## Proposed repository layout

The implementation should add the following structure, subject to the exact module naming required by the pinned hax and Coq/Rocq versions:

```text
crates/protocol-core/proofs/ssprove/
  dune-project
  dune
  README.md
  check-assumptions.sh
  assumptions.allow
  extraction/
    ... hax-generated .v files; never hand-edited ...
  theories/
    Contracts.v
    ProtocolTypes.v
    PrimitiveInterfaces.v
    PackageState.v
    ExtractionBridge.v
    RealExtracted.v
    RealSpec.v
    CtxGame.v
    RatchetGame.v
    RecordGame.v
    RegistrationGame.v
    CompromiseGame.v
    PersistenceGame.v
    Composition.v
    Results.v
    NegativeControls.v
    AssumptionAudit.v
```

Use Dune's `coq.theory` support if the pinned hax/SSProve stack passes the feasibility build, because hax's own SSProve proof library uses that layout and Dune can place `.vo`, `.glob`, and `_build` output under repository `target/formal-verification/ssprove`.
`_CoqProject` plus `coq_makefile` remains the fallback if the pinned toolchain cannot provide a reproducible Dune build.

File responsibilities will be:

- `Contracts.v`: parameterized deterministic contracts reused from F*, with no global axioms and no embedded protocol-security conclusion.
- `ProtocolTypes.v`: game-level identifiers, normalized wire values, events, freshness data, and finite query-bound parameters.
- `PrimitiveInterfaces.v`: real and ideal primitive packages and definitions of primitive advantages.
- `PackageState.v`: reusable finite maps, event logs, bad-event flags, and reveal histories.
- `RealExtracted.v`: narrow wrappers around generated hax code with no alternate transition semantics.
- `RealSpec.v`: game-oriented real packages and equivalences to `RealExtracted` or named contract dependencies.
- `CtxGame.v`: generic pointwise-to-probabilistic CTX reduction and the separately scoped confidentiality game.
- `RatchetGame.v`: KDF hybrids, arbitrary schedules, cache behavior, non-reuse, and ratchet-current-state forward secrecy.
- `RecordGame.v`: established-session confidentiality, authenticity, replay, and separation.
- `RegistrationGame.v`: multi-user registration, malicious bundles, agreement, confirmation scope, and channel-initializer pseudorandomness.
- `CompromiseGame.v`: positive freshness results and expected exposure attacks.
- `PersistenceGame.v`: optional ideal-store refinement and fork/rollback counterexamples.
- `Composition.v`: replacement of ideal packages by real packages and exact accumulation of advantage terms.
- `Results.v`: small, stable capstone statements intended for `Print Assumptions` and documentation.
- `NegativeControls.v`: executable counterexamples and deliberately false stronger claims, kept separate from positive results.
- `AssumptionAudit.v` and `check-assumptions.sh`: `Print Assumptions` commands, exact output classification, and `coqchk` checks for every exported capstone.

The [`protocol-core` Makefile](../../beaconcrypt-core/Makefile) will gain narrowly scoped variables and targets such as `HAX_SSPROVE_ITEMS`, `extract-ssprove`, `check-ssprove-extraction`, `check-ssprove-policy`, `check-ssprove`, `verify-ssprove`, and `verify-ssprove-in-shell`.
The existing backend targets will remain independently runnable.
The initial extraction target should preserve the current backend-enabling Cargo feature and use hax 0.3.7's supported command shape: `cargo hax -C --locked --features=proverif ';' into -i '$(HAX_SSPROVE_ITEMS)' --output-dir proofs/ssprove/extraction ssprove`.
Renaming the currently backend-misnamed `proverif` feature is optional cleanup and SHOULD NOT be mixed into the feasibility change unless hax requires it.

`verify-in-shell` will regenerate and check all three proof backends after SSProve is accepted.
`check-generated` will compare all three generated directories and reject untracked generated artifacts.
CI will then run the generated/proof gate and the separate reviewed-inventory gate.

## Extraction coverage policy

Maintain an extraction-coverage table for every operation used by a real game.
Each row MUST use exactly one of these classifications:

- `direct extraction`: the SSProve real package executes hax-generated code from a named production-used Rust item.
- `F*-backed contract`: the game is parameterized by a deterministic predicate discharged by a named F* theorem over a named Rust item.
- `opaque primitive`: the package is deliberately abstract and contributes a named primitive advantage term.
- `handwritten orchestration`: the code manages sessions, adversary queries, event logs, and game state but does not replace a production transition.
- `adapter assumption`: the fact is outside `protocol-core` and is explicitly inventoried with tests or review evidence.

No real-game operation may remain unclassified.
The table MUST distinguish semantic wire fields from concrete Cap'n Proto bytes and MUST identify any production adapter that supplies a field to an extracted core helper.

## Implementation phases

### Phase 0: repair the baseline and freeze claims

#### Work

1. Review the seven stale inventory entries against their committed diffs and current trust-boundary descriptions.
2. Update only the justified inventory prose, structural checks, and hashes in a dedicated prerequisite change.
3. Move the existing F* cache and all planned SSProve compiled output out of the inventory-monitored `proofs/` tree and into repository `target/formal-verification/`.
4. Add a CI invocation of `make -C crates/protocol-core check-inventory` after the proof/generated gate, or add an explicitly named combined CI target while preserving the ability to inspect changed generated artifacts before refreshing hashes.
5. Write the exact games, events, reveal oracles, freshness predicates, public leakage, query-bound parameters, and theorem names in a maintained `doc/computational-security.md` reference document.
6. Resolve the decision gates required by Phase 1 through Phase 5, recording chosen assumptions and any approved protocol changes before modifying production.
7. Record the first extraction-coverage table and identify every adapter operation that is not currently in `protocol-core`.

#### Exit criteria

- `check-inventory`, `check-generated`, the current F* proofs, and the current ProVerif scenarios all pass on the unchanged proof baseline.
- Every proposed positive theorem has a precise success event and freshness predicate.
- Every known false converse or compromise property has a planned negative control.
- No document uses “secure PQXDH,” “forward secrecy,” “post-quantum,” or “end-to-end” without the corresponding scope and assumptions.
- All protocol-changing decisions needed by the next phase are explicit.

### Phase 1: lock and qualify the SSProve backend

#### Work

1. Pin a mutually compatible Coq/Rocq kernel, MathComp, SSProve, extructures, mathcomp-word/Jasmin, Equations, RecordUpdate, Hierarchy Builder, ConCert, and every other transitive proof library in `flake.nix` and `flake.lock`; do not rely on an ambient opam switch, `opam update`, a moving branch, or an unpinned system package.
2. Add the exact Coq/Rocq and SSProve identities to `check-toolchain`, including a commit or package version that uniquely identifies the reviewed source.
3. Reproduce the hax SSProve extraction probe with deny-all item selectors and a dedicated generated output directory.
4. Start with `build_commitment_transcript` and the smallest required fixed-array and integer definitions, then add one PQXDH transition and one concrete ratchet operation.
5. Compile every generated file in a clean build without repository-owned generated-file edits or post-generation rewriting, and run `coqchk` or the pinned kernel equivalent over the resulting beaconcrypt capstone dependency graph.
6. If hax output needs a backend fix, prefer an upstream change or a pinned reviewed hax revision; if a local patch is unavoidable, stop for approval and inventory the patch, exact affected constructs, and regeneration check.
7. Audit hax 0.3.7's bundled Hacspec/SSProve libraries before accepting them: the planning inspection found an `Axiom falso : False` used by unchecked `result_unwrap` code and exported transitively by the aggregate Hacspec library.
8. Prefer a pinned upstream fix or a minimal inventoried Nix source patch that removes or isolates the false axiom; no beaconcrypt capstone, generated operation, proof script, or transitive theorem dependency may use `Hacspec_Lib_Pre.falso`, `admit_falso`, `result_unwrap`, or an equivalent contradiction escape hatch.
9. Add extraction checks for unresolved placeholders and suspicious self-referential definitions; the planning PQXDH probe emitted constants equivalent to `RATCHET_CHAIN_SIZE := RATCHET_CHAIN_SIZE` and `SYM_RATCHET_INFO := SYM_RATCHET_INFO`, so patchless compilation and an exact resolution check are mandatory.
10. Treat generated Equations constructs such as `Fail Next Obligation.` according to their checked semantics rather than rejecting them textually as admissions, but require the complete generated module to compile and pass the assumption audit.
11. Add policy checks rejecting `Admitted`, `admit`, `Abort`, global `Axiom`, disabled guard checking, and other proof-bypass controls in repository-owned SSProve files.
12. Add `Print Assumptions` or the pinned equivalent for each pilot capstone and an exact allowlist for unavoidable, reviewed upstream foundations.
13. Add deterministic regeneration and untracked-file checks for the SSProve extraction directory.
14. Measure clean extraction and proof time and set per-target and CI timeouts from observed results rather than copying ProVerif's timeout.

#### Exit criteria

- One locked command enters the proof shell, regenerates the pilot, and checks it from a clean tree.
- The commitment, one PQXDH, and one ratchet generated module compile without hand edits.
- Re-running extraction produces no diff.
- Repository-owned SSProve sources contain no admissions or unaudited axioms.
- Assumption reports are stable and checked, and no checked result depends on the Hacspec false axiom or unchecked result unwrap.
- Generated PQXDH constants resolve to concrete imported or local definitions rather than self-reference.
- The measured cost is compatible with CI, or a reviewed job split preserves identical locked inputs and generated-diff checking.
- Failure to meet these conditions is a go/no-go gate; switching to EasyCrypt, maintaining a fork, or handwriting extracted semantics requires a new decision.

### Phase 2: implement the contract layer and CTX pilot

#### Work

1. Implement `Contracts.v`, the first coverage table, and trust-inventory entries for `DC-CTX-ENCODING` and `DC-CTX-WITNESS`.
2. Define the production protected-payload parser and explanation predicate over fixed fields.
3. Define the BLAKE2b collision game and the beaconcrypt misattribution game without assuming AEAD key commitment.
4. Implement the reduction adversary that converts any successful misattribution into the F*-contracted collision witness.
5. Prove the exact probability inequality and oracle-query relationship.
6. Add an SSProve negative control using an abstract deliberately multi-opening AEAD package in which removing the outer commitment check makes the attack succeed; retain the existing concrete Rust multi-opening fixture as separate integration evidence unless its byte-level bridge is explicitly assumed.
7. Keep the privacy- and integrity-preservation games in a separate module and mark them conditional until the CTX record-security assumption decision is resolved.
8. Update [`ctx-commitment.md`](../ctx-commitment.md) and [`formal-verification-analysis.md`](../formal-verification-analysis.md) only after the mechanized result exists, replacing the current prose-only probability lifting with an exact account of what SSProve checks.

#### Exit criteria

- The capstone has the form `Adv_misattribution <= Adv_collision` with no spurious AEAD advantage term.
- The transcript injectivity and pointwise collision witness are reused through explicit contracts and are not duplicated in Coq/Rocq.
- The theorem statement visibly quantifies over the reviewed contract, while the assumptions report and `coqchk` audit show that no hidden global axiom was used; an explicit theorem parameter need not appear as a global `Print Assumptions` entry.
- The with-CTX game is proved and the no-CTX negative control is executable and classified as expected.
- Documentation distinguishes the F* witness, SSProve probability lifting, cross-prover representation bridge, and production BLAKE2b assumption.

### Phase 3: implement faithful ratchet packages

#### Work

1. Resolve the initial-versus-step HKDF-label decision before defining primitive packages.
2. Implement one production-faithful joint variable-input, variable-info, variable-output HKDF interface for root and ratchet calls; if symmetric labels remain shared, calls on equal 32-byte inputs and the same label MUST have prefix-consistent 64-byte and 76-byte outputs.
3. Implement real and ideal key-evolution packages that expose message key, next chain, and nonce exactly as production partitions them.
4. Wrap the hax-extracted concrete ratchet operations and reuse `DC-RATCHET-REQUEST`, `DC-RATCHET-DIRECTIONS`, and `DC-RATCHET-STATE` for source-level transition facts.
5. Prove SSProve-native history invariants for arbitrary bounded adversarial schedules, including unique session/direction allocation positions and bad chain-input collisions.
6. Model receive planning and the exact capacity rules: forward gap at most 50 and existing cache length plus the gap at most 50.
7. Model pre-authentication advancement, retained failed targets, zero-derivation retry, successful whole-entry consumption, replay failure, and capacity release.
8. Prove `(key, nonce)` pair non-reuse for every successful allocation or seal invocation, including attempts that later fail, conditional on no input/output collision, `SingleAuthoritativeLineage`, and `NoForkOrRollback`.
9. Prove consumed-key ratchet-current-state forward secrecy under the selected key-evolution assumption and the explicitly restricted reveal set.
10. Add negative games for skipped-cache exposure, live-future exposure, and lack of post-compromise recovery.

#### Exit criteria

- The model does not treat initialization and later ratchet steps as independent random functions unless production has distinct labels.
- Every state transition used by an oracle is direct extraction or mapped to an F* contract.
- The arbitrary-schedule theorem has explicit session, send, delivery, failure, and reveal bounds.
- The exact 50-entry behavior and failure-retains-state semantics are covered by positive reachability tests and negative controls.
- The non-reuse theorem names all probabilistic collision events and states ownership, lineage, and rollback conditions as explicit premises.
- The compromise suite proves consumed-key secrecy only within its freshness predicate and demonstrates the expected cached and future-key attacks.

### Phase 4: prove established-session record security

This phase requires the D5 branch that supplies CTX privacy and integrity preservation or an approved construction redesign; the binding-only branch defers this phase's positive record-security capstones.

#### Work

1. Define established matching endpoints independently of registration so record composition can be reviewed in isolation.
2. Connect extracted ratchet outputs to the abstract ChaCha20-Poly1305 and BLAKE2b packages with the exact associated data, sequence, and sender identifier.
3. Implement equal-length nonempty left/right record privacy for both directions and multiple concurrent peers and sessions.
4. Implement injective semantic-frame authenticity with the exact protected payload and matching-send fields, separating ordinary transformed-AEAD forgery from CTX misattribution cases.
5. Permit arbitrary delivery order, forged future sequence numbers within the admission policy, repeated invalid targets, valid delayed frames, and replay.
6. Prove peer, session, direction, sender-ID, sequence, and associated-data separation.
7. Account for every KDF, AEAD, hash, and collision query in the reductions.
8. Add negative controls that omit CTX, collapse peer context, reuse a forked state, and reveal a cached challenge key.
9. Parameterize bounded message and frame lengths by `L_max`, preserve public length leakage, and model exact send/receive `u64` exhaustion and state-neutral rejection.

#### Exit criteria

- Privacy and authenticity are separate readable capstones with exact bounds, and both use the selected CTX preservation assumption while collision resistance is limited to binding and misattribution.
- Public metadata and decryption-oracle restrictions are stated in the games and documentation.
- Message spaces are finite under explicit public bounds, and allocation/OOM behavior is not misclassified as a cryptographic result.
- The theorem covers the real failed-active-receive schedule rather than an atomic ideal receive.
- Replay rejection follows successful consumption in one authoritative lineage.
- Expected attacks succeed when their protecting premise or component is removed.

### Phase 5: prove registration and AKE properties

#### Work

1. Resolve identity-key correlation, bundle multiplicity, adversary modality, CTX record-security preservation, registration-confirmation, and registration-response sequence decisions before finalizing the games.
2. Implement a multi-user, multi-session registration package with arbitrary attacker-owned self-signed beacons and replayed honest bundles.
3. Preserve the exact four DH roles, ML-KEM ciphertext and secret, padded root input, `PQXDH_INFO`, initial-chain expansion, and complementary direction assignment.
4. Model the exact adapter order: Phase-1 verification and freshness check; ephemeral, KEM, DH, core-acceptance, and root-HKDF work; replay-identifier consumption before returning caller-owned pending output; then later response-ratchet derivation, encryption, serialization, and peer/counter publication.
5. Model beacon verification of its pinned server public key and numeric ID, the registration-completing frame's sender ID and admitted sequence, and the authenticated assigned-ID prefix.
6. Prove field-wise Phase-1 signature origin independently of bundle multiplicity, then prove whole-bundle coherence or unique initiation only under the selected single-bundle or whole-bundle authentication rule.
7. Prove `BeaconCommit` implies one unique matching earlier `ServerCommit` by composing root authentication with registration-completing record integrity and CTX integrity preservation, then add the dropped-response counterexample to the converse.
8. Prove the hidden channel-initializer replacement theorem for fresh eligible sessions with the exact primitive reductions rather than a composite PQXDH assumption or an exported raw-session-key test.
9. State server-side key confirmation only at the first accepted later beacon record unless the protocol has gained an explicit confirmation message.
10. Preserve reachability of malicious registration and attacker recovery of data intentionally routed to that malicious identity while proving separation from honest sessions.
11. Model arbitrary attacker-supplied X25519 byte strings, aliases or noncanonical encodings accepted by the pinned production parser, and exact all-zero-output rejection rather than restricting the real game to ideal group elements.
12. Track caller-owned `RegistrationOutput`, provisioned identity seeds, and registration temporaries through their exact production lifetimes and freshness rules.
13. Model exact server and assigned-ID `u64` exhaustion, occupied-ID rejection, and state neutrality rather than assuming an unbounded identifier space.
14. Add a D9 branch regression: current behavior must reach a beacon commit through an admissible later same-session record with the assigned-ID prefix, while a sequence-1 production change must reject the same substitution.

#### Exit criteria

- Independent Ed25519 and X25519 security assumptions are used only if production keys are independent; otherwise the theorem names the approved joint assumption.
- Field-wise origin remains separate from whole-bundle coherence, and cross-bundle splicing is excluded from the stronger theorem by an enforced invariant or prevented by a production authentication change.
- The agreement direction and matching fields reflect actual commit ordering.
- The model either preserves the current admissible registration-record sequence behavior or targets an approved production check requiring sequence 1.
- The proof does not call self-signature acceptance authorization or liveness.
- The channel-initializer bound contains explicit primitive advantages, coefficients, query mappings, and bad events and never exposes a raw root or initial chain.
- Root-HKDF hybrids tolerate the other transcript components being adversarially chosen or correlated, and the real X25519 interface matches production byte acceptance and rejection.
- The malicious-registration and dropped-response traces remain reachable as intended.

### Phase 6: compose registration and records

This phase is part of the full record/AKE milestone and is deferred by the D5 binding-only branch.

#### Work

1. Replace the ideal established-session initializer in `RecordGame.v` with the real registration package one interface at a time.
2. Prove an exact post-registration state bridge rather than resetting to two fresh chains: under a sequence-1 production check, the server-to-beacon direction has allocated, opened, and consumed sequence 1 while beacon-to-server remains at 0; under current production, the bridge tracks the actual admitted completing sequence, all prior server allocations, retained skipped receive keys, any later server advancement, the optional caller-supplied initial plaintext, and every already exposed protected record.
3. Lift record privacy, authenticity, attribution, replay, and separation to fresh registered sessions.
4. Integrate CTX binding, privacy preservation, and integrity preservation without conflating their assumptions.
5. Produce separate capstones for privacy, authenticity, beacon-side agreement, server confirmation after a later record, non-reuse, and ratchet-current-state forward secrecy; exclude long-term, provisioned-seed, registration-secret, and pending-output reveals unless a separate AKE forward-secrecy theorem has been added.
6. Generate the exact final coefficients and query bounds from the composed reductions.

#### Exit criteria

- Every ideal package replacement has a local theorem and no unexplained whole-protocol hop remains.
- Every final SSProve premise appears in the contract ledger or primitive interface table.
- All final events carry enough data to exclude cross-peer, cross-session, cross-direction, and identifier-confusion matches.
- `Results.v` contains small stable statements suitable for assumption reporting and documentation.
- No theorem is labeled end-to-end while it depends on an unmapped adapter fact.

### Phase 7: add compromise and persistence refinement

#### Work

1. Add adaptive reveal histories to the composed games and freeze exact freshness predicates for each capstone, keeping the baseline past-record theorem limited to later ratchet-current reveals.
2. Prove the volatile affine-owner theorem first, without persistence.
3. Add an ideal `SnapshotStore` package only if the persistence decision keeps it in the first suite.
4. Relate canonical restore to `DC-RESTORE` and state the external integrity, provenance, durability, rollback-resistance, and one-lineage premises.
5. Prove the ideal-store conditional theorem and record correspondence of the actual Rust `PersistentServer<S>` usage discipline as an inventoried adapter/deployment obligation plus tests; a proof-assistant-checked adapter refinement requires first moving and production-using an extractable pure transition.
6. Add explicit attacks for retained snapshots, duplicate restoration, rollback, failed CAS without fencing, and binding checkpoint imports.
7. Audit every public secret getter, provisioned identity seed, caller-owned `RegistrationOutput`, and snapshot-producing API and classify its output and deletion timing in the reveal taxonomy.

#### Exit criteria

- Current-state forward secrecy never relies on Rust `Drop` as a physical erasure theorem.
- No end-to-end result permits later long-term or registration-secret compromise without a separately proved AKE forward-secrecy theorem.
- Snapshot bytes and caller-retained copies are treated as secret state.
- The strong persistence result is conditional on the exact `SnapshotStore` contract and excludes weaker binding helpers.
- Fork and rollback attacks are checked and documented.
- No post-compromise-security claim is present.

### Phase 8: production correspondence, CI, and documentation

#### Work

1. Finish the extraction-coverage table and adapter refinement ledger for every real-game operation.
2. Add Rust integration tests for every new production-used core helper, including success, authentication failure, replay, malformed input, and state rollback where relevant.
3. Extend `check-toolchain`, proof policy checks, assumption reports, generated drift checks, and the trust-boundary checker to cover SSProve and every handwritten or generated file.
4. Update the GitHub Actions proof job to run all proof backends, generated-diff checks, assumption checks, negative controls, and the standalone inventory check within reviewed timeouts.
5. Update [`formal-verification-analysis.md`](../formal-verification-analysis.md) with a plain-English explanation of every new result, exact limitations, cross-prover contracts, advantage terms, and expected attacks.
6. Update [`formal-verification.md`](../formal-verification.md), [`protocol.md`](../protocol.md), [`threat_model.md`](../threat_model.md), [`ctx-commitment.md`](../ctx-commitment.md), and [`persistence.md`](../persistence.md) only where completed theorems or approved protocol changes require it.
7. Update [`trusted-boundary.md`](../../beaconcrypt-core/proofs/trusted-boundary.md), structural counts, and `reviewed-inventory.txt` only after all generated and handwritten diffs have been reviewed.
8. Add `doc/impl/computational-security-proof-completion.md` as an implementation record that lists theorem names, final bounds, commands, decisions, negative controls, and residual trust.

#### Exit criteria

- A clean locked run regenerates and checks F*, ProVerif, and SSProve artifacts.
- Generated output is deterministic and never hand-edited.
- Every repository-owned capstone has an allowlisted assumption report and no admission escape hatch.
- The standalone inventory passes and CI invokes it.
- The maintained plain-English analysis matches the checked theorem statements and does not overstate cross-prover or production correspondence.
- All protocol, wire, persistence, KAT, binding, and API changes are explicitly called out in the completion record and pull request.

## Planned validation commands

The exact command names may be adjusted during Phase 1, but the final interface should support at least:

```sh
make -C crates/protocol-core verify-ssprove
make -C crates/protocol-core verify
make -C crates/protocol-core check-generated
make -C crates/protocol-core check-inventory
```

Inside the locked shell, maintain independently runnable targets equivalent to:

```sh
make -C crates/protocol-core check-toolchain
make -C crates/protocol-core extract-ssprove
make -C crates/protocol-core check-ssprove-extraction
make -C crates/protocol-core check-ssprove-policy
make -C crates/protocol-core check-ssprove
```

When production-used Rust changes, also run:

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test
cargo check --no-default-features --features pqxdh,beacon --lib
cargo check --no-default-features --features pqxdh,server --lib
```

Every phase MUST inspect generated diffs before updating inventory hashes.
Every negative control MUST have an expected-result classifier that rejects missing, inconclusive, timed-out, or accidentally reversed results.

## Pull-request sequence

Keep the work reviewable and avoid mixing proof infrastructure, protocol changes, and theorem claims in one patch.
The recommended sequence is:

1. Repair the pre-existing inventory baseline and add its explicit CI invocation.
2. Land the claim specification, decision record, and extraction-coverage skeleton without new security claims.
3. Pin and qualify the SSProve/Coq/Rocq toolchain with a minimal compiled extraction pilot.
4. Land the cross-prover contract framework and CTX probability reduction.
5. Land faithful ratchet packages, non-reuse, failed-receive behavior, and compromise negative controls.
6. Land established-session record privacy and authenticity.
7. Land registration/AKE packages and one-way agreement.
8. Land end-to-end composition and exact final bounds.
9. Land optional persistence refinement, final CI hardening, maintained documentation, and the completion record.

Any approved protocol change, such as new identity keys, KDF labels, or bundle authentication, SHOULD be its own earlier pull request with wire/KAT/persistence/binding compatibility tests and regenerated proof baselines before proofs target the new protocol.

## Risks and fallback rules

| Risk | Required response |
| --- | --- |
| Hax emits SSProve syntax but the selected generated modules do not compile. | Minimize the selector, file an upstream issue or patch hax at a pinned revision, and stop before maintaining handwritten generated-code translations. |
| Generated code requires repeated local rewriting. | Treat this as a backend failure unless an explicit decision accepts and inventories a narrow deterministic postprocessor. |
| SSProve lacks a usable native runtime cost model. | Mechanize probability, exact oracle calls, and query multiplicities; document and review computational overhead separately rather than claiming a checked runtime theorem. |
| A deterministic F* theorem does not match the SSProve representation. | Strengthen the contract and representation ledger or add a production-used core normalization helper; do not assume the mismatch away. |
| The desired AKE theorem needs independent signature and DH keys. | Stop at the identity-key decision instead of composing inapplicable independent assumptions. |
| CTX privacy or ordinary-integrity preservation cannot be justified under the selected standard assumptions. | Use the explicitly reduced binding-only milestone or obtain approval for a classical RO, appropriately quantum model, precise transformed-AEAD assumption, or construction change; do not keep the dependent record/AKE capstones. |
| Proof time exceeds CI limits. | Profile modules, split independently checkable jobs under the same lock, and preserve at least one aggregate required status; do not weaken proofs or time out silently. |
| Final coefficients are unexpectedly large. | Report the checked bound, identify the responsible hops, and optimize the game sequence in a follow-up; do not replace it with an informal tighter number. |
| Persistence cannot be related to the real store API without assuming deployment behavior. | Keep the volatile theorem primary and label persistence as a conditional refinement with exact external premises. |

## Decisions requiring approval

The following choices materially change either production or the theorem and cannot be made implicitly during implementation.

### D1: assurance boundary

Choose between:

- Parameterized cross-prover composition, where F* discharges deterministic contracts and SSProve proves the computational reductions; this is the recommended baseline and avoids duplicate CTX and state-machine proofs.
- A closed Coq/Rocq theorem, which requires reproving the deterministic facts in Coq/Rocq or approving a separately justified proof bridge.

This decision blocks the contract architecture in Phase 2.

### D2: computational adversary scope

Choose between:

- Classical active security first, with an optional separately named passive harvest-now-decrypt-later analysis; this is the recommended achievable scope for SSProve and the current hybrid protocol.
- A quantum computational model, which requires different tooling and cannot yield active quantum security while Ed25519 and X25519 remain in the protocol.

This decision blocks primitive notions and CTX privacy/integrity-preservation modeling.

### D3: correlated signing and static-DH identities

Current production converts the same Ed25519 identity keys to X25519 while also using them for signatures.
Choose between:

- Add distinct signed and pinned static X25519 identity keys, accepting the protocol, wire, KAT, persistence, and compatibility changes; this gives a cleaner modular reduction under standard independent assumptions.
- Preserve the current protocol and state an explicit joint/related-key security assumption for Ed25519 signing plus Ed25519-to-X25519 conversion and DH.

This decision blocks the registration/AKE theorem.
For a theorem under conventional modular assumptions, the recommended choice is distinct signing and static-DH keys; preserving the current wire is viable only if the bespoke joint assumption is accepted as residual trust.

### D4: initial and step ratchet HKDF domains

Current production uses the same `SYM_RATCHET_INFO` and 32-byte input form for the 64-byte initial expansion and 76-byte ratchet expansion.
HKDF expansion is prefix-consistent, so the two calls cannot be modeled as independent random functions when their inputs coincide.
Regardless of this choice, root derivation and symmetric derivation use the same HKDF-SHA-512 implementation and remain in one joint primitive package unless a separate game hop proves that their input-length and info domains may be replaced independently.
Choose between:

- Give initialization and later steps distinct labels, accepting a protocol/KAT compatibility change and a simpler domain-separated proof.
- Preserve production and use one variable-output prefix-consistent HKDF package plus an explicit root/live-chain input-collision bad event.

This decision blocks the ratchet primitive package.
Distinct labels are recommended if protocol/KAT compatibility can change; otherwise the prefix-consistent joint model is mandatory rather than a proof shortcut.

### D5: CTX record-security preservation model

Choose between:

- A classical random-oracle, transformed-nAE, or precisely defined secret-input-hash assumption for the first privacy and integrity preservation theorems.
- A standard-model protocol redesign supporting the desired record privacy and integrity claims.
- Binding only, leaving both CTX privacy and ordinary-integrity preservation outside the first proof suite.

Collision resistance remains sufficient for the separate binding theorem in every branch.
The binding-only branch is a deliberately reduced milestone: it completes CTX misattribution and any independent ratchet results, but defers established-record privacy, ordinary record authenticity, registration-completing-record integrity, `BeaconCommit` agreement, channel-initializer pseudorandomness after the public response, and all full composition capstones.
Choosing that branch requires updating the objective and completion record so deferred claims are not treated as failed acceptance criteria.
For the full record/AKE objective, the recommended first target is a precisely stated classical RO or transformed-nAE preservation theorem, with binding remaining a separate collision-resistance result.

### D6: Phase-1 bundle multiplicity

Current Phase 1 signs the advertised prekey, one-time key, and PQ key separately under the same self-signed beacon identity.
Those signatures support field-wise origin under EUF-CMA, but they do not by themselves make fields from multiple honest bundles one coherent initiation.
Choose between:

- Enforce and prove one honest bundle per fresh identity for the lifetime covered by the theorem.
- Add one signature over a canonical whole-bundle encoding, or include the same fresh bundle identifier plus domain and field role in every signed message and require all bundle identifiers to match before allowing multiple honest bundles per identity.

This decision blocks the whole-bundle coherence or unique-initiation theorem, but not the weaker field-wise origin theorem.
A canonical whole-bundle signature is recommended if multiple bundles per identity are a supported use case; otherwise enforce the one-bundle invariant in production and in the theorem.

### D7: registration key confirmation

Choose between:

- Prove the actual one-way property at registration and treat the first accepted beacon-to-server record as server-side key confirmation; this requires no protocol change.
- Add an explicit beacon confirmation flight and prove mutual explicit AKE at registration.

This decision blocks the final authentication claim but not the one-way agreement proof.
The recommended first theorem keeps the protocol unchanged, proves the actual one-way registration property, and uses the first accepted beacon record for server-side confirmation.

### D8: compromise and persistence scope

Choose which reveal oracles and persistence theorem belong in the first suite.
The recommended first milestone covers volatile one-owner state, current ratchet reveals, cached-key exposure, and no-PCS negative results, while deferring the ideal-store refinement until the record and AKE capstones are stable.
Later long-term, provisioned-seed, registration-secret, or pending-output reveals require a separate AKE forward-secrecy theorem and are excluded from the recommended first milestone.

This decision blocks Phase 7 only.

### D9: registration-completing record sequence

Current `Beacon::finish_registration` does not check that the successfully opened `CryptoFrame.seq` is 1.
From a fresh candidate receive ratchet it may admit an authenticated server-to-beacon record at a future sequence up to the 50-entry window, and a later same-session record whose plaintext begins with the assigned-ID binding can therefore complete registration while skipped earlier receive keys remain cached.
Choose between:

- Add and test a production requirement that the registration-completing frame has sequence 1, accepting the resulting behavior change and simpler post-registration state bridge.
- Preserve current production and prove agreement and record composition for any admissible completing sequence, including retained skipped keys and already exposed prior or later server records.

This decision blocks the final registration and post-registration composition games.
A production sequence-1 requirement is recommended because it matches the response constructor's intent, prevents a later same-session application record from completing registration, and yields one canonical post-registration state.

## Completion criteria

The computational-proof effort is complete only when all of the following hold:

These are the full record/AKE milestone criteria; if D5 selects binding only, the resulting reduced milestone is complete only for CTX binding and independent ratchet work and MUST record the remaining record, agreement, and composition criteria as explicitly deferred rather than satisfied.

- The chosen security games, primitive notions, reveal rules, freshness predicates, and public leakage are frozen in maintained documentation.
- SSProve, Coq/Rocq, and all dependencies are locked, version-checked, reproducible, and usable without ambient packages.
- Hax-generated SSProve artifacts compile without hand edits and regenerate deterministically.
- The extraction-coverage table classifies every real-game operation.
- Every reused F* fact appears as an explicit parameterized contract with an exact discharge and representation mapping.
- CTX misattribution has a checked probability reduction with no unnecessary AEAD term.
- Record privacy and authenticity cover arbitrary bounded concurrent schedules, exact failed-receive retention, cache capacity 50, replay, separation, and the selected CTX privacy and integrity preservation model.
- Registration results reflect malicious self-signed beacons, replay consumption, exact adapter commit order, pinned-server verification, the actual or deliberately changed registration-completing sequence rule, and one-way key confirmation.
- The final bounds contain exact coefficients, query counts, bad events, and primitive advantages rather than a prose-only composition.
- Ratchet-current-state forward secrecy and send-allocation non-reuse state their ownership, erasure, reveal, pending-output, provisioned-seed, and persistence premises, and the expected cached-key, future-key, ancestor-snapshot, fork, and rollback attacks are checked.
- Repository-owned proof files contain no admissions, hidden axioms, disabled checks, or unclassified assumptions.
- F*, ProVerif, SSProve, generated drift, assumption reports, negative controls, and the standalone inventory all pass in CI.
- [`formal-verification-analysis.md`](../formal-verification-analysis.md) gives a plain-English account of every new theorem and limitation.
- A completion record under `doc/impl` lists the exact commands, theorem names, final bounds, decisions, changed protocol surfaces, and remaining trusted boundary.
