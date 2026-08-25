<!-- SPDX-License-Identifier: 0BSD -->

# Computational security proof integration evaluation

Status on 2026-08-25: the ProVerif suite now names and checks the four required attacker scenarios, the active-quantum scenario produces the expected attack witness, and the SSProve work establishes the first CTX event-inclusion milestone. A complete computational proof of the beaconcrypt handshake, ratchet, and record protocol is not yet present and must not be inferred from these results.

## Decision and separation of concerns

The computational proof must reason about protocol security games, adversarial advantage, reductions, and composition assumptions. It assumes that the Rust operations supplied to those games implement their stated deterministic contracts. Lean and F* own implementation correctness, extraction refinement, fixed-size layouts, and state-machine correctness; a temporary Lean or F* failure caused by implementation/extraction reorganization is therefore not a computational-model counterexample and is not repaired as part of this work.

This separation does not permit an undocumented implementation assumption. Every deterministic fact consumed by a computational theorem must be a named contract with a representation bridge to a named Lean or F* result. The computational proof remains conditional when that bridge has not been reviewed against the current extraction snapshot.

The integration has three deliberately different evidence layers:

- ProVerif checks symbolic reachability, secrecy, and correspondence under ideal constructor and destructor equations.
- SSProve checks probabilistic event and game reasoning under explicit primitive and deterministic contracts.
- Lean and F* discharge deterministic contracts about the extracted implementation without being asked to prove cryptographic primitive security.

No result in one layer should be relabeled as a result from another layer.

## Four-scenario ProVerif matrix

The four named scenarios reuse the same hax-derived PQXDH types and builders and distinguish network control from classical-key recovery. The active and passive labels describe the network adversary; the classical and quantum labels describe the symbolic capabilities made available to that adversary.

| Scenario | Network power | Cryptographic capability | Checked result | Exact interpretation |
| --- | --- | --- | --- | --- |
| Active classical | Full Dolev-Yao interception, injection, deletion, replay, reordering, and attacker-owned self-signed registrations. | Ideal Ed25519, X25519, ML-KEM, HKDF, ratchet, AEAD, and CTX equations with no secret-key recovery. | All five secrecy queries and all six injective correspondence queries are true, and the seven-query active reachability control finds its required witnesses. | The bounded per-session trace preserves the selected task and record canaries and the listed origin, replay-consumption, response-abort, beacon-commit, and record-origin correspondences in the symbolic model. |
| Passive classical | Transcript observation without network modification or injection over one bounded honest-only session. | The same ideal classical primitives as the active-classical model. | All five secrecy queries are true, and a shared active-scheduler control proves registration commit and record delivery reachable in the same process. | The selected transcript does not reveal the initial, cached, advanced, future, or beacon-to-server record canary. This is an explicit threat-model check and is logically weaker than the active-classical result. |
| Passive quantum | Transcript observation without network modification or injection over one bounded honest-only session. | Public symbolic recovery of secrets behind Ed25519 and X25519 public keys, while ML-KEM remains opaque. | All five secrecy queries are true, the shared active-scheduler control proves progress, and two expected-failure controls prove that both classical recovery rules expose their test secrets. | The selected hybrid transcript continues to hide the five canaries after the modeled classical-key recovery capability is enabled while the ML-KEM shared secret remains unavailable. This checks dependency structure only; it is not a computational quantum proof. |
| Active quantum | Full network control exercised by one bounded scripted man-in-the-middle. | Scripted recovery of Ed25519 and X25519 secrets, adversary-chosen replacement classical and ML-KEM keys, and no ML-KEM break. | Secrecy, explicit recovery reachability, and honest-origin agreement are all false as required. | The model contains a concrete trace in which the server accepts a forged registration under the honest beacon identity and the attacker derives and opens the initial tasking. Active post-quantum security is therefore refuted rather than claimed. |

The maintained entry points are [`baseline.pv`](../../beaconcrypt-core/proofs/pro-verif/baseline.pv) for active classical, [`passive.pv`](../../beaconcrypt-core/proofs/pro-verif/passive.pv) for both passive scenarios, and [`active-quantum.pv`](../../beaconcrypt-core/proofs/pro-verif/active-quantum.pv) with [`active-quantum-witness.pvl`](../../beaconcrypt-core/proofs/pro-verif/active-quantum-witness.pvl) for the bounded break. [`check-results.awk`](../../beaconcrypt-core/proofs/pro-verif/check-results.awk) fixes each expected classification, including the reachability and capability controls.

The active-classical query set consists of `attacker(INITIAL_SECRET)`, `attacker(CACHED_SECRET)`, `attacker(ADVANCE_SECRET)`, `attacker(FUTURE_SECRET)`, `attacker(BEACON_RECORD_SECRET)`, and the following six injective correspondences:

- `ServerAccepted` implies the matching `BeaconInitiated` event.
- `ServerAccepted` implies the matching single-use `RegistrationConsumed` event.
- `RegistrationConsumed` implies the matching `BeaconInitiated` event.
- `ServerResponseAborted` implies the matching prior `RegistrationConsumed` event.
- `BeaconCommitted` implies the matching prior `ServerCommitted` event.
- `MessageReceived` implies the matching `MessageSent` event with the same session, direction, sequence, sender, receiver, and plaintext.

The converse of beacon commitment is intentionally absent. A server can consume a registration and commit its response before that response is dropped, so `ServerCommitted` does not imply `BeaconCommitted`. Server-side confirmation of beacon receipt requires a later authenticated beacon-to-server record and is not supplied by the registration response alone.

The baseline process has replicated roles and therefore admits multiple sessions, but each honest session follows a fixed record prefix: the registration task, an out-of-order downstream record that creates one cached key, delayed consumption of that cached record, the next future downstream record, and one beacon-to-server record. The result does not quantify over arbitrary record schedules, arbitrary cache contents, replication or rollback of persistent state, parser behavior, denial of service, or implementation side channels. Dedicated existing failed-receive and compromise scenarios provide additional finite traces but do not turn this bounded prefix into an arbitrary-schedule theorem.

Passive scenarios ask only confidentiality queries. Agreement and authenticity queries are omitted because an observer that cannot inject messages cannot exercise the attacks those properties are meant to exclude; passing such correspondences in a passive model would add little evidence and could hide vacuity.

The passive scenarios use `passive.pv`, which removes replicated malicious endpoints and runs one bounded honest beacon, one server, and the private state sink. ProVerif does not classify positive reachability in passive-attacker mode, so both passive targets depend on an active-scheduler run of the same honest-only process that witnesses `BeaconCommitted` and `MessageReceived`. The passive-quantum target also depends on a minimal active-mode control that publishes Ed25519 and X25519 public keys and requires both corresponding private canaries to become attacker-known. A further negative control that reveals or removes the ML-KEM contribution and requires transcript secrecy to fail would strengthen, but is not required for, the current preliminary dependency classification.

The active-classical positive queries use the separately named reachability scenario as their non-vacuity control. Its expected reachable events and malicious-recipient canary exposure are checked independently rather than in the same ProVerif invocation.

## Active-quantum attack witness

The bounded attack intercepts the honest beacon's signed initialization, obtains the signing secret through the modeled Ed25519 recovery capability, and signs a replacement bundle containing attacker-chosen X25519 prekey, X25519 one-time key, and ML-KEM public key. The server accepts the replacement under the honest beacon identity and encapsulates to the attacker-controlled ML-KEM key.

After receiving the server response, the attack obtains the classical server secret through the modeled X25519 recovery capability, computes the four modeled DH contributions, decapsulates the ML-KEM ciphertext with its chosen ML-KEM secret, rebuilds the hax-derived ordered root input and associated data, derives the server-to-beacon chain material, and opens the initial frame. The same run emits `QuantumInitialSecretRecovered(INITIAL_SECRET)`, makes `INITIAL_SECRET` attacker-known, and gives a `ServerAccepted` event for which no matching honest `BeaconInitiated` event exists.

The attack does not need to break ML-KEM because an active attacker that can forge the classical authentication substitutes its own ML-KEM public key before the server encapsulates. This is the central distinction between passive harvest-now-decrypt-later resistance and active post-quantum authentication.

The active witness uses private recovery functions inside one scripted process rather than giving unrestricted recovery destructors to ProVerif's active search. That restriction keeps resolution finite and is sufficient to exhibit a break, but it is not a complete symbolic characterization of every active quantum strategy. The public recovery destructors used by the passive-quantum scenario and the separate private recovery functions used by the scripted active witness are threat-model controls, not implementations or computational descriptions of Shor's algorithm.

## Computational meaning of the scenario matrix

ProVerif operates in a symbolic term algebra. Its positive results do not supply concrete advantage bounds, multi-user reduction losses, running-time bounds, quantum query semantics, random-oracle semantics, or proofs about the named primitive implementations. The four-scenario matrix is valuable because it fixes the intended security claims, finds symbolic dependency errors, checks correspondence structure, and provides the required active-quantum counterexample before the same claims are encoded as computational games.

The active-classical symbolic result is the specification target for a classical computational protocol proof. The passive-classical result should follow as a restricted-adversary corollary rather than receive an unrelated reduction. The passive-quantum result requires a separate QPT or carefully justified post-quantum lifting theorem over classical transcripts. Standard SSProve packages are classical probabilistic programs and do not model quantum state, superposition oracle queries, or QROM access, so a classical SSProve theorem must not be renamed a passive-quantum theorem.

The active-quantum result is a negative theorem and should remain an executable expected-failure test. Replacing Ed25519 or X25519 assumptions with quantum-secure names cannot make the current wire protocol actively post-quantum secure because the concrete attack substitutes an attacker-owned KEM key after breaking classical authentication.

## Modified CTX commitment milestone

For key `K`, nonce `N`, 153-byte associated data `A`, transmitted 16-byte AEAD tag `T`, sequence `S`, and sender identifier `I`, production builds the following 229-byte transcript and protected payload:

```text
X = K || N || A || T || LE64(S) || LE64(I)
U = BLAKE2b-512(X)
R = C || T || U
```

A CTX misattribution event is one fixed protected payload `R` with two accepted explanations that differ in at least one of `K`, `N`, `A`, `S`, `I`, or accepted plaintext. The base AEAD is allowed to open the same `C || T` under distinct keys or contexts, so the binding claim does not smuggle in key commitment from ChaCha20-Poly1305.

The repository-owned [`CtxEventReduction.v`](../../beaconcrypt-core/proofs/ssprove/CtxEventReduction.v) expresses a run as a joint observation containing a misattribution bit and the collision bit extracted by the reduction. Given the pointwise contract that every successful misattribution sets the collision bit, `ctx_misattribution_reduces_to_collision` proves the following inequality in SSProve's probability semantics:

```text
Pr[CTX misattribution] <= Pr[hash collision].
```

This is the correct first computational event-inclusion step for CTX binding and needs no additive AEAD term. The theorem is an event-inclusion lifting inside a joint experiment; a full game-based deliverable must additionally define the adversary-facing CTX package, construct the collision adversary from that package, connect its output to the collision experiment, and account for oracle calls and reduction overhead.

The locked pilot uses Rocq 9.0.0, SSProve 0.2.4, and MathComp 2.4.0, and both `coqc` and `coqchk` pass. The dependency audit retains SSProve/MathComp's standard Boolean-predicate foundations of propositional extensionality, dependent functional extensionality, and constructive indefinite description, while the probability carrier is parameterized by an abstract `realType`; it finds no repository admission, SSProve interchange admission, or hax `falso` dependency.

### Cross-prover deterministic contract

The SSProve theorem deliberately takes the pointwise implication as a parameter instead of re-proving byte encoding or implementation correctness. Its intended discharge is the combination of these checked F* results in [`Beaconcrypt_core.Commitment.Lemmas.fst`](../../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst):

- `production_commitment_input_is_injective` establishes injectivity of the exact six-field 229-byte transcript, including both little-endian integers.
- `ctx_distinct_openings_imply_hash_collision` constructs unequal transcripts with equal hash outputs from any two semantically distinct accepted explanations of one fixed payload, for arbitrary pure hash and AEAD-open functions.

Cross-prover composition still requires a reviewed representation bridge showing that an SSProve misattribution observation contains exactly the two parsed explanations expected by the F* theorem, that both checks correspond to the modeled acceptance predicates, and that the collision bit denotes the unequal-input, equal-output witness returned by F*. The bridge is an integration obligation, not a request for SSProve to verify Rust correctness.

Collision resistance establishes only CTX binding or misattribution resistance. It does not by itself prove that publishing an unkeyed hash whose input includes secret `K` preserves record privacy or ordinary ciphertext integrity. Those composition claims need a separately stated transformed-AEAD, random-oracle, secret-input, or equivalent assumption that is suitable for the classical or quantum attacker class being claimed. Ordinary modifications to `C` remain covered by the base AEAD integrity argument rather than by the same-payload CTX collision reduction.

## Hax coverage and SSProve extraction gate

The ProVerif model uses the hax extraction boundary for six production PQXDH data types and three production-used builders: `registration_id`, `build_root_key_input`, and `build_associated_data`. The three functions carry source-local ProVerif replacement annotations because ProVerif needs ideal constructor semantics, and the build rejects extraction placeholders or disappearance of those named items. Cryptographic equations, role processes, events, state tables, record schedule, attacker controls, and queries remain handwritten because they are security specifications rather than executable Rust behavior.

Direct hax-to-SSProve extraction was probed for `build_commitment_transcript` and related deterministic helpers, but it is not currently an admissible proof dependency. The generated module imports hax's bundled Hacspec prelude and aggregate library, and the pinned prelude exports `Axiom falso : False` for unchecked result unwrapping. Importing that axiom would make every proposition provable and invalidate the trusted computational proof. The selected generated commitment code also requires backend support for Rust array construction that is not yet emitted as a complete standalone SSProve definition.

The SSProve pilot therefore imports neither hax-generated Rocq nor the Hacspec aggregate library. This is an explicit safety gate, not a decision to abandon extraction. Direct extracted code can replace a deterministic contract only after all of the following conditions hold:

1. The exact hax, Rocq, MathComp, and SSProve versions are pinned and version-checked.
2. The deny-all hax selector emits only the reviewed production-used items and their necessary dependencies.
3. The generated modules compile without hand edits or unresolved identifiers.
4. No imported path exposes `False`, unchecked unwrap axioms, admissions, disabled guard checking, or an equivalent proof bypass.
5. Regeneration is deterministic and CI rejects generated drift.
6. The generated representation is shown to match the game interface used by the computational theorem.

Until this gate passes, the sound route is a generic SSProve theorem parameterized by explicit deterministic contracts, with F* or Lean discharging those contracts through a reviewed bridge. Handwriting an executable look-alike of production and silently calling it extracted is not acceptable.

## Assumption ledger

The eventual protocol theorem must state assumptions per attacker class rather than use one undifferentiated “secure primitives” premise.

| Component | Active classical requirement | Passive quantum requirement | Important limitation |
| --- | --- | --- | --- |
| Ed25519 authentication | A multi-user unforgeability notion matching identity, prekey, one-time-key, and ML-KEM-key signatures, including the protocol's related Ed25519-to-X25519 use. | It may be treated as completely broken for transcript confidentiality. | It cannot authenticate against an active quantum attacker. |
| X25519 contributions | The exact active key-agreement assumption needed for the four DH contributions, including public-key validation and all-zero rejection behavior. | Every classical DH contribution may be treated as known. | Classical DH secrecy supplies no harvest-now-decrypt-later protection. |
| ML-KEM-768 | The selected multi-user IND-CCA or protocol-specific encapsulation notion. | Security against QPT adversaries is the remaining public-key source of transcript secrecy. | Passive survival does not stop active substitution of an attacker-owned ML-KEM key. |
| Hybrid root HKDF | A faithful joint combiner or extractor/PRF theorem for the ordered four-DH-plus-KEM input and the protocol's actual labels and output lengths. | A quantum-suitable combiner theorem when the four DH inputs are known and only the ML-KEM secret retains entropy. | Modeling each contribution with independent ideal constructors is stronger than the production HKDF call and does not prove combiner security. |
| Symmetric ratchet KDF | PRF, key-evolution, input-separation, and one-way properties sufficient for record keys and scoped forward secrecy. | Quantum-suitable versions for any passive-quantum claim. | No post-compromise security follows from a one-way chain without fresh secret input. |
| ChaCha20-Poly1305 | The exact nonce-based privacy and integrity notion under the protocol's key and nonce discipline. | A quantum-suitable classical-interface notion for passive transcript confidentiality. | Primitive correctness and implementation side channels remain out of scope. |
| Modified CTX/BLAKE2b-512 | Collision resistance for binding, plus an explicit CTX privacy and ordinary-integrity preservation assumption for record composition. | Quantum collision resistance for binding and a QROM or other quantum-suitable preservation assumption for privacy. | Collision resistance alone does not show that publishing `H(K || ...)` preserves secrecy or ordinary integrity. |
| State and randomness | Fresh unbiased key generation, one authoritative state owner, atomic replay consumption, no rollback or fork, and correct peer routing. | Honest unmodified delivery and retained ML-KEM secret state. | Replication, rollback, compromise timing, erasure, and availability need separately scoped models. |

Primitive correctness, primitive implementation verification, compiler correctness, side-channel resistance, and machine-code correspondence are outside the computational proof requested here. Primitive security properties remain explicit assumptions, while deterministic protocol and state facts are imported as Lean/F* contracts.

## Remaining computational protocol work

The following work remains before beaconcrypt has a complete computational protocol proof:

1. Define adversary-facing SSProve interfaces for registration, response, record sending, record receiving, compromise, replay, and bounded concurrency with the actual public transcript and failure leakage.
2. Replace the CTX joint-observation pilot with an executable CTX game and collision reduction, record exact hash-query and running-time overhead, and complete the F*/SSProve representation bridge.
3. Select and formalize one joint HKDF combiner assumption that covers the production input order, shared labels, variable output lengths, public or correlated classical inputs, and the remaining ML-KEM entropy.
4. Prove active-classical handshake secrecy and one-way agreement under explicit multi-user Ed25519, X25519, ML-KEM, and HKDF assumptions, while retaining the dropped-response counterexample to converse agreement.
5. Prove ratchet record privacy, authenticity, replay resistance, direction and peer separation, and the intended scoped forward-secrecy statements for arbitrary bounded schedules rather than only the current fixed ProVerif prefix.
6. Compose CTX binding separately from CTX privacy and ordinary-integrity preservation so that a collision-resistance theorem is never used for the wrong property.
7. Add an ML-KEM-removal or reveal negative control to the honest-only passive suite, then state passive-classical security as a restricted-adversary corollary and either use a quantum-aware framework or provide a reviewed external lifting theorem for passive quantum harvest-now-decrypt-later security.
8. Retain the active-quantum ProVerif trace as a required negative control and state active post-quantum security as unsupported until the wire protocol authenticates all key-establishment material with a quantum-secure mechanism.
9. Maintain the existing SSProve proof-policy, exact assumption report, out-of-tree object, `coqchk`, CI, and trust-boundary inventory gates, and extend them for every future full-game or admitted hax-extraction artifact.

Completion means checked games and reductions with named assumptions and losses, not merely four passing ProVerif scenario labels. Until the items above are complete, the supported summary is: beaconcrypt has an explicit four-way symbolic threat-model suite, an expected active-quantum break, and a mechanized first CTX event-inclusion result, while the end-to-end computational protocol theorem remains work in progress.

## Maintenance and verification

The ProVerif result checker pins the exact number and classification of queries for each named scenario, so an unexpected proof, attack, timeout, inconclusive result, or missing query fails the build. Some correspondence checks currently include ProVerif-generated variable suffixes and are therefore safe against false acceptance but brittle across harmless pretty-printer changes; structural or normalized matching should replace those exact suffixes. The CTX/no-CTX weak-AEAD differential remains a separate required negative control: the double-opening query must be unreachable with CTX and reachable when only the commitment checks are removed.

Run the focused checks in the locked proof shell before changing the status in this report:

```bash
make -C beaconcrypt-core check-proverif
make -C beaconcrypt-core check-ssprove
```

Run `make -C beaconcrypt-core verify` for the repository-wide proof gate once the independent Lean/F* extraction reorganization is healthy. A failure confined to those correctness backends must be reported to their owners, but it must not be hidden by weakening the computational or symbolic checks.
