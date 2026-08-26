<!-- SPDX-License-Identifier: 0BSD -->

# Computational security proof integration evaluation

Status on 2026-08-26: the ProVerif suite names and checks the four required attacker scenarios, and the SSProve suite contains bounded hidden-ROM CTX binding/privacy hops, a closed one-session one-record ideal PQXDH-and-ratchet game, and an attacker-facing bounded classical-ROM extension. The closed game proves zero advantage for active classical, passive classical, and a passive-quantum classical-query capability model, while active quantum has the expected advantage-one attack. The extension reduces each positive forwarding case and all active-classical actions to the exact hidden-pad-query probability but supplies no negligible production-width bound. This is not yet a complete computational proof of arbitrary beaconcrypt executions or a QROM theorem.

## Decision and separation of concerns

The computational proof must reason about protocol security games, adversarial advantage, reductions, and composition assumptions. It assumes that the Rust operations supplied to those games implement their stated deterministic contracts. Lean and F* own implementation correctness, extraction refinement, fixed-size layouts, and state-machine correctness; a temporary Lean or F* failure caused by implementation/extraction reorganization is therefore not a computational-model counterexample and is not repaired as part of this work.

This separation does not permit an undocumented implementation assumption. Every deterministic fact consumed by a computational theorem must either be a named contract with a representation bridge to a named Lean or F* result or be identified explicitly as a handwritten model shape whose bridge remains open. The computational proof remains conditional when that bridge has not been reviewed against the current extraction snapshot.

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

The active-classical symbolic result is the specification target for a classical computational protocol proof. The passive-classical result should follow as a restricted-adversary corollary rather than receive an unrelated reduction. The checked SSProve passive-quantum capability game exposes the classical secret-recovery consequences while keeping honest ML-KEM decapsulation opaque, but a genuine passive-quantum result still requires a QPT or carefully justified post-quantum lifting theorem over classical transcripts. Standard SSProve packages are classical probabilistic programs and do not model quantum state, superposition oracle queries, or QROM access.

The active-quantum result is a negative theorem and should remain an executable expected-failure test. Replacing Ed25519 or X25519 assumptions with quantum-secure names cannot make the current wire protocol actively post-quantum secure because the concrete attack substitutes an attacker-owned KEM key after breaking classical authentication.

## Bounded SSProve PQXDH and ratchet games

[`PqxdhRatchetGames.v`](../../beaconcrypt-core/proofs/ssprove/PqxdhRatchetGames.v) defines network power and computation power independently and instantiates all four combinations. One Ed25519 seed jointly controls signing and the converted X25519 identity, so the quantum capability compromises those correlated uses together rather than sampling independent secrets.

The modeled PQXDH root input contains exactly four ordered DH contributions followed by the ML-KEM contribution, corresponding to the production `build_root_key_input` contract after its fixed padding. Authentication metadata is deliberately absent from the root hash input. The symmetric KDF is one shared finite table for both initial expansion and later ratchet steps, and its abstract output has two common prefix components plus the later suffix so equal inputs enforce the production 64/76-byte prefix relation represented by `split_initial_ratchet_kdf_output` and `split_ratchet_kdf_output`.

The closed confidentiality experiment samples a jointly uniform eight-bit finite random-oracle tape with distinct honest and substituted root entries, establishes one session, advances one symmetric-ratchet record at fixed sequence zero, and masks a Boolean challenge with the ideal record key. Public metadata is fixed and equal between challenge branches. For every deterministic Boolean distinguisher, a measure-preserving tape involution proves exact equality of the hidden-root games and therefore advantage zero.

The checked modality results are:

- Active classical has zero advantage for both statically selected network actions: forwarding reaches the hidden honest root, while replacement fails ideal authentication and returns a challenge-independent failure observation.
- Passive classical is the forward-only restriction and has zero advantage.
- Passive quantum capability has zero advantage after modeled recovery of the joint Ed25519/X25519 secret because the passive observer cannot replace the honest ML-KEM key and cannot decapsulate its ciphertext.
- Active quantum has advantage one for the identity distinguisher on the replacement action because forged classical authentication permits an attacker-selected ML-KEM key. The proof indexes the root oracle separately at the honest and substituted inputs and derives the removed record pad by recomputing from the exact accepted substituted input.

These are exact results for the closed finite ideal game, not reductions for the production primitive instances. The action is chosen outside the challenge game, and that closed game does not give the attacker a public-transcript API, direct KDF-random-oracle queries, record-tampering/decryption access, or a numerical hidden-input guessing bound. It covers neither multiple sessions nor arbitrary ratchet schedules, replay, compromise, forward secrecy, CTX composition, randomized interactive distinguishers, QPT computation, or QROM access. The executable SSProve package records the same bounded sampling computation, while the assumption-safe capstones use its direct finite pushforward to avoid a stronger admitted infinite-sum interchange dependency in the pinned high-level library.

[`PqxdhRatchetRom.v`](../../beaconcrypt-core/proofs/ssprove/PqxdhRatchetRom.v) adds the missing bounded classical root/ratchet oracle interface for the positive cases. It fixes the four DH coordinates so the observer may guess them, samples only the honest ML-KEM atom and complete tagged table secretly, publishes the challenge ciphertext, and runs an arbitrary fuel-bounded adaptive query tree against that table. A table-dependent involution flips the pad without changing the hidden query that indexes it; any coupled decision mismatch therefore implies that the trace asked that exact query. The main capstone proves `Adv <= Pr[hidden-pad query]`, active-classical replacement is exactly zero, and `protocol_supported_scenario_root_hidden` checks that only active-classical forward/replace, passive-classical forward, and passive-quantum forward inhabit the wrapper. Active-quantum replacement remains exclusively the separate advantage-one theorem.

This extension does not turn the abstract result into a negligible bound. The one-bit symmetric domain can be exhausted with two queries, so the bad-event probability can be one; production-width parameterization and a guessing bound remain open. The program receives only the fixed public shape and challenge ciphertext, not the actual registration transcript or a record-tampering/decryption interface, and its oracle queries remain classical.

## Modified CTX commitment games

For key `K`, nonce `N`, 153-byte associated data `A`, transmitted 16-byte AEAD tag `T`, sequence `S`, and sender identifier `I`, production builds the following 229-byte transcript and protected payload:

```text
X = K || N || A || T || LE64(S) || LE64(I)
U = BLAKE2b-512(X)
R = C || T || U
```

A CTX misattribution event is one fixed protected payload `R` with two accepted explanations that differ in at least one of `K`, `N`, `A`, `S`, `I`, or accepted plaintext. The base AEAD is allowed to open the same `C || T` under distinct keys or contexts, so the binding claim does not smuggle in key commitment from ChaCha20-Poly1305.

[`BoundedRom.v`](../../beaconcrypt-core/proofs/ssprove/BoundedRom.v) supplies a generic fuel-bounded adaptive classical random-oracle tree whose complete finite function table remains hidden from the program and observation. [`CtxGame.v`](../../beaconcrypt-core/proofs/ssprove/CtxGame.v) instantiates that runner with an adversary that can make at most `q` hash queries and return one protected payload with two explanations. The verifier performs exactly two additional hidden-table queries, checks both outer digests and both calls to an arbitrary deterministic multi-opening AEAD, and extracts the two transcript-and-digest pairs.

The checked game proves:

```text
Pr_bounded-hidden-ROM[CTX misattribution] <= Pr_same-run[unequal-input, equal-output collision].
```

`ctx_hidden_rom_extractor_reduction` proves the generic inequality for any hidden-table distribution, and `ctx_uniform_hidden_rom_extractor_reduction` specializes it to a uniformly sampled finite random function. `ctx_hidden_binding_trace_size_bound` accounts for at most `q + 2` completed oracle queries, while `ctx_attach_verifier_completed_run` proves that a bounded completed adversary trace is preserved and followed by exactly the two verifier queries. A concrete deliberately multi-opening AEAD with a colliding constant table makes the misattribution event executable and non-vacuous. The earlier [`CtxEventReduction.v`](../../beaconcrypt-core/proofs/ssprove/CtxEventReduction.v) remains as the more generic same-execution event-inclusion lemma.

[`CtxPrivacy.v`](../../beaconcrypt-core/proofs/ssprove/CtxPrivacy.v) keeps confidentiality separate from binding. It represents the real digest by jointly sampling a uniform hidden key, finite random-oracle table, and fresh value and programming the table at the key-derived transcript. A key-preserving swap establishes the true-real/programmed-real representation, the same-run fundamental lemma makes every programmed/fresh decision mismatch imply a classical query for the secret transcript, and `ctx_hidden_uniform_key_true_real_privacy_bound` bounds the absolute true-real/fresh-ideal decision gap by that bad-query probability using direct finite-source reindexing.

The CTX binding proof needs no additive AEAD-security term, but it supplies no numerical collision bound for BLAKE2b-512. The privacy hop is conditional on a hidden uniform record key and an independent ideal-AEAD confidentiality theorem; it supplies neither the probability of guessing a production-width key nor a complete transformed-AEAD composition theorem. Both files use one-bit finite atoms to make exhaustive random functions available to SSProve, so a representation and width-parameter bridge remains required before claiming the production game.

The locked suite uses Rocq 9.0.0, SSProve 0.2.4, and MathComp 2.4.0. The build compiles and kernel-checks every repository-owned module, exact-diffs every assumption report, and rejects repository admissions, the unsafe hax prelude, and the pinned library's admitted infinite-sum interchange theorem. The accepted foundational assumptions are propositional extensionality, dependent functional extensionality, constructive indefinite description, and an abstract `realType`.

### Cross-prover deterministic contract

The game-level CTX transcript is an injective product of its semantic bit fields, which lets SSProve prove the extractor soundness without assuming implementation correctness. Its intended connection to production is the combination of these checked F* results in [`Beaconcrypt_core.Commitment.Lemmas.fst`](../../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst):

- `production_commitment_input_is_injective` establishes injectivity of the exact six-field 229-byte transcript, including both little-endian integers.
- `ctx_distinct_openings_imply_hash_collision` constructs unequal transcripts with equal hash outputs from any two semantically distinct accepted explanations of one fixed payload, for arbitrary pure hash and AEAD-open functions.

Cross-prover composition still requires a reviewed representation bridge showing that the SSProve semantic fields represent the parsed production explanations expected by the F* theorem, that both checks correspond to the modeled acceptance predicates, and that the abstract transcript constructor corresponds to the proved fixed-width byte encoding. The bridge is an integration obligation, not a request for SSProve to verify Rust correctness.

Collision resistance establishes only CTX binding or misattribution resistance. It does not by itself prove that publishing an unkeyed hash whose input includes secret `K` preserves record privacy or ordinary ciphertext integrity. Those composition claims need a separately stated transformed-AEAD, random-oracle, secret-input, or equivalent assumption that is suitable for the classical or quantum attacker class being claimed. Ordinary modifications to `C` remain covered by the base AEAD integrity argument rather than by the same-payload CTX collision reduction.

## Hax coverage and SSProve extraction gate

The ProVerif model uses the hax extraction boundary for six production PQXDH data types and three production-used builders: `registration_id`, `build_root_key_input`, and `build_associated_data`. The three functions carry source-local ProVerif replacement annotations because ProVerif needs ideal constructor semantics, and the build rejects extraction placeholders or disappearance of those named items. Cryptographic equations, role processes, events, state tables, record schedule, attacker controls, and queries remain handwritten because they are security specifications rather than executable Rust behavior.

Direct hax-to-SSProve extraction was probed for `build_commitment_transcript` and related deterministic helpers, but it is not currently an admissible proof dependency. The generated module imports hax's bundled Hacspec prelude and aggregate library, and the pinned prelude exports `Axiom falso : False` for unchecked result unwrapping. Importing that axiom would make every proposition provable and invalidate the trusted computational proof. The selected generated commitment code also requires backend support for Rust array construction that is not yet emitted as a complete standalone SSProve definition.

The SSProve suite therefore imports neither hax-generated Rocq nor the Hacspec aggregate library. This is an explicit safety gate, not a decision to abandon extraction. Direct extracted code can replace a deterministic contract only after all of the following conditions hold:

1. The exact hax, Rocq, MathComp, and SSProve versions are pinned and version-checked.
2. The deny-all hax selector emits only the reviewed production-used items and their necessary dependencies.
3. The generated modules compile without hand edits or unresolved identifiers.
4. No imported path exposes `False`, unchecked unwrap axioms, admissions, disabled guard checking, or an equivalent proof bypass.
5. Regeneration is deterministic and CI rejects generated drift.
6. The generated representation is shown to match the game interface used by the computational theorem.

Until this gate passes, the sound route is to state the handwritten finite model explicitly, mirror only named production operation shapes, and keep the F*/Lean-to-SSProve representation bridge as a named open obligation. Handwriting an executable look-alike of production and silently calling it extracted is not acceptable.

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

Primitive correctness, primitive implementation verification, compiler correctness, side-channel resistance, and machine-code correspondence are outside the computational proof requested here. Primitive security properties remain explicit assumptions. Deterministic protocol and state facts must be supplied by named Lean/F* contracts when the representation bridge is complete; the present finite SSProve shapes keep that bridge open rather than claiming an import that has not occurred.

## Remaining computational protocol work

The following work remains before beaconcrypt has a complete computational protocol proof:

1. Extend the one-session, one-record game to adversary-facing registration, response, record sending, record receiving, compromise, replay, and bounded-concurrency interfaces with the actual public transcript and failure leakage.
2. Generalize the finite CTX fields to production-width types, complete the F*/SSProve representation bridge, and connect the extracted collision to a named primitive collision game with exact hash-query and reduction-overhead accounting.
3. Generalize the one-bit bounded root/ratchet random-oracle interface to production-width domains, prove a numerical hidden-input bad-query bound, and select one joint HKDF combiner assumption covering the production input order, shared labels, variable output lengths, public or correlated classical inputs, and remaining ML-KEM entropy.
4. Lift the closed active-classical game to multi-user handshake secrecy and one-way agreement under explicit ideal or reduced Ed25519, X25519, ML-KEM, and HKDF interfaces, while retaining the dropped-response counterexample to converse agreement.
5. Prove ratchet record privacy, authenticity, replay resistance, direction and peer separation, and intended scoped forward secrecy for arbitrary bounded schedules rather than one fixed sequence-zero record.
6. Compose the CTX programming hop with ideal AEAD confidentiality, and prove ordinary-integrity preservation separately from CTX binding so collision resistance is never used for the wrong property.
7. Add an ML-KEM-removal or reveal negative control to the honest-only passive suite, and use a quantum-aware framework or reviewed external lifting theorem before promoting the passive-quantum capability result to a QPT or QROM claim.
8. Retain both active-quantum attack witnesses as required negative controls and state active post-quantum security as unsupported until the wire protocol authenticates all key-establishment material with a quantum-secure mechanism.
9. Maintain the SSProve proof-policy, exact assumption reports, out-of-tree objects, `coqchk`, CI, and trust-boundary inventory gates for every future full-game or extraction artifact.

Completion means checked games and reductions with named assumptions and losses, not merely four passing labels in a fixed ideal game. The supported summary is now: beaconcrypt has a four-way symbolic suite, bounded hidden-ROM CTX binding and privacy hops, a one-session one-record closed ideal game with three exact zero-advantage results and the expected active-quantum advantage-one break, and an adaptive classical-ROM reduction of the positive cases to an explicit bad-query event. Its numerical production-width bound, arbitrary-execution composition, and quantum-computational lifting remain work in progress.

## Maintenance and verification

The ProVerif result checker pins the exact number and classification of queries for each named scenario, so an unexpected proof, attack, timeout, inconclusive result, or missing query fails the build. Some correspondence checks currently include ProVerif-generated variable suffixes and are therefore safe against false acceptance but brittle across harmless pretty-printer changes; structural or normalized matching should replace those exact suffixes. The CTX/no-CTX weak-AEAD differential remains a separate required negative control: the double-opening query must be unreachable with CTX and reachable when only the commitment checks are removed.

Run the focused checks in the locked proof shell before changing the status in this report:

```bash
make -C beaconcrypt-core check-proverif
make -C beaconcrypt-core check-ssprove
```

Run `make -C beaconcrypt-core verify` for the repository-wide proof gate once the independent Lean/F* extraction reorganization is healthy. A failure confined to those correctness backends must be reported to their owners, but it must not be hidden by weakening the computational or symbolic checks.
