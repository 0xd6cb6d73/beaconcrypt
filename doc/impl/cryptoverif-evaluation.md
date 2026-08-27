<!-- SPDX-License-Identifier: 0BSD -->

# CryptoVerif evaluation for beaconcrypt

## Outcome

This evaluation was performed in the dedicated `cryptoverif` worktree and branch, based on `ssprove` at commit `babec5d`. It concerns protocol security in the computational model only. It neither uses nor extends the F*/Lean implementation-correctness layers, and it makes no claim that the handwritten CryptoVerif processes correspond to Rust.

CryptoVerif is a strong fit for the automated protocol-proof role requested for beaconcrypt. The checked suite demonstrates automatic game transformations for active, polynomially replicated registration and established-channel abstractions, derives explicit multi-user advantage bounds from named primitive assumptions, proves injective correspondences, and detects the loss of assigned-ID agreement in a one-line negative control. This goes materially beyond the current SSProve proof of concept in adversary scheduling and session replication.

The result is not yet a full beaconcrypt theorem. The active registration model authenticates one representative static-DH contribution rather than the exact four-DH-plus-ML-KEM root, the established-channel model assumes fresh directional traffic keys and a composed record transform rather than the exact ratchet and CTX construction, and CryptoVerif did not automatically compose active beacon-finish decryption with registration confidentiality. Those gaps are recorded as model boundaries, not hidden behind a general “secure primitives” premise.

CryptoVerif's relevant capabilities and computational semantics are described on the [official CryptoVerif site](https://cryptoverif.inria.fr/) and in the [CryptoVerif 2.12 manual](https://bblanche.gitlabpages.inria.fr/cryptoverif/manual.pdf). The suite pins that release rather than relying on a system installation.

## What the checked results mean for developers

The most useful way to read these proofs is as tests of protocol behavior under a hostile network. The modeled attacker may create many sessions, choose inputs, observe traffic, delay or drop messages, replay old messages, modify transmitted values and protected frames, and deliver a message in the wrong session or direction. An “honest” beacon or server here means a role that follows the modeled steps and whose relevant secrets have not been disclosed; it does not mean that the application has authorized an identity. “Proved” means CryptoVerif shows that violating the stated behavior would require successfully attacking an explicitly assumed building block such as signing, key exchange, or authenticated encryption, with the accumulated probability shown in its result. It does not mean that failure is mathematically impossible.

Every statement in this table begins with “in the checked model.” The final column is part of the claim, not fine print.

| Developer question | Functionally proved behavior | Required qualification |
| --- | --- | --- |
| Can the network make an honest beacon finish registration with a response that the honest server never created? | No. Every completed honest-beacon registration has one unique matching honest-server commit over the same initialization bundle, server and response fields, assigned beacon ID, initial task, and protected frame. | This simplified registration model represents one authenticated classical key-exchange contribution, not the complete production hybrid handshake or Rust implementation. |
| Can the modeled honest server commit an exact honest-beacon bundle that no modeled honest beacon initiated? | No. An honest-server commit for an exact bundle in the model's private honest set has one unique matching beacon initiation. | Membership in that private set is proof instrumentation. This result does not say that the server rejects, distrusts, or deauthorizes other valid self-signed registrations. |
| Does a successfully signed registration prove that a beacon is authorized to use the application? | No. The model distinguishes bundles created by its honest-beacon role from other valid self-signed bundles, but that classification is proof bookkeeping rather than an access-control decision. | Enrollment, routing, tenant separation, and authorization policy remain the integrating application's responsibility. The cryptographic proof does not create an ACL. |
| Can a registration response be relabeled with a different assigned beacon ID? | Not when the beacon checks that the clear outer ID equals the ID inside the authenticated encrypted payload. Removing only that equality permits the documented relabeling trace and causes CryptoVerif to stop proving agreement in the negative control. | CryptoVerif's expected failure is paired with the concrete modeled trace; `Could not prove` alone is not an attack proof. |
| Does a server response prove that the beacon is established? | No, and no such property is claimed. The network may drop the response after the server commits, so only beacon acceptance implies a matching server commit, not the reverse. | The model consumes the registration identifier before returning Phase 2 and proves neither retry nor recovery after response loss. Server-side confirmation needs a later authenticated beacon-to-server record. |
| Can an observer learn the initial task from the registration response? | The complete response does not reveal which of two attacker-chosen equal-length task values it contains, across many registrations. | This model does not let the attacker feed modified responses into a beacon and learn whether they were accepted. Length and public metadata are not hidden. |
| Can the network invent, alter, replay, direction-swap, or move an established-channel record and still have it accepted? | An accepted record has one unique matching send with the same session, endpoints, direction, associated data, sequence, plaintext, and frame. For each session and receiving direction, a sequence can be accepted at most once, and using another session or direction changes the protected context. | The model begins with already authenticated, independent fresh directional keys and assumes the combined record transform is private and tamper-resistant. It does not derive those keys through beaconcrypt registration or ratcheting. |
| Can the network read established traffic? | Even across many active sessions and chosen messages in both directions, it cannot determine which member of each equal-length message pair was protected except with the displayed probability of defeating the assumed record protection. | Message lengths and routing metadata remain public; the exact ratchet, derived nonces, skipped-key cache, and application behavior are absent. |
| What post-quantum behavior is covered? | One passive harvest-now/decrypt-later probe keeps a selected equal-length registration plaintext confidential after all X25519 contributions are treated as known. If authenticated keys already exist and the symmetric assumptions resist quantum attackers, the established-channel abstraction retains its modeled record-confidentiality and unique-send-origin properties against an active network. | Active post-quantum registration and end-to-end authentication are not proved and are false for the current Ed25519-authenticated handshake after classical authentication is broken. |
| Is an earlier record hidden after later ratchet state is exposed? | In the one-step probe, revealing the next chain state does not reveal the earlier equal-length challenge record when the previous chain state has actually been discarded. | This covers one step and modeled deletion only; cached skipped keys, retained copies, longer histories, persistence, and recovery after compromise are outside the result. |

For a library consumer, the supported wording today is: “The beaconcrypt protocol design has executable computational proofs for these abstract registration and channel behaviors under named cryptographic assumptions.” The unsupported wording is: “The shipped beaconcrypt library is end-to-end formally proved secure.” That stronger statement requires the exact PQXDH root, registration-to-channel composition, active registration privacy, ratchet and persistence models, and a reviewed connection from the CryptoVerif processes to the implementation.

## CryptoVerif versus SSProve

The two tools answer different questions and should coexist.

| Dimension | CryptoVerif role in beaconcrypt | Existing SSProve role |
| --- | --- | --- |
| Primary strength | Executes guided game transformations and automatically accumulates computational reduction losses | Makes small finite games, couplings, bad events, and exact probability arguments explicit in a proof assistant |
| Adversary interface | Naturally expresses replicated, attacker-callable oracles and active scheduling | Current models use closed or fuel-bounded finite interfaces that require manual proof construction |
| Authentication | Automatically proves event correspondences, including injective agreement derived from one-use state | Requires a purpose-built game and theorem for each correspondence or bad event |
| Secrecy | Native real-or-random secrecy queries and game equivalences | Fine-grained control over the exact experiment and measure-preserving argument |
| Bounds | Automatically reports primitive advantages, collision terms, query counts, and multi-user factors | Best suited to fundamental lemmas and exact finite bounds once the game is manually decomposed |
| Stateful detail | Effective for monotone tables and bounded replicated protocol structure; exact mutable cache evolution can impede automation | Better suited to bespoke reasoning about the bounded ratchet/cache mechanics, at the cost of more proof work |
| Trust and review | The process, primitive interfaces, typed encodings, and CryptoVerif transformations must be reviewed | The game definition and any admitted library facts must be reviewed; proof terms are kernel-checked |

The recommended division is therefore to use CryptoVerif for the largest protocol-level game it can automate cleanly and retain SSProve for fundamentals that need custom probability or state arguments. Reimplementing CryptoVerif's automatic multi-session reductions manually in SSProve would lose the main benefit of this investigation; asking CryptoVerif to encode the exact 50-entry cache before the higher-level protocol theorem stabilizes would likewise play against its strengths.

## Checked automated results

Seven oracle-front-end models under [`beaconcrypt-core/proofs/crypto-verif/`](../../beaconcrypt-core/proofs/crypto-verif/) run automatically with CryptoVerif 2.12. Three are protocol-level positive models, three are focused assumption probes, and one is an expected-failure control.

| Model | Adversary and replication | Automatically checked property | Main abstraction boundary |
| --- | --- | --- | --- |
| `automated-registration-first-record.ocv` | Active Phase-2 delivery with polynomially many honest beacons and server registrations | Injective honest Phase-1 origin and injective `BeaconCommitted` to matching `HonestServerCommitted` agreement | One authenticated static-DH root contribution; no confidentiality query; terminal one-shot finish |
| `automated-registration-confidentiality.ocv` | Polynomially many honest Phase-1 publications and registrations with adversary-chosen equal-length task pairs | Secrecy of one global left/right bit from complete Phase-2 responses | No active beacon-finish decryption oracle |
| `automated-established-channel.ocv` | Polynomially many attacker-parameterized sessions, sends, receives, modifications, replays, and cross-context deliveries in both directions | One global left/right bit plus injective acceptance-to-send in both directions | Starts from fresh directional keys; composed record interface; no exact ratchet |
| `assigned-id-binding-negative-control.ocv` | Same as registration agreement, except the encrypted and outer assigned IDs need not match | Honest Phase-1 origin still proves; beacon-to-server commit agreement does not | Expected failure, not a security theorem |
| `passive-post-quantum-one-record.ocv` | One honest encapsulation with every X25519 contribution public | Equal-length registration-record confidentiality | Passive, one session, one record |
| `ratchet-forward-secrecy.ocv` | One record followed by successor-chain disclosure | Predecessor-record confidentiality conditioned on logical erasure | One step; no cached keys or other compromise |
| `record-authentication-replay.ocv` | Repeated delivery attempts against one sent record | Injective acceptance-to-send correspondence | One session; composed record-integrity assumption |

The positive protocol models establish the following scoped statements.

- If an honest beacon reaches `BeaconCommitted` in the registration-agreement model, there was a unique matching honest server commit over the same complete modeled transcript, assigned ID, accepted task, and protected frame. The reported bound contains signature-forgery and signing-key-collision terms, multi-session static-DH PRF-ODH loss, and registration-record integrity loss.
- If the server commits a response for an exact honest Phase-1 bundle, there was a unique matching beacon initiation. This origin query proves exactly in the transformed model because the one-use registration table and private honest-bundle table supply the injectivity; it does not authenticate attacker-owned self-signed identities.
- The registration-confidentiality challenge bit remains secret across polynomially many honest beacon and server-registration calls. Its bound contains the corresponding multi-user signature, static-DH PRF-ODH, and record-privacy terms.
- In the established-channel abstraction, one global challenge bit remains secret across polynomially many sessions and chosen-message sends in both directions. Every accepted record has a unique matching send with the same session, server, beacon, associated data, direction-specific context, sequence, plaintext, and frame.

The exact output policy records the complete ordered `RESULT` lines rather than matching only “proved.” This makes changes in query multiplicity, reductions, collision factors, or assumptions review-visible.

“Automated” here means guided automation, not inference from Rust or from an informal protocol description. Each main model contains a short proof strategy that selects the expected primitive transformations and their order; CryptoVerif then performs the index-sensitive game rewrites, oracle replication reasoning, collision accounting, correspondence proof, and bound construction. Developing the model still required choosing the correct multi-session PRF-ODH interface, exposing monotone state, using bounded transcript types, and separating a combined privacy game that the available transformations did not close.

## Active registration model

The registration model is the clearest demonstration of CryptoVerif's comparative advantage. Its adversary-facing oracles represent the following protocol shape:

- `NewHonestBeacon` generates a fresh signing identity and three separately signed Phase-1 public fields, records the exact honest bundle privately, emits `BeaconInitiated`, and exposes a single terminal `BeaconFinish` continuation.
- `ServerRegister` accepts adversary-supplied bundles after verifying all three signatures, consumes the identity/one-time-key registration identifier at most once, allocates a unique requested key ID, produces fresh public response fields, and returns either a protected honest task or an adversary-controlled frame for a bundle outside the private honest set.
- `BeaconFinish` accepts adversarially selected response fields, checks the pinned server public key, derives the modeled root from the beacon prekey and server static key, authenticates the protected initial task, requires the encrypted assigned ID to equal the clear outer assigned ID, and only then emits `BeaconCommitted`.

The signatures use one injective, role-tagged message constructor. This accurately preserves that production signs three fields independently while preventing proof search from spending time on collisions between syntactically unrelated signing interfaces. The root uses CryptoVerif's multi-session `msPRF_ODH` equivalence with the server static exponent on the many-session side and each beacon prekey exponent on the one-session side. A single-session `snPRF_ODH` assumption would not match one long-lived server key processing many registrations.

The consumed-registration and allocated-ID tables are monotone, which fits CryptoVerif well. Their lookup-failure branches make reuse impossible, and CryptoVerif turns that state fact into injective correspondence automatically. One finish continuation per beacon matches the terminal success/abort typestate and also avoids modeling impossible repeated finishes.

The server-commit-to-beacon-commit converse is intentionally absent and false: an active adversary can drop Phase 2 after the server commits. Server-side key confirmation requires a later authenticated beacon-to-server record. Composing such a first reply with registration is a useful next model, but it is not claimed by the current separate registration and established-channel results.

The assigned-ID negative control removes only `=outer_assigned_id` from the decrypted payload pattern. CryptoVerif then fails precisely the `BeaconCommitted`-to-`HonestServerCommitted` query while retaining the honest-origin result. The concrete modeled relabeling trace forwards a valid protected response while replacing its clear outer ID with a distinct value, after which the weakened beacon commits event data under the substituted ID and no longer matches the server event under the encrypted ID. The `Could not prove` output is a regression classification rather than an attack theorem by itself, but together with that trace it is useful evidence that the positive agreement result depends on the intended binding check.

## Why confidentiality is a separate game

An initial combined model exposed both the active `BeaconFinish` decryption oracle and a global registration challenge bit. CryptoVerif applied record-integrity and record-privacy transformations but left a randomized-key, cross-oracle branch unresolved. The predefined AEAD privacy equivalence is IND-CPA shaped and does not itself provide the chosen-ciphertext interface needed after adding active finish.

The checked suite therefore makes two honest claims: active registration agreement under INT-CTXT, and registration-response confidentiality without the finish decryption oracle under IND-CPA. These results are complementary, but the repository does not assert their CCA-style composition. Closing that gap requires either a suitable reviewed AEAD/record primitive interface with the necessary decryption oracle or a manual intermediate game, not a change of wording around the current output.

## Primitive assumption boundary

Primitive proofs are explicitly out of scope. CryptoVerif is used to prove protocol composition conditional on named interfaces.

| Protocol dependency | Modeled assumption | Scope condition |
| --- | --- | --- |
| Three Phase-1 signatures | Multi-user EUF-CMA signature interface | Role-tagged field encodings; honest identities sign one bundle in this milestone |
| Authenticated classical root contribution | Multi-session PRF-ODH interface | Pinned server static key, adversarially scheduled registrations, one finish per beacon |
| Session-key projection | Random output splitting | One server-to-beacon record key in the registration milestone |
| Registration record | AEAD IND-CPA in the privacy game and INT-CTXT in the agreement game | These separate assumptions are not claimed to compose automatically into active CCA privacy |
| Established records | Privacy and integrity of a direction/context-aware composed record transform | Exact ChaCha20-Poly1305 plus BLAKE2b CTX composition is not proved |
| Passive hybrid probe | ML-KEM IND-CCA2, hybrid-root PRF, shared symmetric-KDF PRF, and AEAD privacy | All four DH contributions are deliberately public |
| Ratchet probe | Ratchet PRF and AEAD privacy | Logical predecessor erasure and one successor reveal only |

The active registration model binds the other three public DH placeholders and a KEM placeholder into its transcript but does not derive security from their hidden values. This is a deliberate intermediate abstraction, not a statement that production should omit them. Replacing the classical authenticated contribution with KEM IND-CCA2 would be unsound for active authentication: anyone can encapsulate to a public ML-KEM key and know the resulting shared secret.

The largest later primitive-interface decision remains the modified CTX transform. Collision resistance can support binding of two distinct explanations, but it does not establish confidentiality preservation for publishing `BLAKE2b(K || nonce || AD || tag || sequence || sender)`. A full protocol theorem should either assume the security of the composed record transform or add a reviewed secret-input/hash or random-oracle game. It must not infer privacy from collision resistance alone.

## Classical and post-quantum scope

The active registration results load `default.ocvl` because their PRF-ODH authentication assumption is classical. The established-channel abstraction and three focused probes load `pq.ocvl`; that library contains assumptions intended to retain CryptoVerif's post-quantum soundness for black-box interactive attackers. The supporting [CSF 2024 work](https://bblanche.gitlabpages.inria.fr/publications/BlanchetJacommeCSF24.html) describes CryptoVerif's post-quantum computational soundness and hybrid-protocol case studies.

The positive post-quantum registration/hybrid result in this suite is deliberately passive: all X25519 contributions are public and record confidentiality rests on ML-KEM plus the combiner and symmetric assumptions. Separately, the established-channel abstraction is active-network and PQ-capable under its symmetric assumptions, but only after already authenticated fresh directional keys are supplied. Active post-quantum registration/key establishment and end-to-end authentication are false for the current protocol because breaking Ed25519 permits substitution of an attacker-owned KEM key. Loading a hypothetical post-quantum signature assumption would model a different wire protocol.

## Fidelity limits

The following limitations are essential to interpreting the checked results:

- The models are handwritten semantic processes with no code extraction or model-to-Rust correspondence.
- The active registration root has one authenticated static-DH contribution; the exact ordered four-DH-plus-ML-KEM computation and symmetric ratchet initialization remain to be composed.
- Registrations outside the private honest-bundle set return an adversary-selected Phase-2 frame. This abstracts arbitrary frame values but deletes the real server DH/root/encryption path and its chosen-key/oracle effects; no simulation establishes that the abstraction preserves every honest-agreement or confidentiality behavior.
- Beacon finish success and failure have the same public return, so success-dependent application behavior and failure side channels are absent.
- Assigned IDs are adversary-selected but globally uniqueness-checked, abstracting allocator behavior and excluding exhaustion.
- The established-channel model uses fresh per-direction keys with arbitrary unique sequence labels. It does not derive per-sequence key/nonce material, model the shared KDF prefix relation, or prove nonce non-reuse from ratchet state.
- There is no skipped-key cache, out-of-order ratchet derivation, 50-entry capacity, arbitrary compromise, post-compromise healing, persistence, rollback, snapshot fork, concurrent owner, or physical-erasure theorem.
- Typed injective constructors replace byte encodings, Cap'n Proto parsing, malformed-input behavior, allocation failure, and timing.
- Correct application routing and authorization remain external; a cryptographically valid self-signed registration is not proof of application trust.

## Recommended next proof increments

1. Compose registration agreement with one authenticated beacon-to-server sequence-1 reply. Query server-side key confirmation as `ServerReplyAccepted` implying both a unique `BeaconReplySent` and the matching `BeaconCommitted` event.
2. Replace the representative registration root with a reviewed primitive interface for the exact ordered four-DH-plus-ML-KEM hybrid input, preserving the correlated Ed25519/X25519 identity and all-zero DH rejection without attempting to prove those primitives.
3. Close active registration confidentiality with an assumption/interface that genuinely supports the finish decryption oracle, or document a manual intermediate game if CryptoVerif cannot automate the composition.
4. Replace fresh established-channel keys with ordered ratchet continuations and prove key/nonce non-reuse, replay rejection, and past-record secrecy for an arbitrary bounded in-order schedule.
5. Add bounded out-of-order receive state only while every table lookup names a unique immutable version. Keep the exact cache argument in SSProve if reproducing swap/remove state would make the CryptoVerif model ambiguous or unautomatable.
6. Add separately timed reveal oracles for current chains, cached keys, identity keys, and registration secrets, together with executable negative controls for cached-key disclosure, future traffic after current-chain disclosure, and forked state.

The most valuable immediate capstone is registration through the first authenticated beacon reply, because it joins CryptoVerif's strongest automated features: replicated active registration, one-use state, injective agreement, record authenticity, and server-side key confirmation. Full ratchet/cache fidelity should follow rather than block that protocol-level result.

## Tooling and reproducibility

The flake pins CryptoVerif 2.12 from the official source archive with a fixed Nix hash. The standalone target uses a minimal `cryptoverif` development shell and does not invoke the F*/Lean implementation proof toolchain. The current opam package publishes the same release on the [CryptoVerif opam page](https://opam.ocaml.org/packages/cryptoverif/).

Run the isolated suite with:

```sh
make -C beaconcrypt-core verify-cryptoverif
```

The target checks the exact tool version, selects the pinned `default.ocvl` or `pq.ocvl` per model, rejects locally authored equivalences, equations, collisions, and security statements, stores logs outside `proofs/`, exact-matches every complete ordered result line, requires every positive query to prove, and requires the assigned-ID control to reproduce its reviewed failure. CryptoVerif 2.12 can return process status zero for at least some input errors, so checking the output is part of the sound regression gate.
