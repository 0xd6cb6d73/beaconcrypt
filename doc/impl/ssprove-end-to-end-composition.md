<!-- SPDX-License-Identifier: 0BSD -->

# SSProve end-to-end composition investigation

## Status and conclusion

Status on 2026-08-31: SSProve can express the composition needed for beaconcrypt, and the state-separating proof pattern already exists in the literature, but the current repository theorems cannot be combined merely by adding their inequalities. The viable architecture treats PQXDH as a keying package, treats the symmetric ratchet plus record layer as a keyed package, connects them through a private key interface, and proves contextual replacements through one shared end-to-end experiment. [`StateSeparatedComposition.v`](../../beaconcrypt-core/proofs/ssprove/StateSeparatedComposition.v) implements the first single-run structural slice and a security-shaped optional-ciphertext public view with internal finite sampling, while [`StateSeparatedPackageSemantics.v`](../../beaconcrypt-core/proofs/ssprove/StateSeparatedPackageSemantics.v) now certifies the exact authenticated and rejected executions of that linked operation for one call and equates its public finite view and advantage with the direct calculation. This is not yet the repeated-call contextual or computational composition theorem.

The closest computational repository artifact remains [`PqxdhRatchetRom.v`](../../beaconcrypt-core/proofs/ssprove/PqxdhRatchetRom.v), which follows a hidden path from an ordered PQXDH root input through initial chain derivation to one abstract record pad. It selects the second initial half at abstract sequence zero, so it is not already the production registration response: production steps the server's first half at sequence one. It should be refactored into the common KDF and protocol-package nucleus rather than wrapped around the standalone theorems after the fact.

This investigation adds [`ProtocolLabels.v`](../../beaconcrypt-core/proofs/ssprove/ProtocolLabels.v). That module records the two exact production ASCII labels, proves their lengths and inequality, gives the existing Boolean ROM tags a proved-injective interpretation, records the 32/64/76-byte uses, and proves that initial and per-record ratchet derivation share one symmetric domain. `StateSeparatedComposition.v` consumes those exact typed uses without adding a role, session, direction, sequence, or initialization-versus-step KDF tag, and `StateSeparatedPackageSemantics.v` executes the exact linked bodies rather than introducing a second KDF vocabulary. None of these modules proves that the handwritten Rocq literals equal extracted Rust arrays; that representation bridge remains explicit.

No end-to-end computational-security theorem is claimed by this document. The new result is a structural state-machine, single-run key-correctness, and exact one-call semantics milestone, not an unrestricted package-interpreter contextual equivalence, four-corner advantage bound, confidentiality theorem, authenticity theorem, agreement theorem, production record proof, or implementation refinement. The present SSProve results remain bounded finite-game milestones, and production primitive security, implementation refinement, numerical losses, arbitrary schedules, and quantum semantics remain open or assumed as stated below.

## What “end to end” should mean

The useful target is a family of related theorems over one common adversary-facing experiment, not one Boolean theorem named “secure.” The experiment should begin with registration material, run the actual asymmetric two-role PQXDH lifecycle, and expose bounded registration, send, delivery, replay, reveal, and corruption operations. The server derives and uses its candidate chains to seal the response, then commits its counter, peer, and ratchet after successful serialization but before response delivery; the beacon stages its candidate chains and commits them only after the response record opens and the sender and assigned identifiers pass their checks. A dropped response therefore leaves a committed server without a committed beacon, which the game and agreement claims must preserve.

The theorem family should cover:

- active-classical left-or-right confidentiality for uncorrupted challenge sessions under the required challenge exclusions;
- injective accepted-record origin, context binding, and replay rejection for both directions;
- the correctly oriented registration and key-confirmation correspondences;
- key/nonce non-reuse within one authoritative, non-rollback lineage, with explicit KDF-output collision events;
- erasure-conditioned secrecy of already consumed records after an allowed current-state reveal;
- passive-classical security through an explicit forwarding-package embedding of every passive adversary into the active interface, followed by contextual perfect equivalence; and
- the existing passive-quantum classical-query capability result and active-quantum attack as dependency controls, without relabeling either as a QPT or QROM theorem.

Persistence should initially remain outside the cryptographic game behind the documented authoritative-store contract. Including it would require modeling rollback, forks, durable publication, and the fact that snapshot identity and CTX use the same unkeyed BLAKE2b implementation without a textual domain label but with different digest-length parameters: snapshots request 32 bytes and CTX requests 64 bytes. A future shared BLAKE2b package must key its call semantics by `(output_length, input)` and must not impose HKDF-style prefix consistency.

## Existing assets and why they do not yet compose

| Artifact | Reusable result | Missing composition seam |
| --- | --- | --- |
| [`PqxdhRatchetGames.v`](../../beaconcrypt-core/proofs/ssprove/PqxdhRatchetGames.v) | Closed root-to-initial-chain-to-one-record computation, joint Ed25519/X25519 compromise, exact active-quantum negative control, and shared 64/76-byte symmetric prefix behavior. | One session, one fixed record, static forward-or-replace choice, ideal authentication and encryption, and no adversary-facing transcript or state API. Its capstones use a direct finite pushforward rather than an equality to the package interpreter. |
| [`PqxdhRatchetRom.v`](../../beaconcrypt-core/proofs/ssprove/PqxdhRatchetRom.v) | One shared tagged table and a checked reduction from record distinguishing to the exact hidden pad query. | One-bit domains, fixed public DH coordinates, no registration transcript, no delivery or decryption interface, and no numerical hidden-query estimate. |
| [`StateSeparatedComposition.v`](../../beaconcrypt-core/proofs/ssprove/StateSeparatedComposition.v) | A typed `CK || CD` package linked to a private consuming CKEY provider; one-shot role/session checks and cleared tombstones; correct `(L,R)/(R,L)` orientation; authenticated first-response use of the left half at sequence one; exact typed KDF uses; a `unit -> option ciphertext` game interface with one private joint finite-tape sample and no opened-plaintext return; a pure single-run public-view equality to the monolithic calculation; and explicit lifecycle scenario facts. | The record is only a one-bit XOR harness; provenance and accepted root input are parameters; the public API is a fixed honest-delivery call rather than an active network schedule; lifecycle facts are snapshots rather than package reachability; and there is no first-left-half confidentiality bound, four-corner bound, AEAD/CTX/AD composition, production-width representation, or implementation bridge. |
| [`StateSeparatedPackageSemantics.v`](../../beaconcrypt-core/proofs/ssprove/StateSeparatedPackageSemantics.v) | A proof-carrying certificate for the exact linked `RUN` raw code from the empty heap with one indexed value for its sole joint sampler. Authenticated execution returns the direct optional ciphertext and two `Taken` tombstones; rejected provenance returns `None` before sampling or core execution and two `Empty` slots. The authenticated public marginal, uniform finite-source view probability, and distinguishing advantage equal the direct state-separated definitions, while executing the same exact-label KDF bodies. | The evaluator and certificate are intentionally one-call and assumption-safe, not stock `Pr`/`Pr_op` or unrestricted contextual semantics. A second call distinguishes the consuming package from the stateless harness, and active scheduling, repeated sessions, primitive reductions, production widths, and implementation refinement remain open. |
| [`PqxdhHybridSecurity.v`](../../beaconcrypt-core/proofs/ssprove/PqxdhHybridSecurity.v) | One-hidden-contribution robustness for the ordered `DH1 || DH2 || DH3 || DH4 || ML-KEM` combiner shape. | Its ROM types and experiment differ from the protocol ROM, and it does not prove production HKDF real-or-random security. |
| [`RatchetForwardSecrecy.v`](../../beaconcrypt-core/proofs/ssprove/RatchetForwardSecrecy.v) | One erased predecessor-step bad-query bound while revealing the next chain and nonce. | Its chain is sampled independently rather than installed by PQXDH, and it has no session, direction, sequence, receive cache, or multi-step state. |
| [`RecordIntegrity.v`](../../beaconcrypt-core/proofs/ssprove/RecordIntegrity.v) and [`RecordIntegrityBound.v`](../../beaconcrypt-core/proofs/ssprove/RecordIntegrityBound.v) | Query-or-guess classification, cross-context and cross-sequence collision extraction, and the exact one-bit fresh-guess bound. | They assume one combined ideal AEAD-plus-CTX authenticator and therefore cannot yet consume real ratchet material or discharge record-transform composition. |
| [`CtxGame.v`](../../beaconcrypt-core/proofs/ssprove/CtxGame.v) and [`CtxPrivacy.v`](../../beaconcrypt-core/proofs/ssprove/CtxPrivacy.v) | Separate binding/collision and secret-transcript programming hops. | No theorem plugs either hop into the record experiment, and production-width representation and numerical bounds remain open. |
| Lean and F* | Exact deterministic layouts, requests, partitions, and selected state refinements. | Proof terms cannot be imported into Rocq directly, current Lean still has ratchet lifecycle gaps, and direct hax-to-SSProve extraction fails the repository safety gate. |

The immediate lesson is that each computational lemma must be restated over compatible package interfaces or connected to the common experiment by a checked perfect-equivalence lemma. Similar-looking hidden-query events in different table types are not composable security assumptions.

## The SSProve composition pattern

SSProve supplies sequential package linking (`link`, written `∘`), parallel composition (`par`), identity packages, state-separation conditions, an interchange law, contextual advantage lemmas, and triangle inequalities. The pinned [SSProve 0.2.4 KEM-DEM development](https://github.com/SSProve/ssprove/blob/v0.2.4/theories/Crypt/examples/KEMDEM.v) is the closest mechanized template: it moves a keying component and a keyed component between real and ideal worlds while keeping their state separate and connecting them through an explicit key package.

The older state-separating-proofs paper goes further: [Section 6 and Theorem 35](https://eprint.iacr.org/2018/306.pdf) give a multiple-key composition pattern for a forward-secure authenticated key exchange followed by an arbitrary symmetric-key protocol. The theorem is not a ready-made beaconcrypt Rocq library lemma, but its architecture and loss accounting match this task.

The intended linking orientation is schematically `API ∘ ((CK_b || CD_b) ∘ (CKEY || PRIMITIVES))`, where a package on the left imports calls supplied by the provider on its right. `CKEY` and the primitive packages are sibling providers of the keying and keyed packages; primitive calls are not routed through `CKEY`. Further identity packages and interface restrictions will be needed to make the concrete procedure sets line up.

```text
bounded adversary A
        |
adversary-facing registration / send / deliver / reveal wrapper API
        |
  (PQXDH keying package CK_b  ||  ratchet-record package CD_b)
        |                    |              |
        +---- private CKEY --+              |
        |                                   |
        +-- signature | DH | ML-KEM | joint HKDF | AEAD | BLAKE2b providers
```

`CK_b` should own registration identities, one-time-use state, accepted root provenance, separate server and beacon candidates, and their role-specific publication status. `CD_b` should own candidate and live directional chains, counters, skipped receive material, record allocation, acceptance, replay state, and allowed reveal state. `CKEY` should mediate one-way, consuming `PUT`/`TAKE` transfers indexed by session and role: `CK_b` supplies the candidate chain pair, and `CD_b` obtains the raw chains privately without exporting them through the adversary-facing interface. The outer wrapper invokes server publication after successful response sealing and serialization and beacon publication after successful response opening and identifier checks; feeding a later `CD_b` acceptance call back through `CKEY` into `CK_b` would create a cycle outside the stock keying/keyed theorem.

Applying the state-separating theorem requires compatible corruptible keying and keyed games, a valid one-way `CKEY` interface, and aligned partnering, freshness, and corruption conditions. Beaconcrypt's dropped-response behavior and final beacon commit must live in the wrapper rather than being erased by an atomic mutual-install abstraction.

The implemented CKEY slice is intentionally custom. Each role-local slot follows `Empty -> Full(role, session, authenticated provenance, send chain, receive chain) -> Taken`, and `Taken` contains only a cleared tombstone. There is one `PUT` and one destructive `TAKE`; overwrite, retake, wrong-role, and wrong-session attempts reject, and neither reset, fork, public `GET`, nor a keyed-to-keying callback exists. This is not the state-separation paper's repeatable administrative `GET`/`HON` CKEY, so Theorem 35 cannot be cited directly without a compatibility theorem. The production success wrapper also uses the first keyed record before server publication and conditions beacon acceptance on opening that record, which must be preserved by any later repeatable-session construction.

The linked SSProve package is executable and its public interface hides CKEY, raw payloads, setup, seal, open, the complete finite tape, and the opened plaintext. `RUN` accepts only `unit`; the success driver samples `uniform_rom_sample` through one private joint operation and returns `Some ciphertext`, while the known false-provenance branch returns `None` before invoking the core. The challenge remains the hidden `loc_GamePair` world index, and a direct pushforward over the same uniform source defines the optional-ciphertext distinguishing view. `StateSeparatedPackageSemantics.v` now gives this operation a checked finite one-call semantics from the canonical empty heap. Its restricted evaluator supplies one indexed value to the sole joint sampler and executes SSProve's actual raw-code returns and heap operations; local bridges identify staged proof-erased raw projections with the computational fields of the exact linked packages. An indexed certificate carries equality from each complete optional-observation-and-final-heap raw execution to its concrete normal form. Authenticated execution returns the same `Some ciphertext` as the direct observation and the complete `both_consumed_heap`, while false provenance returns `None` before sampling or core execution and retains the complete canonical empty heap; the reportable summaries show the two private slots respectively `Taken` and `Empty`. Hiding the private heap yields pointwise public-observation equality, equality of the uniform finite-source decision probability, and equality of the distinguishing advantage for every deterministic predicate. The executed root, initialization, and step calls retain the distinct `PQXDH_INFO` domain, shared `SYM_RATCHET_INFO` domain, and exact 32/64/76-byte uses.

The assumption boundary remains narrower than stock SSProve contextual reasoning. In pinned release 0.2.4, retaining generic package/raw sampler syntax in an assumption-reported capstone makes `Print Assumptions` traverse a generic distribution proof with the repository-rejected infinite-sum interchange dependency; package validity, `Parable`, association, interchange, `Pr`, `Pr_op`, and stock contextual-advantage paths are therefore not accepted capstones here. The module instead kernel-checks the exact raw execution locally, reduces the indexed certificate to a proof-erased normal form, and states its probability result directly over the finite uniform source. This discharges the one-call package-semantics and finite-probability bridge, but not a repeatable relation: the CKEY-backed package remains tombstoned after that call while the monolithic calculation harness is stateless, so a second invocation distinguishes them. A repeatable indexed-session relation or another assumption-admissible contextual bridge remains prerequisite for the computational hybrid.

The real and ideal components form the four corners `CK₀ || CD₀`, `CK₁ || CD₀`, `CK₁ || CD₁`, and `CK₀ || CD₁`. The proof walks around three sides and uses the fourth corner to restore the real handshake transcript after idealizing the keyed layer:

```text
CK₀ || CD₀  ->  CK₁ || CD₀  ->  CK₁ || CD₁  ->  CK₀ || CD₁
   PQXDH term        ratchet/record term          PQXDH term
```

Schematically, for a bounded execution with `n` session-key/`CKEY` instances, the generic composition has the shape

```text
Adv_e2e(A)
  <= Adv_keying(B0[A])
   + n * Adv_keyed(B1[A])
   + Adv_keying(B2[A]).
```

The two contextual keying terms are intentional. One replaces the key supplied to the real ratchet/record context; the other restores the real key-establishment transcript around the ideal keyed context. They are full multi-session PQXDH/AKE advantages, not the current standalone combiner bound, and `n` counts installed session-key instances rather than records or arbitrary challenge queries. Multiple records under one installed session need a separate record hybrid or a direct multi-record keyed theorem. SSProve's `Advantage_link`, package interchange and identity laws, `Advantage_triangle`, and relational perfect-equivalence judgments are the relevant mechanisms. Heap invariants modeled on KEM-DEM's `heap_ignore`, `triple_rhs`, and `couple_lhs` can relate a monolithic reference state to the separated PQXDH, key-store, and ratchet states.

Signature, DH, ML-KEM, HKDF, AEAD, CTX, forgery, and collision terms arise later when the two keying advantages and the keyed advantage are reduced to primitive games. Checked deterministic representation bridges should be zero-cost perfect equivalences; bridges that are not checked remain explicit trust assumptions rather than invented additive advantage terms.

In pinned SSProve 0.2.4, parallel package composition requires disjoint exported procedure implementations through the `Parable` condition; imported procedures and locations are unioned, and state separation remains an additional proof obligation for the interchange and contextual-equivalence steps. The HKDF calls must not be implemented as independent root, initialization, and step packages: they intentionally share one primitive and, for the latter two calls, one label and input domain.

## Exact domain-separation contract

The production uses two HKDF `info` strings:

```text
PQXDH_INFO       = "BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768"  (46 bytes)
SYM_RATCHET_INFO = "SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305"       (41 bytes)
```

The exact calls that the real-spec and ideal packages must represent are:

| Use | Input key material | Exact `info` | Output |
| --- | --- | --- | --- |
| PQXDH root | `0xff^32 || DH1 || DH2 || DH3 || DH4 || ML-KEM-SS` (192 bytes) | `PQXDH_INFO` | 32 bytes |
| Initial ratchet | PQXDH root (32 bytes) | `SYM_RATCHET_INFO` | 64 bytes, split into complementary 32-byte directional chains |
| Ratchet step | Current chain (32 bytes) | `SYM_RATCHET_INFO` | 76 bytes: record key `[0,32)`, next chain `[32,64)`, and nonce `[64,76)` |

Production performs HKDF-SHA-512 Extract with no explicit salt and then Expand with the listed `info`. The real primitive package should preserve that structure. An ideal random-function or random-oracle hop must be justified by a named HKDF assumption rather than treating label inequality as proof that the real primitive is already independent.

The ideal HKDF interface should be prefix consistent. A convenient representation is a lazy byte stream indexed by an injective encoding of `(IKM, info, byte_index)`; a request for length `L` returns the first `L` bytes. The requested output length must not select an independent table entry. In particular, if an initial-ratchet input equals a later chain input, its 64-byte answer is exactly the prefix of the 76-byte step answer.

`ProtocolLabels.v` connects the two-case finite tag to equality of the two exact handwritten strings, and the closed game now passes explicit `PqxdhRootDerivation`, `InitialRatchetExpansion`, and `RatchetStepExpansion` uses into its ideal KDF calls. The attacker-facing ROM constructors also use the common tag. This is an internal typed-domain connection, not yet a string-indexed-oracle renaming or contextual-equivalence theorem; Phase 1 must prove that stronger bridge for the production-width package.

The proof must track at least the following collision events instead of assuming them away:

- a live chain equals the PQXDH root that was used as the initial symmetric input;
- two directional initial halves collide;
- chains collide across directions, peers, sessions, or generations;
- a step repeats an earlier chain input; or
- projected record-key and nonce pairs collide despite distinct chain inputs.

The exact separation sources are:

| Intended separation | Production mechanism | Modeling rule |
| --- | --- | --- |
| PQXDH root vs symmetric derivation | Distinct exact `info` strings and different structured IKM widths. | Use the two labels from `ProtocolLabels.v` in one joint HKDF package and reduce the real-to-ideal hop to an explicit HKDF assumption. |
| Initial expansion vs record step | No distinct label; same 32-byte input type and same `SYM_RATCHET_INFO`. | Use one prefix-consistent stream and do not add an `Init`/`Step` domain bit. |
| Beacon-to-server vs server-to-beacon | Complementary halves of the one 64-byte initial output. | Prove role selection and chain noncollision; do not add a direction label. |
| Peer identity context | Long-lived identity-bound associated data and authenticated root contributions. | Thread the exact identity pair through record acceptance, but do not treat associated data as a KDF domain or a unique session identifier. |
| Repeated sessions for one identity pair | Fresh root contributions and resulting root/chain state only; associated data is identical across those sessions. | Track cross-session root and chain collisions and replay explicitly; do not add a session label absent from production. |
| Record sequence | Stateful chain iteration, public sequence selection, and the CTX transcript. | Model counters, replay consumption, and state lineage; do not put sequence into the KDF query. |
| Registration key encodings | X25519 uses type byte `0x04` and role bytes `0x80` or `0x81`; ML-KEM uses `0x03`, and the advertised Ed25519 verification key uses `0x01`. | Model signatures only on the X25519 and ML-KEM field encodings and retain the unsigned tagged identity key. These markers are not HKDF labels. |
| CTX vs HKDF | Different primitives and typed fixed-width inputs. | Keep BLAKE2b and HKDF as distinct primitive packages. Production has no CTX ASCII label, so the game must not invent one. |

Associated data is exactly `[0x01 || server Ed25519 public key] || [0x01 || beacon Ed25519 public key] || PQXDH_INFO || SYM_RATCHET_INFO`, totaling 153 bytes. It is the same in both directions, records, and repeated sessions for one identity pair; it binds peer context but supplies no within-pair session separation. Direction, sequence, and numeric sender ID are bound elsewhere. [`ProtocolLabels.v`](../../beaconcrypt-core/proofs/ssprove/ProtocolLabels.v) checks the exact 87-byte label suffix, while the existing F* theorem `associated_data_is_exact` is the deterministic production-layout evidence.

CTX has no textual domain label. Its BLAKE2b-512 input remains exactly `K32 || N12 || AD153 || AEAD-tag16 || LE64(sequence) || LE64(sender_id)`. The semantic direction field in `RecordIntegrity.v` represents directional key selection, not a serialized commitment byte, and its production justification must come from the chain/key provenance theorem.

The three Phase-1 key fields `preKey`, `oneTimeKey`, and `pqKey` are signed separately and have type/role markers but no Beaconcrypt-wide signature prefix. `identityKey` is the advertised tagged verification key and is not itself signed. A computational field-authentication package therefore needs a premise excluding unsafe cross-protocol reuse of the signing key, or the protocol must add and authenticate an explicit signature-domain prefix in a separately reviewed wire-format change. Field-wise origin does not by itself establish whole-bundle coherence or forbid combining valid fields from different bundles; the PQXDH game must retain that behavior and reduce any stronger coherence premise to an explicit invariant or bad event.

## End-to-end package interfaces

The public game interface should be sufficiently expressive to cover the active network rather than selecting `Forward` or `Replace` outside the game. A first bounded interface should include:

- creation of honest beacon registration material and observation of its public bundle;
- submission, replacement, replay, or dropping of an initialization bundle at the server;
- observation, replacement, replay, or dropping of the response;
- challenge-record sending in either direction under equal-length and freshness restrictions;
- delivery of arbitrary frames to an identified receiver and observation of success or failure;
- current-state or long-term-key reveals with explicit timing and challenge exclusions; and
- a final Boolean decision plus a public event trace suitable for agreement and integrity games.

The private `CKEY` interface should remain narrow. The implemented single-run slice associates separate role slots with a bounded session handle and authenticated provenance, accepts each candidate directional-chain pair once, and lets the keyed package consume it through one private destructive `TAKE`. Raw chains and provenance cross this private interface into `CD_b` but are not exported by the adversary-facing API. The multi-session version must replace the bounded Boolean handle with indexed partnered sessions while retaining destructive consumption; a second installation, fork, rollback, or cross-session handle mismatch should remain unrepresentable or set a named bad event.

Confidentiality, authenticity, agreement, replay, non-reuse, and forward secrecy should share this state machine but use separate events and game wrappers. This keeps a confidentiality bit from silently weakening an authenticity claim and lets each final theorem state the primitive assumptions and corruption restrictions it actually needs.

## Proposed game sequence

The first useful capstone is one active-classical registration through the first authenticated response record. It should use the following checked hops:

1. Relate the production-shaped `RealSpec` package to named Lean/F* deterministic contracts for the exact root input, labels, associated data, initial direction split, record transcript, and state transition.
2. Replace verification of the three signed key fields with an ideal field-authentication interface, retain the unsigned advertised `identityKey`, and preserve cross-bundle combinations unless a separate checked invariant or bad-event reduction establishes bundle coherence.
3. Hybridize the four ordered DH values and ML-KEM contribution, then replace the real PQXDH HKDF result through a named combiner/PRF assumption.
4. Pass each accepted candidate root through the one-way `CKEY` interface and prove complementary chain derivation while preserving separate publication times: the server publishes after successful response serialization, whereas the beacon publishes only after authenticated open and identifier checks. This is the missing checked connection between PQXDH and the current ratchet theorems.
5. Replace the shared symmetric HKDF package while preserving exact labels, the 64/76 prefix law, and all input/output collision events.
6. Prove record confidentiality and integrity from the ratchet material under the exact associated data, sequence, sender ID, and directional provenance.
7. Compose ideal AEAD privacy with the CTX secret-transcript programming hop, and keep the base-AEAD integrity branch separate from the CTX same-payload collision branch.
8. Show that the final ideal package reveals only the allowed metadata and satisfies the first-record confidentiality, origin, agreement, and replay events.

The next capstone should generalize the keyed package to an arbitrary bounded schedule with the production receive gap and cache capacity. Multi-session lifting should follow only after the single-session state invariants and collision accounting are stable.

## Deterministic representation bridges

The computational proof should name rather than hide the following cross-prover obligations:

| Contract | Existing evidence | Remaining work |
| --- | --- | --- |
| Exact 192-byte root IKM and ordered five contributions | F* `root_key_transcript_is_exact` and Rust construction/tests. | Relate production-width SSProve encoders to the F* arrays. |
| Exact `PQXDH_INFO` root call | Rust adapter call and extracted constants. | Add a reviewed adapter/request theorem or contract; the root HKDF invocation is outside the current core-owned typed request. |
| Exact symmetric label for initialization and steps | Core-owned `SymmetricRatchetKdfRequest`; current Lean request theorems and historical F* lemmas. | Relate the SSProve literal and package request to the extracted array and adapter response provenance. |
| Exact 64/76 partitions and complementary roles | Current Lean initial response split and step-response facts; historical F* complementary-session theorem. | Prove current two-role initial `KernelRefines` composition and retain the shared-prefix primitive semantics. |
| Exact 153-byte associated data | F* `associated_data_is_exact`. | Thread the same production-width value through PQXDH, AEAD, record, and CTX packages. |
| Exact CTX transcript and collision witness | F* production transcript injectivity and pointwise collision theorem. | Complete the production-width F*/SSProve representation bridge and primitive collision reduction. |
| Send/receive state and erasure | Current Lean send, rollback, cached-open, and control refinement. | Finish future receive publication, cached material-array publication, restoration, initial composition, ideal exhaustion, and adapter-driver refinement. |

Direct hax-to-SSProve import remains rejected because the pinned generated Hacspec aggregate exposes a proof of `False` and the selected array extraction is incomplete. A handwritten model plus reviewed deterministic contracts is safer than importing that boundary until the existing gate is satisfied.

## SSProve-specific constraints

Beaconcrypt pins SSProve 0.2.4. The pinned [SSProve documentation](https://github.com/SSProve/ssprove/blob/v0.2.4/DOC.md) describes package linking, parallel composition, state separation, interchange, advantage reduction, and triangle reasoning. The [SSProve paper](https://eprint.iacr.org/2021/397.pdf) explains the package/relational-logic connection and also documents that some conventional bad-event and efficiency reasoning remains outside the core logic.

The current repository deliberately proves distributional capstones through direct finite pushforwards because the pinned high-level interpreter path can expose an unaccepted infinite-sum interchange dependency. New package-level results must preserve the exact assumption allowlist, avoid that dependency, or justify a reviewed toolchain change; moving to package syntax without a checked semantics-to-probability bridge would not advance the theorem.

The pinned [symmetric-ratchet example](https://github.com/SSProve/ssprove/blob/v0.2.4/theories/Crypt/examples/SymmRatchet.v) is useful for state and forward-secrecy structure, but its scope and assumptions must be inspected rather than imported as a claim about beaconcrypt. The pinned [lazy random-oracle example](https://github.com/SSProve/ssprove/blob/v0.2.4/theories/Crypt/examples/RandomOracle.v) is the appropriate shared-table pattern for the joint HKDF idealization.

[SSProve 0.3.0](https://github.com/SSProve/ssprove/tree/v0.3.0) introduced the nominal package layer, and [0.3.1](https://github.com/SSProve/ssprove/tree/v0.3.1) includes it together with `HybridArgument` machinery and `chTuple`. Those APIs live in the nominal layer, so adopting them is a proof migration rather than a version-pin-only change. An upgrade should be evaluated in an isolated branch against the proof-policy, exact assumptions, and `coqchk`; it is not required for the first composition capstone and should not be mixed silently into the protocol proof.

Standard SSProve games are classical probabilistic programs. They do not model quantum state, QPT execution, or superposition queries, and their advantage semantics do not internally enforce polynomial time. Passive post-quantum security therefore needs a separate quantum-aware framework or a carefully reviewed lifting theorem with QPT/QROM primitive assumptions.

## Implementation sequence and acceptance criteria

### Phase 0: exact shared vocabulary

This phase is implemented by `ProtocolLabels.v` and the refactored finite ROM query constructors. Acceptance requires compilation under the locked Rocq/SSProve shell, a closed assumption report for the label module, exact label lengths and inequality, the shared initial/step domain theorem, the 32/64/76 sizes, the 87-byte associated-data suffix, and `coqchk` coverage.

### Phase 1: one joint HKDF package

Define production-width request encoders, a real Extract/Expand interface, a prefix-consistent ideal stream, and bad events for repeated or colliding inputs and outputs. Replace the incompatible query vocabularies in the PQXDH hybrid, protocol ROM, and ratchet-erasure modules with this common interface. Acceptance requires exact root/symmetric label use, no initial/step tag, and checked contextual equivalences back to each retained standalone capstone.

### Structural lifecycle milestone: implemented one-call seam and semantics certificate

`StateSeparatedComposition.v` implements the affine key-transfer and production-orientation nucleus needed by Phase 2. It constructs typed keying and keyed siblings around a private two-slot CKEY provider, checks one role- and session-bound `PUT`/destructive `TAKE` path with cleared tombstones, requires authenticated provenance on seal and open, steps the server's left initial half at sequence one, and proves a pure single-run equality to the monolithic key calculation. Its first public-experiment redesign makes `RUN` take only `unit`, samples the exact joint finite source internally, returns an optional ciphertext rather than the tape or opened plaintext, and defines a challenge-indexed game pair plus direct optional-ciphertext view. `StateSeparatedPackageSemantics.v` then certifies the exact linked authenticated and rejected one-call executions, including consumed-versus-empty private slots, and proves equality of the authenticated public marginal, uniform finite view probability, and distinguishing advantage with those direct definitions. It does so through locally checked raw projections and a kernel-reduced proof-carrying certificate because the pinned stock package-syntax probability path exposes the rejected interchange dependency. Separate closed snapshots record replay consumption before construction, failed construction without server publication, dropped-response asymmetry, accepted counters, and rejection that terminally aborts a pending beacon while leaving prior server state unchanged. This milestone does not complete a repeated-call contextual relation, Phase 1's production-width HKDF interface, the production-left-half confidentiality reduction, or Phase 2's active adversary experiment and computational hybrid.

### Phase 2: PQXDH-to-first-record composition

Add `CK`, `CD`, and `CKEY` packages for one session and the adversary-facing active registration/response/first-record API. Mechanize the three-side state-separating hybrid and prove confidentiality plus the correctly oriented agreement and active-quantum negative control. Acceptance requires a final bound with named reductions and no ideal-secret premise that bypasses PQXDH.

### Phase 3: bounded ratchet schedules

Generalize `CD` to both directions, arbitrary bounded sends and deliveries, skipped-key caching, replay consumption, allowed reveals, and failure-neutral receive state. Acceptance requires record privacy, injective origin, replay rejection, non-reuse modulo explicit collision events, and one clearly scoped erasure-conditioned forward-secrecy theorem.

### Phase 4: record-transform decomposition

Replace the combined authenticator by separate ChaCha20-Poly1305 and CTX packages. Acceptance requires AEAD privacy plus the CTX secret-input programming term for confidentiality, base-AEAD integrity for ordinary modification, CTX collision resistance only for same-payload distinct explanations, and exact production-width context encodings.

### Phase 5: sessions, losses, and implementation bridge

Lift to bounded multi-user sessions and adaptive scheduling, derive numerical production-width bad-event and multi-user bounds, and complete the reviewed Lean/F*/adapter contracts. Acceptance requires exact query/runtime accounting, explicit corruption exclusions, no-fork/no-rollback premises, and documentation that distinguishes the checked computational theorem from primitive and compiler assumptions.

## Decision gates

- Model the current shared symmetric label by default. Introducing separate initialization and step labels would be a protocol and KAT change, not a proof refactor.
- Decide whether the final record theorem assumes a reviewed composed AEAD-plus-CTX transform or fully mechanizes the separate AEAD, CTX privacy, ordinary-integrity, and collision branches.
- Decide whether the first capstone excludes persistence behind the store contract or expands the experiment to include rollback and both unkeyed BLAKE2b parameterizations, keyed by 32-byte versus 64-byte output length rather than treated as one undifferentiated hash domain.
- Keep the active-quantum break as a required negative result unless the wire protocol gains quantum-secure authentication of every key-establishment field.
- Evaluate an SSProve upgrade separately; do not trade the current exact assumption and kernel-checking policy for convenience without review.

## Defensible current conclusion

SSProve is technically suitable for composing PQXDH with beaconcrypt's ratchet because its package algebra can represent the keying-plus-keyed structure, and the new single-run slice demonstrates a private consuming CKEY seam with production-correct role orientation, lifecycle snapshots, and a checked assumption-admissible one-call execution certificate. This does not by itself satisfy the stock paper theorem's repeatable CKEY or the repository's assumption policy for unrestricted package-level contextual advantage reasoning. The missing work is not a final triangle inequality: it is a repeatable indexed-session relation or another admissible contextual bridge, the common production-shaped adversary experiment, a joint exact-label and prefix-consistent HKDF interface, contextual equivalences for the standalone hops, arbitrary bounded ratchet state, AEAD/CTX composition, production-width bounds, and deterministic representation bridges.

The exact label model and the explicit `kdf_use` arguments in the handwritten games now prevent three common internal modeling errors: treating root and ratchet derivations as unlabeled calls, inventing an initialization-versus-step label absent from production, and describing CTX as if it had a serialized domain string. The stronger byte-string-indexed oracle equivalence and the connection from its two literals and associated encodings to extracted Rust constants remain obligations for the reviewed cross-prover contracts above.
