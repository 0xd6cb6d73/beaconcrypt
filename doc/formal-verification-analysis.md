<!-- SPDX-License-Identifier: 0BSD -->

# What beaconcrypt's formal verification proves

## Purpose and bottom line

This document explains the formal-verification results in plain language. It audits the checked F*, Lean, and ProVerif sources under [`beaconcrypt-core/proofs`](../beaconcrypt-core/proofs), distinguishes generated translation coverage from behavioral refinement, and records which concrete F* theorems still describe the predecessor executor/callback source snapshot.

The short conclusion is:

- The checked F* artifact proves useful universal facts about the selected deterministic Rust snapshot from which it was generated, including exact PQXDH layouts, ratchet control and refinement invariants, the old executor/callback concrete specialization, receive rollback/publication properties, restoration conditions, and the CTX transcript and collision-witness results described below. The production concrete layer has since been defunctionalized, so the old concrete F* theorem names are historical evidence and must not be cited as proofs of the current effect API until extraction and lemmas are regenerated or ported.
- Production stores `ConcreteRatchetKernel`, which directly specializes `RefinedRatchet` to core-owned `RatchetChain` and `RatchetMaterial` values but stores no executor or function pointer. It exposes affine first-order KDF, seal, and open phases that the adapter drives synchronously. This removes the former Charon exclusions and makes the complete default core translatable to Lean. The generated control-plane driver now refines the handwritten `Ratchet.recvStep` directly at the common 50-skipped-key bound: retained skipped keys alone occupy the cache, while the incoming target is consumed separately. The imported Lean effect proofs establish exact structural equations plus a precise kernel relation, an assumed ideal ratchet-step response law, non-exhausted send begin/resume/ideal success plus cancellation, rollback for supplied finite failed-trace witnesses, conditional consistency with ideal opening, generated cached-open construction from an ideal skipped-key lookup, the control-plane half of cached consumption, and conditional cached-key success directly against the ideal model. They do not yet prove effect-level future-receive success, complete the cached material-array publication relation, model ideal send exhaustion, compose initial roles or restoration, or verify the adapter driver.
- The maintained high-level adapter makes the operational kernel and manager affine, returns only inert serialized ratchet views, gates runtime use on established state, and provides `PersistentServer` to fence activation and every accepted or otherwise state-changing result through a monotonic generation CAS while returning rejected receives without a successor or CAS. Its `SnapshotStore` is trusted for payload integrity and provenance as well as linearizable, durable, rollback-resistant head management; snapshots have no cryptographic authentication or encryption. These are reviewed Rust and deployment enforcement mechanisms, not Lean, F*, or ProVerif conclusions. Concrete HKDF and AEAD semantics, output noncollision, faithful adapter interpretation, canonical serde behavior, trusted-store behavior, panic/crash handling, deployment discipline, compiler correspondence, and physical zeroization remain assumptions.
- ProVerif proves secrecy and authentication properties for an active-attacker
  symbolic model of registration and a fixed record-exchange schedule. It also
  demonstrates the expected exposure of cached and future keys after one
  precisely timed beacon-state compromise.
- A dedicated state-neutral receive model reuses one exact symbolic state across repeated rejection, exercises success-only skipped-key publication and the exact 50-slot capacity boundary, and distinguishes rejection non-expansion from compromise of the unchanged live chain before later honest delivery.
- A separate ProVerif negative control deliberately gives one base-AEAD ciphertext and tag two valid openings under distinct keys, nonces, associated-data contexts, and plaintexts.
  The identical multi-opening query is proved unreachable with CTX and is deliberately reachable when the CTX check is removed.
- F* proves the exact 229-byte production commitment transcript layout, injectivity of both `u64` encodings and the complete six-field input, and that two distinct accepted explanations of one fixed payload yield an explicit collision witness for arbitrary pure hash and AEAD-open functions.
- These results do **not** constitute an end-to-end proof of the complete Rust
  application, its adapters, the cryptographic libraries, persistence, or the
  deployed executable. The strongest production claims are conditional on the
  assumptions and implementation-to-model connections listed below.
- The proof does **not** establish general computational or post-quantum security of the primitive implementations.
  Lean now mechanizes factor-one probability reductions from the general ideal-model CTX misattribution event and separately named wrong-sequence, wrong-sender, and cross-session record-opening games to BLAKE2b collision-resistance advantage. It also proves that every honest-run `beaconFinish` outcome classified as post-record admission passed the pinned-sender and nonzero-sequence checks and contains the exact successful `openRecord` call, uses that eliminator for factor-one reordered-first-record and foreign-session transition bounds over a fixed honest run, and proves that frames naming a sender different from the pinned server have exactly zero post-record admission advantage. The lower wrong-sender record game remains a CTX fact below that precheck, “cross-session” means different associated-data bytes and relies on field provenance for its identity/session interpretation, PPT/runtime preservation and the extracted-production refinement remain unmechanized, and BLAKE2b-512 collision resistance remains assumed.
  The protocol still uses classical Ed25519 authentication and is not safe against an active quantum attacker, as the project already records in its [known gaps](rationale.md#known-gaps).

In one sentence: important protocol-control logic and an idealized network
model have been verified, but “beaconcrypt as a whole is formally proven
secure” would be an overstatement.

## How to read a proof claim

A proof never means “nothing can go wrong.” It means:

> If the model accurately describes the relevant implementation, and all stated
> assumptions hold, then the proved conclusion follows.

Four kinds of evidence appear in this repository:

| Evidence | What it establishes | What it does not establish |
| --- | --- | --- |
| F* theorem | A fact holds for all inputs satisfying the theorem's preconditions, for the selected Rust snapshot translated by hax. | Current production behavior after source drift, cryptographic security, adapter correctness, persistence, or behavior outside the extracted functions. |
| Lean theorem | A checked fact holds for the handwritten model or generated Aeneas definition named by the theorem. A refinement theorem additionally connects those layers through its explicit relation and effect laws. | Semantics or premises not covered by that theorem, the external adapter interpreter, or the mere fact that source translated successfully. |
| ProVerif result | No attack exists, or a stated attack does exist, in the handwritten symbolic protocol and ideal-cryptography model. | Computational security or automatic correspondence with the full Rust program. |
| Rust regression, known-answer, or Wycheproof test | The tested implementation behaves correctly on finitely many concrete examples. | A universal proof for all possible inputs and executions. |
| Assumption or refinement obligation | A fact needed to connect one verified layer to another. | Nothing by itself; it must be justified by implementation review, testing, another proof, or an operational control. |

Some terms used below are worth defining:

- **F*** is a programming language and proof checker. Here, hax translates a
  selected subset of the Rust protocol core to F*, and handwritten lemmas state
  facts about those translated functions.
- **Lean** is the proof checker used for the newer refinement path. Hax, Charon, and Aeneas translate the default core to Lean; a handwritten ideal ratchet states the desired behavior, and separate theorems must relate generated transitions to that model.
- **ProVerif** is an automated analyzer for protocol models. Here it explores
  what an all-powerful network attacker can do when cryptographic operations
  obey idealized rules.
- **Symbolic model** means cryptography is represented by perfect mathematical
  building blocks. For example, a symbolic signature cannot be forged and a
  symbolic hash never collides unless an equation explicitly permits it.
- **Computational security** is the corresponding real-world claim: an attack
  may be mathematically possible but should require infeasible time or have
  only negligible probability. The ProVerif model does not calculate such
  probabilities or reduce its claims to the security of the real algorithms.
- **Adapter** means the production code around the verified pure functions: it
  calls cryptographic libraries, parses and serializes data, updates maps, and
  persists state. A **refinement obligation** is a fact that this code must
  preserve for a model-level result to describe the running system.
- **PQXDH** is the hybrid registration/key-establishment protocol used here. It
  combines classical X25519 exchanges with an ML-KEM post-quantum shared secret.
- A **key-derivation function (KDF)** turns shared secret material into the
  separate keys a protocol needs. **Authenticated encryption (AEAD)** both
  hides a plaintext and detects unauthorized modification, assuming its key
  and nonce are used correctly.
- **Correspondence** means that if a later event occurs, an earlier matching
  event must have occurred. For example, “message accepted” implies “the same
  message was sent.”
- **Injective correspondence** additionally makes this matching one-to-one. One
  send cannot justify two accepted receives in the modeled event structure.
- **Precondition** is something a theorem requires rather than proves.
- **Invariant** is a rule that is true before a state transition and is proved
  to remain true afterward.
- An **honest** party follows the modeled protocol and has not had the secrets
  excluded by that model's compromise rules disclosed.
- A **trace** is one possible sequence of modeled sends, receives, state
  changes, and attacker actions. ProVerif searches across such traces.
- **Commit** in the workflow means finalizing and publishing pending state. A
  cryptographic **commitment** is different: here it is a digest intended to
  bind record fields so they cannot later be opened as different values.
- **Forward secrecy** means that a later state compromise does not reveal an
  earlier message. The result here applies only after that message's exact key
  material is no longer present.
- **Post-compromise security** means recovery of security for future traffic
  after a compromise. Beaconcrypt's symmetric ratchet deliberately does not
  provide it.

## What is connected to production source

The proof paths have different source connections:

```text
selected deterministic beaconcrypt-core Rust
              |
              +---- hax F* extraction ---- generated F* definitions
              |                                      |
              |                                      +---- handwritten F* lemmas
              |
              +---- Charon/Aeneas Lean extraction ---- generated Lean definitions
              |                                              |
              |                                              +---- handwritten ideal model
              |                                                   and refinement lemmas
              |
              +---- hax ProVerif extraction ---- generated data-type declarations
                                                 plus three trusted handwritten
                                                 simplified function definitions
                                                           |
                                                           +---- handwritten
                                                                ProVerif crypto,
                                                                processes, events,
                                                                and queries

full application adapters, real crypto, wire formats, persistence, FFI
              |
              +---- outside the formal proof; required to match the models
```

The F* path has the stronger source connection only when its generated definitions are current: the build selects exact Rust items, regenerates their F* definitions, and checks the handwritten lemmas without lax checking. The tracked concrete F* lemmas currently describe the predecessor executor/callback API, so their mathematical results remain auditable but their production-refinement claim is suspended until they are regenerated or replaced for the phase API.

The Lean path translates the default core without module exclusions. Its handwritten symmetric-ratchet driver is the ideal specification, `RatchetRefinement.lean` connects extracted control-plane behavior directly to `Ratchet.recvStep` at its 50-skipped-key bound, and the imported `RatchetEffectRefinement.lean` connects a substantial part of the defunctionalized concrete lifecycle to the same model. That checked bridge covers the exact kernel relation, an assumed ideal KDF-response law, non-exhausted send begin/resume/ideal success plus cancellation, supplied finite failed-trace witnesses, conditional open-reply consistency with ideal decryption, generated cached-open construction from the kernel relation plus an ideal skipped-key lookup, the control-plane half of cached consumption, and conditional cached-key success; structural equations separately cover exhaustion and advanced-state return for either seal result. It does not yet cover effect-level future-key success, prove the material-array half of cached publication, compose initial role kernels or restoration, verify the real synchronous adapter driver, or model ideal send exhaustion. “Lean can translate it” and “Lean proves a named transition refines the ideal model” remain deliberately separate claims.

### Native Lean computational reduction for modified CTX

The imported [`CtxReduction.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxReduction.lean) module states a concrete misattribution game over the handwritten ideal PQXDH record layer. The adversary returns an arbitrary raw wire payload and two well-formed explanations containing message material, record associated data, and plaintext. A win requires the real `Pqxdh.openRecord` parser, CTX check, and deterministic AEAD-open call to accept both explanations while the explanations differ.

The model theorem `Pqxdh.openRecord_double_opening_yields_ctx_collision` proves pointwise that every win exposes two unequal values of `ctxPreimage` with equal `c.blake2b` outputs, using the Poly1305 tag parsed from the shared payload. The game-level theorem `ctxMisattributionAdvantage_le_blake2b_cr` turns that witness into a VCVio `CollisionResistance.CRAdversary` and proves a factor-one bound from the CTX misattribution advantage to the collision-resistance advantage of the same pure `c.blake2b` function. There is no additive loss and no AEAD-security or random-oracle assumption in this reduction; determinism of the ideal `aeadOpen` function is enough to show that equal contexts cannot explain the payload as two different plaintexts.

The relabelling specialization constructs an honest `sealRecord` under a source explanation and asks whether it opens under a distinct target context. `ctxRelabelAdvantage_le_blake2b_cr` proves the same factor-one bound for that event, while the wrong-sequence, wrong-sender, and cross-session corollaries expose the exact collision produced by acceptance under each changed field.

This is a computational reduction for an ideal-model component, not a proof of BLAKE2b-512 collision resistance, transformed-AEAD privacy, ordinary ciphertext integrity, or end-to-end protocol security. VCVio's unkeyed `CRAdversary` does not carry a machine-checked PPT cost, and the proof does not yet connect `Pqxdh.ctxPreimage` and `Crypto.blake2b` to the Aeneas-extracted production transcript builder and adapter hash call. Those complexity and production-refinement obligations remain explicit.

The older imported [`VCVioFeasibility.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/VCVioFeasibility.lean) module remains supporting evidence. It specializes generic bounded adaptive lazy-random-oracle commitment results to the extracted 229-byte transcript field and a 512-bit output, and it checks basic linked consuming-key state behavior. Those ROM and handler pilots are not used to prove the native standard-model CTX theorem and are not a roadmap for reproducing the SSProve branch. The revised direction and remaining bridges are recorded in [`vcvio-feasibility.md`](impl/vcvio-feasibility.md).

The generated F* view exposes some record constructors and fields that are
private in Rust, so a lemma can construct states that ordinary Rust callers
cannot. The composed handshake theorem explicitly calls the authentication
transition, but an isolated field-preservation lemma is not by itself proof
that a value came through the production validation path
([exception](../beaconcrypt-core/proofs/trusted-boundary.md#generated-code-exceptions)).

### Defunctionalized production effect interpreter

Lean itself can represent functions. The practical blocker was the pinned Rust-to-Lean path's treatment of Rust `fn` fields and callback-bearing generic APIs. The production core now defunctionalizes that boundary: instead of storing an executor or calling a callback, it returns one of a finite set of typed phase values. Each phase owns the continuation and exact request, exposes only borrowed inputs, and is consumed by `resume`, `finish`, `cancel`, or `reject`. This is an ordinary first-order state machine that Charon/Aeneas can translate.

| Operation | Core phase path | Exact adapter interpretation | Normal-return state rule |
| --- | --- | --- | --- |
| Initial ratchets | `start_initial_ratchet_kdf` or a role/candidate-specific start → `InitialRatchetKdfPending` → `resume_initial_ratchet_kdf` | [`finish_initial_ratchet_kdf`](../beaconcrypt/src/ratchet.rs) passes the core-owned `{ root, SYM_RATCHET_INFO }` request to `initial_ratchet_hkdf`, wraps the 64-byte result in `InitialRatchetKdfResponse`, and resumes the role-ordering continuation. | The core alone splits the two 32-byte halves and constructs complementary send/receive kernels; dropping the pending phase constructs no kernel. |
| Send | `begin_send` → `SendKdfRequested` → `SendKdf::resume` → `SendSeal::finish` | [`encrypt_message_with_ratchet`](../beaconcrypt/src/ratchet.rs) moves `SealFrameContext` into the phase, calls `ratchet_hkdf` on the exact request, then calls `seal_frame` with the phase's material, sequence, and same context. | Exhaustion or pre-KDF cancellation returns the exact entry kernel. KDF resume advances the chain and counter; `finish(Some(frame))` and `finish(None)` both return that advanced kernel, so failed sealing still consumes the one-use key. |
| Receive | `begin_receive` → zero or more `ReceiveKdfRequested` phases → `ReceiveOpenRequested` → `ReceiveOpen::finish` | [`decrypt_message_with_ratchet`](../beaconcrypt/src/ratchet.rs) performs empty/parse/sender/length checks first, moves `OpenFrameContext` into the phase, executes each exact `ratchet_hkdf` request, then calls `open_frame` with the selected material, sequence, and same context. | Admission/internal rejection, KDF cancellation, explicit open rejection, or `finish(None)` returns the exact entry kernel. Each future derivation changes only private staged state; `finish(Some(plaintext))` atomically publishes the prevalidated cached removal or final chain/skipped-cache/control delta and consumes the target. |

[`RatchetEffect.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RatchetEffect.lean) checks structural laws against the generated phase definitions: exact initial and step requests, role-specific starts, core response partitioning, context preservation, exact entry recovery on cancellation/rejection/failed open, advanced-kernel return for either send result, and successful publication returning the same plaintext. The imported [`RatchetEffectRefinement.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RatchetEffectRefinement.lean) adds a checked semantic bridge. Its `KernelRefines` relation equates the concrete and ideal send sequence and chains, imports the receive-control refinement, relates every live concrete cache slot bidirectionally to one ideal skipped key, and requires slots above the live prefix to be empty. `ResponseRefines` states the assumed external KDF law exactly: parsing a typed 76-byte reply yields `cr.kdfChain chain` and `cr.kdfMsg chain`. Under that law, Lean proves non-exhausted send begin, KDF resume, ideal send success, and cancellation; receive KDF cancellation, open rejection, and open failure; and exact entry recovery plus refinement preservation for any supplied finite `ReceiveFailureTrace` witness. `OpenReplyRefines` conditionally relates a reply to the exact phase-selected material and `cr.dec`. Given `KernelRefines`, target/index equality, and an ideal skipped-key lookup, `begin_receive_cached_refines` proves that generated `begin_receive` produces the cached open satisfying `CachedOpenRefines`. That relation gives exact material selection and ideal success against cached `recvStep`; concrete `finish(Some plaintext)` returns the same plaintext and matches that ideal result when supplied the generated publication equation. `finish_receive_with_removal_consumed_refines` proves the control state after consumption refines ideal skipped-key filtering, while the full concrete post-state satisfies `KernelRefines` only when additionally supplied `CachedPublicationRefines`, whose material-array swap/empty-suffix part remains unproved.

The generic context is opaque to the core and may contain non-`'static` references. The phase can establish that the same value is threaded to the final request, but it cannot inspect or prove Cap'n Proto parsing, associated-data construction, plaintext/ciphertext ownership, CTX commitment checking, or the libsodium call. Separate `InitialRatchetKdfResponse` and `RatchetKdfResponse` types prevent cross-phase 64/76-byte response confusion, but neither type proves that its bytes came from HKDF or that the adapter answered the request faithfully.

`RatchetManager` holds its non-clonable kernel in a private `Option` slot. A high-level call removes the kernel, drives the phase to completion synchronously, and returns the resulting kernel to the empty slot; phases are stack-local and never serialized. This preserves the public Rust/binding APIs, Cap'n Proto record layout, and the five persisted fields `send_key`, `recv_key`, `send_ctr`, `recv_past`, and `recv_ctr`. Restoration reconstructs direct chains and cached material without rebinding an executor.

The rollback theorem is intentionally about normal returns. If HKDF, commitment, AEAD, allocation, serialization, or the driver panics after the kernel is removed, unwinding drops the owned phase and its secrets but leaves the slot empty, so later access fails closed rather than guessing whether to roll back or commit. Crash recovery, panic atomicity, concurrency around an in-flight manager, and durable publication are adapter/deployment obligations; persisted server output remains subject to `PersistentServer` CAS rules.

Secret-bearing requests, responses, chains, keys, nonces, and material use `ZeroizeOnDrop`, and dropping a continuation recursively drops its owned secret fields. The adapter also wraps variable-length HKDF output in `Zeroizing` and creates libsodium key/nonce values only for the immediate primitive call. Lean reasons about logical ownership and unavailability, not compiler-preserved physical erasure, stack/register copies, allocator behavior, or copies retained inside external libraries.

The remaining Lean refinement obligations are deliberately narrower:

- Complete `CachedPublicationRefines`: `finish_receive_with_removal_consumed_refines` already proves the control-plane filtered-cache relation, but the generated material-array swap-remove must still preserve the bidirectional concrete-slot/ideal-filtered-list relation and the empty suffix required by `KernelRefines`.
- Define and prove the staged invariant for future receives, induct over each `ReceiveKdf::resume` under `ResponseRefines`, and prove that successful publication matches the ideal future branch.
- Add a bounded ideal send attempt that represents `u64::MAX` exhaustion, then relate generated `SendExhausted` to that result; the existing `Ratchet.sendStep` is total over `Nat` and only the non-exhausted production branch currently refines it.
- Compose the structurally proved 64-byte initial response split and beacon/server offsets into opposing `KernelRefines` states, then connect authenticated PQXDH establishment to that paired-session result.
- Prove that checked restoration establishes `KernelRefines` under its canonical provenance premises.
- Verify a first-order model of the synchronous adapter loop or retain an explicit reviewed-driver assumption that it invokes only the requested effect once, supplies the matching typed result, passes the exact final context to `seal_frame`/`open_frame`, and always reinstalls the returned kernel on normal completion.
- Lift the direct bound-50 control refinement through the effect-level future KDF staging and publication path. The control theorem already agrees with `Ratchet.recvStep`; the remaining obligation is to relate each typed KDF response, the separately consumed target, the staged 50-entry skipped cache, and the published concrete kernel.

The imported theorems therefore verify a substantive send, rollback, open-reply, and conditional cached-success slice of the current effect architecture, but they do not yet prove that all of `beaconcrypt-core` or its adapter interpreter refines the ideal driver.

### Predecessor F* ratchet module boundaries and measured dependency surface

In the predecessor F* snapshot, an isolated interface prototype found that the generated PQXDH implementation directly needs exactly eight declarations from `Beaconcrypt_core.Ratchet`: `v_RATCHET_CHAIN_SIZE`, `v_SYM_RATCHET_INFO`, `t_RatchetChain`, `impl_RatchetChain__from_bytes`, `t_SymmetricRatchetKdfRequest`, `impl_SymmetricRatchetKdfRequest__new`, `t_ConcreteRatchetKernel`, and `impl_ConcreteRatchetKernel__new`. The maintained historical [`Beaconcrypt_core.Ratchet.fsti`](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Ratchet.fsti) exposes exactly that surface, so ordinary checking of that snapshot does not expose the ratchet's logical state, generic refinement machinery, concrete record representation, or unrelated operations to PQXDH.

In that checked snapshot, the source and generated modules follow the dependency direction `Ratchet.Control` → `Ratchet.Refined` → `Ratchet` → `Pqxdh`. `Ratchet.Control` owns logical counters, cache admission, send/receive transitions, restoration, and peer-local helpers; `Ratchet.Refined` imports that logical layer and binds it to generic chain and material values; `Ratchet` imports the refined layer and owns the KDF types plus the executor-bearing concrete kernel; and PQXDH imports only the narrow concrete facade. The current Rust and generated Lean trees additionally separate `ratchet::concrete` and `pqxdh::concrete`; the frozen F* modules are not a module map of the current affine effect API.

Each generated predecessor ratchet layer has an `.fsti` that exposes only declarations needed across the next stable boundary. Proof implementation visibility is deliberately narrower still: [`Beaconcrypt_core.Ratchet.Lemmas.fsti`](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fsti) exports no proof declarations, while the PQXDH lemma implementation explicitly uses F* friend access to the ratchet implementation and lemma module. The ratchet lemma implementation likewise uses friend access to the hidden Control, Refined, and concrete representations, so representation-dependent reasoning remains available to these named proof implementations without becoming a general downstream proof API.

The narrow interface also exposed an equality detail in the generated PQXDH type `InitialRatchetChains`: an ordinary generated record requests decidable structural equality for its fields, but an abstract `RatchetChain` does not promise that operation. Marking only this extracted record `noeq` suppresses the generated decidable-equality requirement and lets `RatchetChain` remain abstract; it does not remove F* propositional equality and does not change the Rust representation or runtime behavior.

With proof-library caches warm, repeated direct per-module checks measured medians of 0.82 seconds for `Beaconcrypt_core.Ratchet` and 0.89 seconds for `Beaconcrypt_core.Pqxdh`. In the isolated prototype, three paired forced PQXDH rechecks averaged 8.187 seconds against the broad implementation and 8.070 seconds against the eight-declaration interface, a reduction of 0.117 seconds or 1.43 percent; the median reduction was 0.09 seconds or 1.1 percent. A 73.05-second cold run was dominated by proof-library loading, so it is not evidence of a comparable cold-build improvement from the interface split. The measured benefit is deliberately modest: the main gain is preventing implementation details from becoming PQXDH dependencies.

The ProVerif branch is parallel to, not generated from, the F* branch. Hax emits
the selected data-type declarations, but its three relevant operations—
registration-ID construction, root-input construction, and associated-data
construction—use trusted handwritten simplified function definitions embedded
in the Rust source. The root-input definition models only the successful path;
it omits Rust's all-zero-DH error, which F* checks separately.
The wire protocol, ideal cryptographic rules, honest participants, replay
owner, compromise schedule, proof-bookkeeping events, and security questions
are also handwritten. This boundary is described in the
[Stage 7 implementation record](impl/formal-verification-stage-7.md#generated-proverif-boundary)
and the [generated-code exceptions](../beaconcrypt-core/proofs/trusted-boundary.md#generated-code-exceptions),
and the resulting rules are visible in
[`lib.pvl`](../beaconcrypt-core/proofs/pro-verif/extraction/lib.pvl#L347-L357).
The F* byte-layout theorems support human review of those three definitions,
but there is no machine-checked theorem connecting the two branches or showing
that the complete ProVerif process is the complete production application.
The generated ProVerif file also contains permissive constructors, arbitrary
default values, conversion helpers, and error plumbing that do not establish
valid Rust construction. The gate checks that the handwritten model never uses
those defaults or reverse converters and uses only the allowlisted root-input
converter. This containment is a structural check, not a semantic source proof.

## Protocol walkthrough

The protocol has two roles: a **beacon** (the device registering) and a
**server**. The beacon constructs an `InitKex` registration message containing
its public identity and one-time key-establishment material; the server checks
that material, rejects a previously consumed registration identifier, and
assigns the beacon a numeric key ID. Both sides combine four X25519 shared
secrets and one ML-KEM shared secret into an ordered **root-key input**, then
use a key-derivation function to obtain the same root and two directional
message-key chains. The server returns the assigned ID inside the first
authenticated, encrypted response, and each side publishes the new peer only
after its checks succeed.

After registration, each direction uses a **symmetric ratchet**: a one-way chain advances to new material for each sequence number. If sequence 3 arrives before sequence 2, the receiver may derive both materials, use sequence 3, and temporarily cache sequence 2 for delayed delivery. The cache is bounded to 50 entries, and a future target is consumed separately rather than occupying a cache slot. The current core emits exact typed derivation requests and keeps all uncommitted receive state inside affine phases; the adapter computes each response. Lean proves that the generated control driver refines the ideal receive step directly at the 50-skipped-key bound, plus non-exhausted send begin/resume/ideal success and cancellation, rollback for supplied finite failed-trace witnesses, conditional consistency with ideal opening, generated cached-open construction, the control-plane half of cached consumption, and conditional cached success; structural equations separately cover exhaustion and either seal result. Opposing-role composition, effect-level future receive publication, cached material-array publication, restoration, ideal send exhaustion, and adapter interpretation remain obligations distinct from HKDF semantics, output noncollision, secrecy, ephemeral libsodium conversion, and deployed bytes.

Production parses the frame, checks the sender and minimum protected-payload length, and then performs receive admission. For a correctly shaped future frame, the receiver privately derives through the attacker-selected sequence while leaving the live state untouched, stages only skipped keys, and keeps the target material separate. It checks the commitment and AEAD against that private target before publishing anything. A failed open drops the candidate and returns the complete entry state; a successful open publishes the final chain and skipped keys while consuming rather than caching the target. Retrying a forged future frame therefore repeats bounded private derivation from the same live state.

## Concrete properties proved by F*

### Commitment transcript and collision witness

The production BLAKE2b wrapper delegates byte construction to the selected `no_std` [`build_commitment_transcript`](../beaconcrypt-core/src/commitment.rs) helper.
The checked [`Commitment.Lemmas.fst`](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst) module proves that its 229 output bytes are exactly the 32-byte key, 12-byte nonce, 153-byte associated data, 16-byte AEAD tag, little-endian 64-bit sequence, and little-endian 64-bit sender ID in that order.
The maintained Lean refinement now independently proves that the current Hax-extracted commitment integer helper returns the ideal model's `LE64` representation for every `u64`, reusing the separately checked registration-identifier encoder refinement; transcript assembly, adapter hashing and field provenance, Hax/Rust semantic preservation, and compiler correspondence remain separate obligations.
It also proves `encode_u64_le_is_injective` and `production_commitment_input_is_injective`, so equality of two production transcript arrays implies equality of all six semantic inputs.

The theorem `ctx_distinct_openings_imply_hash_collision` quantifies over arbitrary pure hash and AEAD-open functions and fixes one ciphertext core, transmitted tag, and outer commitment for both openings.
If two accepted explanations differ in key, nonce, associated data, sequence, sender ID, or plaintext, it machine-checks an explicit witness consisting of two distinct 229-byte inputs with equal hash outputs.
The theorem permits unequal-key and unequal-context multi-openings by the base AEAD rather than assuming those openings away.
If all transcript inputs are equal, injectivity fixes their semantic fields and the same pure open function on the same ciphertext and tag fixes its result, so a different accepted plaintext is impossible.

This proves the pure builder's source-level layout and pointwise collision implication after hax translation.
The production wrapper's typed call connects its `key`, `nonce`, `ad`, `tag`, `seq`, and `kid` values to that helper.
The libsodium BLAKE2b call, successful slice-to-array conversions, input provenance, hax/compiler correctness, zeroization, and correspondence to machine code remain outside F*.

### PQXDH registration and key establishment

The PQXDH lemmas are checked against the generated Rust translation in
[`Beaconcrypt_core.Pqxdh.Lemmas.fst`](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst).

| Area | Exact machine-checked result | Important qualification |
| --- | --- | --- |
| Public-key encodings | The Ed25519, ML-KEM-768, and X25519 type markers and the two X25519 role markers have the documented distinct byte values. Each encoding preserves the key bytes exactly; encoder/decoder pairs round-trip; a prekey encoding is rejected as a one-time key and vice versa ([marker and role lemmas](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L74-L178)). | Signature verification occurs outside the core. The theorem proves what bytes are tagged and decoded, not that Ed25519 authenticated them. |
| Honest `InitKex` construction | A value made by `beacon_start` is accepted by `validate_init_kex` and yields exactly the four original public keys and expected pending state ([theorem](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L180-L207)). | This is a constructor/validator round trip, not an attacker-controlled wire theorem and not a proof that only one bundle can ever be emitted. |
| Server trust-anchor binding | `BeaconFresh` stores the expected server public key and numeric identity-key ID together. `beacon_start` preserves both fields in `BeaconInitSent`; a different response public key is rejected; a successful finish copies both fields into the candidate and derives associated data from the stored public key; post-open authentication rejects a different sender ID; and commit preserves the pair in `BeaconEstablished` ([state preservation](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L180-L221), [finish and authentication](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L482-L634), [acceptance-implies-agreement theorem](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L764-L816)). | The constructor must still receive the authentic compiled-in binding, and the adapter must truthfully pass the parsed response key plus the sender ID and assigned-ID prefix returned by the successful initial open. The acceptance theorem assumes no stored/accepting binding equality: successful key and ID checks derive both fields' equality with the accepting server candidate. The proof prevents later mutable-map replacement from redefining the expected binding; it cannot repair a trust anchor replaced before construction. |
| Registration identifier | The identifier is exactly the fixed-width beacon identity followed by the one-time X25519 key ([theorem](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L223-L230)). | This avoids a hash-collision assumption for the encoding. Freshness, one-time use, persistent insertion, and absence of rollback are not established by this theorem. |
| Root-key input | When none of the four 32-byte DH outputs is the all-zero array, the 192 bytes are exactly `0xff` repeated 32 times, followed by DH1, DH2, DH3, DH4, and the ML-KEM shared secret in that order. If any DH output is all zero, construction returns `InvalidDhOutput` ([theorems](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L232-L338)). | The KEM secret is not required to be nonzero. This proves the input to later key derivation, not the HKDF implementation or its output. |
| Honest-role input and root agreement | If the adapters supply byte-identical DH1 through DH4 values and byte-identical ML-KEM secrets, the two roles return the same root-input result. `equal_root_inputs_derive_same_fixed_root` and `authenticated_registration_derives_common_fixed_root` then prove equal 32-byte roots when the authenticated beacon candidate and pending server registration expose equal verified transcripts to the same fixed pure root function ([lemmas](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst)). | X25519 and ML-KEM agreement are preconditions. The bridge does not prove HKDF: production must faithfully and totally apply HKDF-SHA-512 to the exact transcript with `PQXDH_INFO`. |
| Associated data | The 153 bytes are exactly the tagged server identity, tagged beacon identity, `PQXDH_INFO`, and `SYM_RATCHET_INFO`, in that order. Equal role identities give equal associated data ([theorems](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L355-L478)). | The adapter must actually supply the returned bytes to authenticated encryption (AEAD). The theorem does not prove AEAD security. |
| Predecessor concrete ratchet composition | The checked F* artifact's `initial_ratchet_chains_use_exact_root_and_directions` proves that the old core-created initial request contains the exact root and `SYM_RATCHET_INFO` and that its two fixed 32-byte halves are complementary. Its concrete role-kernel, directional-agreement, and public seal/open theorems establish the corresponding executor/callback snapshot properties ([lemmas](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst)). | These theorems predate `InitialRatchetKdfPending`, typed responses, and the send/receive phase API. They remain proof-design evidence but are not a refinement proof of the current Rust. Current phase composition, HKDF/AEAD semantics, adapter fidelity, compiler correspondence, peer selection, publication, and rollback prevention remain obligations. |
| Authenticated response IDs | The assigned-ID binding is the exact eight-byte little-endian encoding of the `u64`. The authentication transition requires both the initial frame's sender ID to equal the candidate's pinned server identity-key ID and the assigned-ID bytes to equal the candidate binding; either mismatch is rejected, and commit preserves the complete server binding plus assigned ID ([theorems](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L549-L634)). | The numeric sender and eight assigned-ID bytes must really be the values returned by a successful initial AEAD open. F* accepts those values as inputs; it does not prove their wire or AEAD provenance. |
| Replay status and pending acceptance | `Fresh` is admitted, `Consumed` is rejected, and a fresh successful `server_accept` returns the exact pending values without advancing the live core counter ([theorems](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L636-L686)). | The persistent set lookup and insertion are outside F*. The adapter supplies the `Fresh` or `Consumed` classification. |
| Allocation and server transaction shape | The next key ID is mathematical increment by one or explicit exhaustion at `u64::MAX`; it cannot wrap. A different server binding and an adapter-reported occupied ID are rejected. An available ID produces the exact proposed state and peer; pure commit returns that proposal and pure abort returns the previous state ([theorems](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L688-L762)). | The adapter supplies truthful availability. F* proves return values, not atomic mutation of the production counter, map, ratchet, or persistent storage. |

In plain language, these results remove ambiguity from the bytes both sides are
supposed to use, reject several dangerous boundary cases instead of wrapping or
silently continuing, and show that the pure state machine returns the intended
pending or committed values. They matter because swapping a key role, changing
an identity, reusing a registration, or assigning a different ID should change
or stop the run. They do not establish that the surrounding code performed the
cryptography, database operation, or state publication correctly.

For the server trust anchor specifically, the deployment assumption now enters the verified state once rather than being re-created by a peer-map lookup during finish. The F* lemmas follow the original public-key/ID pair from fresh state through `BeaconInitSent`, candidate, authenticated response, and established state. A focused theorem assumes no equality between that stored pair and an accepting server candidate; when response-key preparation and sender-ID authentication both succeed, it derives equality of both fields throughout those states. Production still has to construct the initial pair from the intended compiled-in values and accurately report the response fields authenticated by the initial open.

The broadest PQXDH theorem is
[`conditional_honest_run_correspondence`](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst#L818-L941).
It assumes a non-exhausted counter, a registration whose beacon identity matches the pending beacon state, four valid and pairwise-equal DH results, an equal KEM secret, `Fresh` replay status, an `Available` next ID, and field-by-field equality between the accepting server binding and the binding already retained in beacon state so that it can state a complete honest successful run. The response public key and successfully opened sender ID are still checked by the beacon transitions, and this broad theorem invokes the separate acceptance-implies-agreement result in its successful server-candidate branch. The production adapter, not either theorem, must authenticate the wire provenance of those values. Under those conditions the broad theorem proves equal root inputs, equal associated data, equality of both server-binding fields, the same assigned peer ID and binding bytes, complementary ratchet directions, successful binding authentication, and matching committed core peer data.

That theorem describes the result after inputs have already been validated and both parties follow the protocol. The newer `authenticated_registration_derives_common_fixed_root`, `concrete_initial_kernels_are_complementary`, and `concrete_initial_kernels_are_reachable` lemmas continue the composition from authenticated equal root-input transcripts through a fixed pure root derivation to complementary reachable production-specialized kernels. They still do not verify signatures, wire provenance, X25519/ML-KEM or HKDF semantics, AEAD, set/map lookups, actual network behavior, or publication. These results should not be read as an active-attacker handshake proof; that is the separate ProVerif layer.

### Symmetric-ratchet control state and predecessor F* artifact

The current ratchet has a logical control layer, a generic refined layer, and a production-facing `ConcreteRatchetKernel`. `RefinedRatchet<SendChain, ReceiveChain, Material>` owns control, both live chain values, and a fixed `[Option<CachedReceiveKey<Material>>; 50]` array; the concrete kernel specializes those parameters directly to `RatchetChain` and `RatchetMaterial` and contains no executor. Each cached record holds both `sequence` and `material`; future receive phases stage skipped records and a separate target privately, and only successful open publication changes the live cache.

The detailed theorem list below audits the last checked F* concrete artifact, whose `ConcreteRatchetChain` stored a function executor and whose public operations accepted pure seal/open callbacks. Its generic control, cache, and preparation results remain useful proof design evidence, but every item mentioning `concrete_reachable`, executor preservation, `concrete_seal_next`, `concrete_open_and_finish`, or callback outcomes describes that predecessor Rust snapshot, not the current phase API. The analogous current Lean obligations are listed in the effect-interpreter section above.

The following properties were proved for that extracted snapshot:

- Empty-cache constructors establish structural validity for arbitrary supplied counters and chain values. `refined_from_counters_is_reachable` additionally requires each supplied live chain to equal the canonical iteration of its fixed initial chain at the supplied counter, while `concrete_kernel_new_is_reachable` establishes `concrete_reachable` for a fresh `ConcreteRatchetKernel` whose two chains contain the same supplied executor.
- `symmetric_ratchet_kdf_request_is_exact` proves that a core-created `SymmetricRatchetKdfRequest` contains the exact supplied 32-byte input and `SYM_RATCHET_INFO`. `ratchet_step_uses_exact_chain_and_partition` proves that `derive_ratchet_step` constructs that request from the exact old chain, assigns output bytes `0..32` to the owned key, `32..64` to the owned next chain, and `64..76` to the owned nonce, and returns one typed step. The executor output remains arbitrary in F*.
- A successful send allocation increments the counter by exactly one, returns a capability for that same sequence and the canonical `material_at` value for the newly published counter, does not touch receive state, and cannot wrap. Exhaustion at `u64::MAX` changes no state. `refined_advance_send_preserves_reachability` covers both outcomes.
- Sequentially finishing an available send capability marks the returned value unavailable; finishing that returned value again fails without changing it.
- A successful future receive plan reports a derivation count equal to the numeric gap; the plan itself derives nothing. Admission requires both a gap of at most 50 and total outstanding capacity of at most 50. Larger gaps and capacity overflow are rejected with a count of zero. An old or current target requires zero new derivations, but that result does not say its key is still present in the cache.
- The low-level compatibility receive-advancement transition increments once, advances the supplied receive chain to the next canonical iteration, appends the exact new sequence with its canonical `material_at` result, preserves the send counter and reachability, and reports the old cache length as the append slot. A full cache or exhausted counter is state-neutral. This fact is not the production open path: high-level opening uses private preparation and success-only publication, and callback failure never publishes the compatibility transition.
- The production-facing `concrete_open_and_finish` selects `concrete_ratchet_step` internally and delegates its complete receive transaction to the refined kernel. The generated definition orders planning and destination preflight before the first KDF request, so source-level admission, capacity, and lookup rejection paths do not evaluate the executor or open callback. `rejected_admission_is_entry_neutral` proves extensional independence from arbitrary pure executor/callback functions; observable runtime call counts and side effects rely on faithful compilation, control-flow review, and Rust tests rather than an F* effect theorem. An admitted future frame may evaluate the executor for its exact bounded candidate path and then evaluate the open callback once, but neither action mutates the live refined state.
- `admitted_future_plan_prepares_valid_pending` proves that every valid admitted nonzero plan returns a future candidate whose `valid_pending` invariant identifies the exact bounded derivation count under the same fixed receive step, consecutive skipped sequences and absolute slots, preserved old cached derivations, separate canonical target, final chain, post-target-consumption control, and exact success publication. `admitted_cached_target_prepares_valid_cached` analogously proves that a valid cached target satisfying the zero-derivation plan returns the exact prevalidated target/old-last removal. The generated pure preparation function has no live-state result and the Rust helper borrows the entry immutably; the high-level rejection theorem, rather than the tautological preparation-equality lemma, proves complete returned-state equality. Callback-success theorems remain conditional on the callback returning plaintext.
- `lookup_receive_key` is characterized in both directions for valid states. A `Some(slot)` result names the unique active slot holding the requested sequence, while a `None` result means the sequence is absent. From a reachable state, `refined_receive_key_is_derived` further proves that any returned material is exactly `material_at` for that requested positive sequence. Production can therefore treat `None` as authoritative instead of reproducing the scan in adapter code.
- `finish_receive_with_removal` is the sole detailed logical completion transition, and the compatibility `finish_receive` function is proved to return the same state and disposition. A wrong sequence/slot pair produces `Missing`, no removal, and unchanged state. Authentication failure produces `Retained`, no removal, and unchanged logical state. Authentication success produces `Consumed`, reduces the cache length by one, reports the target slot and the previous last slot, removes the target, preserves every other logical sequence exactly once, and moves the previous last entry into the target slot when the two slots differ.
- The compiled future-preparation path owns one fixed-capacity staging array in `prepare_receive` and passes only a mutable reference to that array through the bounded recursive helper. The helper returns separate final-target metadata, and the caller moves the staging array into `PendingReceive` exactly once. This source-level ownership shape prevents the staging array's footprint from being replicated at every recursive frame while preserving private, state-neutral preparation. Hax represents the mutable borrow by functionally threading one array value through the extracted recursion, so the updated exact-preparation lemmas reason about the returned array/metadata pair without claiming Rust stack-layout semantics. The constrained-stack Rust regression supplies compiled-code evidence for the intended reduction but does not prove a compiler stack-layout bound.
- The low-level `finish_receive(..., false)` identity fact remains useful for the pure logical completion API, but it is not the high-level production failure trace. Production authentication runs while the cached or future preparation is still private. Callback `None` returns full refined-state equality, drops every staged skipped entry and the separate future target, and consumes no live capacity. Conditional callback-`Some` theorems identify cached publication as the prevalidated whole-entry swap-removal and future publication as the final chain, skipped entries, and post-target-consumption control without the target. Generated control flow and Rust tests show that retrying an invalid future frame repeats the bounded KDF work; this is not inferred from the low-level cached-key retry lemma.
- `restore_receive_key_with_slot` performs the checked ordered append and returns the old logical cache length as the slot containing the restored sequence. Structural validity remains available for arbitrary imported values, but derivational reachability is conditional: `start_refined_restore_is_reachable` requires trusted persistence provenance showing that both live chains are the canonical iterations named by the imported counters, `refined_restore_receive_key_preserves_reachability` requires each appended material to equal the canonical `material_at` value for its positive sequence, and `finish_refined_restore_preserves_reachability` then publishes a reachable state. The maintained `PersistentServer` adapter supplies canonical decode/re-encode checking, lineage and generation, and activation CAS as production evidence for those premises, but F* does not verify that adapter or establish that `SnapshotStore` supplies the required payload integrity and provenance.
- `concrete_seal_next` selects `concrete_ratchet_step` internally, invokes the seal callback with the canonical core material for the allocated sequence and supplied context, and consumes the private token. `concrete_seal_next_preserves_reachability` covers both `Some` and `None` callback results without allowing production to supply or reconstruct a step.
- Refined receive-until rejection is callback-independent and complete-state neutral because plan and destination validation precede every callback; the accepted executor has no reported intermediate failure branch. The F* callback is a pure function, so production callback side effects, panics, crash behavior, and concrete invocation traces remain outside this statement.
- The kernel-private lookup returns only canonical material for the requested sequence in a reachable state and rejects a populated slot whose sealed tag differs from that sequence. `concrete_open_and_finish` passes only the preparation-selected material, its sequence, and the supplied frame context to the opaque open callback. Callback `None` returns the complete entry state; callback `Some(plaintext)` returns that plaintext only with same-sequence consumption and exact success publication. Cached completion checks both target and old-last tags before the callback and successful publication moves the complete old-last canonical record into a non-last target. Future publication validates every staged slot before moving the first value and then installs the final chain and control with no reported failure branch.
- `concrete_initial_kernels_are_complementary` and `concrete_initial_kernels_are_reachable` connect one agreed 32-byte root, one fixed pure initial executor, and one fixed lifetime ratchet executor to both role-bound kernels. `concrete_directional_materials_agree` then proves for every natural-number sequence that beacon-send material equals server-receive material and server-send material equals beacon-receive material. `beacon_seal_server_open_preserves_concrete_session` and `server_seal_beacon_open_preserves_concrete_session` preserve both kernels' concrete reachability across the corresponding public operations for every callback outcome; they do not assert that an arbitrary seal result is accepted by an arbitrary open callback.
- Pointwise replacement leaves a peer record with a different ID unchanged. Mismatched send advancement returns no sequence and an unavailable capability; for the selected peer, the peer ID, ratchet, and sequence match direct send advancement.

State neutrality trades unauthenticated cache exhaustion for bounded recomputation: the same invalid boundary-distance frame can force up to 51 private ratchet-KDF steps on every attempt—50 skipped-key derivations plus the separately consumed target. Deployments still need external per-peer rate limits, admission quotas, or transport replay filtering for availability, and those controls must not encode rejection by mutating the ratchet. Neither proof system models those controls, timing, resource exhaustion, or denial-of-service resistance.

The last result is pointwise: it does not prove that a production Server whole-map lookup selects one unique entry or updates the complete map correctly.

The current implementation retains the useful ownership improvement—`RatchetManager` stores one authoritative `ConcreteRatchetKernel` and no parallel control or material arrays—but replaces the old executor/callback surface with the phase protocol described above. The kernel owns persistent chains/material, exact KDF-request construction, response partitioning, destination preflight, private sequence tags, staged publication, and every logical/material mutation. Production interprets requests without choosing the chain, label, partition, sequence, cache slot, or commit shape.

The predecessor F* proof identified canonical derivations relative to abstract pure executors but did not prove their cryptographic semantics. The new Lean refinement must similarly assume faithful, total HKDF-SHA-512 responses to the exact requests; equal session roots additionally depend on faithful PQXDH root HKDF over the exact verified transcript and `PQXDH_INFO`. Neither proof system currently proves concrete HKDF behavior, output noncollision, adapter side effects or panics, compiler correspondence, or machine code.

This reachability result supports a conditional key/nonce-no-reuse claim rather than proving unconditional uniqueness. `reachable` is a predicate over one state and does not express a global lineage, unique live owner, committed allocation history, external generation, or CAS. If the concrete fixed step faithfully implements the intended HKDF, its canonical outputs have noncolliding key/nonce fields for distinct allocations, and production maintains one authoritative state that is neither forked nor rolled back, then monotonic counters and `material_at` prevent distinct committed allocations in that directional stream from reusing a key/nonce pair. The maintained high-level Rust API supports the ownership premise by removing `Clone` from operational ratchet state and by making returned update snapshots inert; `PersistentServer` supports the restart and multi-owner premise only when its external store contract holds. The C, Go, and Python full-checkpoint helpers use an in-memory store and explicitly do not satisfy that premise: restoring the same export twice or substituting an old export can repeat canonical sequence material. Extending the claim across directions, peers, or sessions also requires the corresponding initial streams and domains to be noncolliding. F* proves neither noncollision nor the production ownership/persistence premises, and a fork or rollback outside the supported path can repeat the same sequence and canonical material.

The affine KDF and open/seal phase values remain private implementation details of `ConcreteRatchetKernel`. They route core-selected material, sequence, and opaque context to the adapter, but no current Lean theorem proves the adapter's commitment or ChaCha20-Poly1305 semantics. The core's secret-bearing request, response, chain, key, nonce, and material values implement `ZeroizeOnDrop`; production converts borrowed material to libsodium values only for the immediate call. Correct conversion bytes, libsodium behavior, result provenance, retained ephemeral copies, compiler treatment of zeroization, and physical erasure remain external. Production restoration canonicalizes the payload and fences activation by external generation CAS, while proof-side restoration remains conditional and does not prove serde fidelity, trusted payload provenance, store correctness, rollback resistance, crash behavior, or replica coordination. No cryptographic snapshot authentication or encryption is provided.

The runtime also enforces an establishment gate that should not be confused with a new generic compile-time typestate theorem. The server map stores `EstablishedRemote` values whose production construction follows PQXDH commit or fresh restoration from the trusted store, and the beacon owns an operational ratchet only in `BeaconState::Established`; manual insertion, reset, associated-data mutation, and mutable ratchet access are test-only or crate-private. F* proves the role-specific PQXDH transition results and fresh-kernel reachability, but it does not prove the complete Rust map representation, visibility rules, trusted restore adapter, or every application call site.

For the selected functions, strict checking also proves the array-bound and similar safety conditions that hax generates. This is not a proof that the entire application, all adapter error paths, allocation, FFI, or machine code is panic-free. Nor does extraction and typechecking give every selected function a complete behavioral specification: the beacon abort helpers, arbitrary malformed `InitKex` inputs, and all registration-finishing error paths do not have handwritten semantic theorems.

## Concrete properties proved by ProVerif

### The modeled attacker and execution

All protocol traffic crosses an attacker-controlled network. Protected payloads
are still symbolically encrypted, but the attacker may observe ciphertexts and
may block, replay, reorder, modify, and synthesize network data. In the baseline
isolation scenario, honest beacons, attacker-owned beacons, and server processes
are replicated, so the model considers unbounded concurrent instances. Each
honest instance nevertheless executes one fixed record schedule: four
server-to-beacon records and one beacon-to-server record, with server sequence 3
received before sequence 2
([model](../beaconcrypt-core/proofs/pro-verif/environment.pvl)). The separate
late-compromise scenario retains the honest protocol processes and adds its
snapshot-specific compromise process; it does not need the malicious-registration
processes to establish those conditional compromise results.

Each attacker-owned beacon creates a fresh identity, prekey, one-time key, and
ML-KEM key, gives all four secrets to the network attacker, and publishes a
valid self-signed registration. A separate server path performs the same public
signature parsing, role validation, DH/KEM root construction, assigned-ID
binding, and initial response sealing. It deliberately treats each malicious
request as fresh, which gives the attacker at least as many sessions as the
production replay set would, but does not prove replay behavior for malicious
identities.

The private `honest_origin` and `malicious_origin` tables select the proof events
and application payload appropriate to each modeled recipient. They are proof
annotations representing the threat model's recipient-specific task-routing
assumption—not production log entries, ACLs, wire fields, or a proof that the C2
application selects the correct recipient.

### CTX commitment negative control

The ordinary record model's [`open_frame`](../beaconcrypt-core/proofs/pro-verif/crypto.pvl) rule already requires an exact key, nonce-derived material, associated data, sequence, sender ID, tag, and ciphertext term.
Its record correspondence therefore establishes origin only under that ideal exact-opening rule; by itself it does not show what CTX adds to a non-key-committing AEAD.

The dedicated [`aead-commitment-negative-control.pvl`](../beaconcrypt-core/proofs/pro-verif/aead-commitment-negative-control.pvl) instead defines one ciphertext/tag term with two successful reductions to distinct fresh plaintexts under structurally distinct key, nonce, and associated-data terms.
Both top-level scenarios run the exact same [`WeakAeadMultiOpened` query](../beaconcrypt-core/proofs/pro-verif/aead-commitment-negative-control-queries.pvl): [`aead-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-commitment.pv) must report the event unreachable because the one collision-free `ctx_commitment` term cannot validate both contexts, while [`aead-no-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-no-commitment.pv) removes those checks and must produce a trace reaching the event.
The result classifier requires those exact opposite classifications.

This differential result supplements the F* pointwise theorem with an explicit ideal-hash CTX/no-CTX counterfactual and does not assume that the base AEAD is key committing.
It remains a symbolic result for one explicit multi-opening theory, not a computational proof of BLAKE2b or an end-to-end theorem about compiled Rust.
The [computational lifting](ctx-commitment.md) is now machine-checked for the corresponding handwritten Lean ideal-model event, while the F* fixed-width witness and the Lean probability theorem remain separate until the extracted transcript/adapter bridge is proved.

### Baseline secrecy

The five baseline secrecy queries in
[`queries.pvl`](../beaconcrypt-core/proofs/pro-verif/queries.pvl#L7-L11)
all succeed while attacker-owned beacons concurrently submit valid registrations
and the server can commit their responses. The symbolic attacker cannot derive
these named honest-session application values while honest state remains
uncompromised:

| Modeled value | Position in the fixed schedule |
| --- | --- |
| `INITIAL_SECRET` | Initial server-to-beacon registration message. |
| `CACHED_SECRET` | Server sequence 2, whose key is temporarily cached because sequence 3 is received first. |
| `ADVANCE_SECRET` | Server sequence 3, consumed during out-of-order advancement. |
| `FUTURE_SECRET` | Server sequence 4 in the uncompromised baseline. |
| `BEACON_RECORD_SECRET` | First beacon-to-server record. |

The malicious-registration response instead contains the distinct private
`MALICIOUS_TASK_SECRET`, and a deliberate negative query confirms that the
attacker can recover it using the beacon secrets it controls. Thus the malicious
path is usable rather than blocked, while it does not receive any of the five
honest canaries. This is symbolic confidentiality of five fixed honest message
positions under correct application routing. It is not a computational
indistinguishability result, an information-flow proof for arbitrary payloads,
or a ProVerif proof for an arbitrary-length application stream.

### Authentication, agreement, and replay correspondences

Six injective correspondences are proved in the baseline. Their antecedent
events occur only on the honest-origin path; compromised endpoints are not
expected to satisfy honest-party authentication:

In this table, `origin` is a private proof-model marker tying events to one
specific honest registration bundle. It is not a field on the wire.

| If this event occurs... | ...a unique earlier event exists with exactly these matching values | Meaning inside the model |
| --- | --- | --- |
| `ServerAccepted` | `BeaconInitiated`: server identity, beacon identity, complete role-tagged `InitKex`, semantic registration ID, origin | An accepted honest-beacon registration came from one matching honest initiation; altered fields cannot be accepted as that honest registration. |
| `ServerAccepted` | `RegistrationConsumed`: the same public registration values and origin | Acceptance occurs only after its modeled replay entry is consumed. |
| `RegistrationConsumed` | `BeaconInitiated`: the same public registration values and origin | At most one modeled consumption can correspond to one honest single-bundle origin. |
| `ServerResponseAborted` | `RegistrationConsumed`: the same registration and origin | An abort is recorded only after consumption. Continued “no undo” behavior is built into the separate replay-owner process and its non-rollback assumption, not this correspondence alone. |
| `BeaconCommitted` | `ServerCommitted`: both identities, full initiation, registration ID, assigned key ID, ordered root input, root, associated data, session, origin | Beacon commit authenticates a unique earlier matching server commit. This is one-way agreement; delivery and eventual beacon commit are not guaranteed after server commit. |
| `MessageReceived` | `MessageSent`: session, direction, sequence, sender, receiver, plaintext | Each accepted record in the fixed schedule has one matching honest send, with peer, direction, sequence, session, and content bound. |

The exact queries are in
[`queries.pvl`](../beaconcrypt-core/proofs/pro-verif/queries.pvl#L13-L174).
The last correspondence is the basis for the modeled record-authentication,
cross-direction, cross-peer, cross-session, replay, and “a party cannot be
tricked about who shares the key” claims. Those are consequences of the event
arguments being equal, not separate general-purpose theorems. The modeled
schedule attempts each receive only once at each fixed sequence; general duplicate receive-key consumption has predecessor F* evidence for the old callback source and is enforced by the current affine open phase. The checked Lean effect refinement derives the actual cached-open phase and its exact selected material/ideal removal relation from `KernelRefines` plus an ideal lookup, and proves the consumed control state refines ideal skipped-key filtering. Full post-state refinement remains under the additional material-array `CachedPublicationRefines` premise. The production claim also requires correct concrete AEAD/commitment semantics, one authoritative state, no retained external copy, and no rollback.

### Reachability checks

An implication can be vacuously true if its later event can never occur. For
example, “every accepted message was sent honestly” says nothing if the model
can never accept any message. Seven separate queries provide non-vacuity
controls
([queries](../beaconcrypt-core/proofs/pro-verif/reachability-queries.pvl)).
Five show that the model can reach honest server acceptance, registration
replay rejection, abort after consumption, beacon commit, and a message receive.
One reaches a committed attacker-owned registration response, and the last
requires the attacker to derive the private canary sealed into that response.

ProVerif prints each positive reachability request as a negated statement. The
required result is therefore `false`: “the event never occurs” is false because
a trace to the event exists. The malicious-canary query is likewise an
intentional false secrecy result. These are consistency/non-vacuity witnesses,
not failed security proofs. They do not separately establish reachability of
every one of the five honest secret-bearing record sites.

### State-neutral receive and compromise

The dedicated [`failed-receive.pv`](../beaconcrypt-core/proofs/pro-verif/failed-receive.pv) file now contains a state-neutral server-to-beacon receive scenario. It gives the attacker public authentic ciphertexts and a correctly typed forged frame whose protected component cannot satisfy the ideal `open_frame` rule. The short leg uses one explicit `ready_state` term before the attempt, after the first rejection, after the repeated rejection, and at the later authentic receive. F* proves the corresponding generic rejection equality, non-vacuous exact preparation, conditional success publication, replay neutrality, and repeated-fixed-rejection retry equivalence without a role or direction parameter; ProVerif supplies the finite cryptographic secrecy, compromise, and exact-schedule witnesses and does not duplicate this trace in the beacon-to-server direction.

The finite execution has two exact legs:

| Phase | Modeled state effect |
| --- | --- |
| Consumed past | Sequence 1 succeeds and its material is no longer in receiver state. |
| Rejected future attempt | A forged sequence-3 frame may represent private candidate derivation, but rejection continues with the exact sequence-1 counter, chain-2 live chain, and empty-cache term. |
| Repeated rejection | The same forged frame is retried from the identical `ready_state` term, so it adds no cache entry and must repeat private candidate derivation. |
| Honest future success | The authentic sequence-3 frame opens against canonical target material, publishes only skipped sequence 2, advances the live chain through sequence 3, and consumes rather than caches sequence 3. |
| Replay and delayed delivery | Replay of the exact sequence-3 frame is rejected relative to the exact post-success state, then the authentic delayed sequence-2 frame consumes the one cached skipped key. |
| Maximum-gap success | In the separate capacity leg, the receiver advances from sequence 1 to sequence 52, retaining exactly sequences 2 through 51 and consuming sequence 52 separately. |
| Capacity rejection and release | Sequence 54 is rejected because all 50 cache slots are occupied and accepting it would retain sequence 53; cached sequence 51 is then consumed without moving the live counter or chain. |
| Forward progress | Sequence 54 then succeeds, publishes skipped sequence 53, consumes sequence 54 separately, and ends with 50 cached entries. |

The private-state queries require all six named application values—consumed past, short-leg skipped and target, maximum-gap target, cached sequence 51, and after-release target—to remain secret. They preserve receive-to-send origin correspondence for every successful open. Twelve reachability queries witness both rejected attempts, every short-leg success and replay event, maximum-gap success, capacity rejection, cached consumption, after-release success, attacker-owned registration commit, and attacker recovery of its routed canary.

The repository threat model permits the attacker to register and fully control separate malicious beacons but excludes access to a legitimate beacon's execution state. The private receive top level runs those malicious registration processes concurrently: their canary is attacker-readable while all six receive canaries remain secret. This is direct symbolic composition of the capabilities, not an end-to-end handshake/record trace; both receive legs begin from fresh symbolic roots. Interpreting the disjoint symbolic states as distinct production peers still depends on the reviewed peer-selection and independent-root adapter refinements. Registering a malicious beacon does not trigger the separate receive-state compromise process.

The separate [`failed-receive-compromise.pv`](../beaconcrypt-core/proofs/pro-verif/failed-receive-compromise.pv) scenario synchronizes compromise immediately after the two rejected attempts and before authentic sequence-3 delivery. The private snapshot message carries `ready_state` as both its before and after term, the unchanged chain-2 live chain, and the empty cache. The compromise process structurally requires that empty cache and discloses only the live chain. The consumed sequence-1 value remains secret. The short-leg skipped and target values are deliberate negative secrecy results because the forward chain derives their material; the independently rooted maximum-gap, cached, and after-release values remain secret. The result is that rejection did not enlarge state or exposure, not that future material survives compromise of a live symmetric chain.

Compromise does not make later honest delivery impossible. A separate reachability witness schedules the attacker to forward the original authentic sequence-3 ciphertext after compromise, and the receiver can still accept it through a freshly prepared candidate. This is possibility, not liveness: the active attacker may block delivery or use the compromised future material to construct another accepted frame first, in which case the honest ciphertext will later be rejected.

This ProVerif result is one exact, unrolled capacity-50 schedule under ideal cryptography. It is not a quantification over every gap, cache arrangement, retry count, or interleaving. The predecessor F* artifact proves general canonical derivation, whole-plan preflight, callback-failure entry equality, conditional success publication, replay, repeated rejection, and capacity facts for its old concrete API, but not the corrected phase API's maximum-gap transition. For the current phase machine, Lean proves that the generated control driver refines `Ratchet.recvStep` directly at the 50-skipped-key bound, exact entry recovery for supplied finite failed-trace witnesses, generated cached-open construction from `KernelRefines` plus an ideal lookup, the control-plane half of cached consumption, and conditional cached success against cached `recvStep`; it does not yet prove cached material-array publication or effect-level future success/publication. Neither proof establishes concrete root or ratchet HKDF semantics or totality, output noncollision, ephemeral libsodium conversion and AEAD behavior, cryptographic secrecy, compromise, or forgery conclusions of the symbolic trace.

The ProVerif attacker starts at the post-parser admission boundary. A symbolic `crypto_frame` represents a frame whose constructor, sender, sequence, and protected component are available to the network attacker; it does not represent Cap'n Proto byte parsing or an arbitrary byte length. Therefore the model does not prove that frames which are empty, truncated, unparsable, from an unknown or wrong sender, or carry no more than the production overhead are rejected before ratcheting. Production ordering in [`decrypt_message_with_ratchet`](../beaconcrypt/src/ratchet.rs) and the boundary/truncation regressions in [`beaconcrypt/tests/protocol.rs`](../beaconcrypt/tests/protocol.rs) support those separate adapter claims.

### Precisely scoped late-compromise results

For each replicated honest-beacon session that reaches the compromise point,
the compromise model permits the same one kind of synchronized beacon snapshot:
after sequence 3 has been consumed while sequence 2 remains cached. It reveals
exactly:

- the live receive chain from which sequence 4 can be derived;
- the cached sequence-2 message material; and
- the live beacon send chain.

It does not reveal long-term identity, prekey, KEM, or server state. The model
constructs the snapshot at the exact point shown in the
[beacon process](../beaconcrypt-core/proofs/pro-verif/environment.pvl#L516-L531),
and the [compromise process](../beaconcrypt-core/proofs/pro-verif/environment.pvl#L1065-L1085)
reveals its three fields.

The expected results are:

| Message | Result after that exact compromise | Meaning |
| --- | --- | --- |
| Initial message | Still secret | Its message material is no longer retained and cannot be derived backward in the ideal ratchet model. |
| Server sequence 3 | Still secret | Its material was consumed before compromise. |
| Server sequence 2 | Exposed | Its skipped-message key is still cached. |
| Server sequence 4 | Exposed | Its key is derivable from the compromised live receive chain. |
| Next beacon-to-server record | Exposed | Its key is derivable from the compromised live send chain. |

The first two are narrow deleted-key forward-secrecy results. The last three are
intentional, machine-checked attack results: skipped cached keys are vulnerable,
and the symmetric ratchet has no post-compromise security. They must not be
reported as ignored proof failures.

The model does not order the server's sequence-4 send relative to the snapshot;
concurrent scheduling permits it before or after. It does order the beacon's
sequence-4 receive after compromise. Revealing the live receive chain exposes
sequence 4 once its ciphertext is available, whether the ciphertext was
recorded before compromise or sent afterward. This is not a theorem about one
particular server-send timing.

In the original late-compromise suite, the events named `MessageKeyUnavailable`, `MessageKeyCached`, and `StateCompromised` document the process but are not premises of its secrecy queries. The separate state-neutral receive suite requires successful delayed delivery to follow both skipped-key publication and later unavailability, and it requires each successful target to become unavailable. Its secrecy conclusions still follow from which symbolic values each process retains or reveals, not from a universal theorem of the form “every unavailable key is forward-secret,” and not from proof of physical memory erasure.

## What is not proven

The modified CTX justification has three deliberately separated layers.
F* machine-checks `ctx_distinct_openings_imply_hash_collision`, which constructs a pointwise collision witness from two distinct accepted explanations of one fixed production-format `C || T || U` payload for arbitrary pure hash and AEAD-open functions.
Lean's native computational layer runs an adversary against the ideal `openRecord` event and returns that witness, giving a machine-checked factor-one advantage inequality under BLAKE2b-512 collision resistance; PPT/runtime preservation and production correspondence are not mechanized.
ProVerif supplies a supplementary explicit ideal-hash negative control in which the base AEAD deliberately multi-opens and removing CTX reverses the query result.
None of these layers proves BLAKE2b, the libsodium call, production field provenance, hax/compiler correctness, or compiled machine code.

### Intended claims that require narrower wording

The main [formal-verification plan](formal-verification.md#proof-inventory) mixes
an intended inventory with completed work. Comparing it to the current proof
sources gives these important qualifications:

| Broadly worded inventory claim | What the current corpus actually supports |
| --- | --- |
| “The commitment input is exactly `(key, nonce, associated data, AEAD tag, sequence, sender ID)`.” | Production delegates its hash input to the extracted fixed-size builder, and F* proves its exact six ranges plus both little-endian encodings ([Rust helper](../beaconcrypt-core/src/commitment.rs), [lemmas](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst)). The caller's field provenance, BLAKE2b call, hax/compiler correctness, and machine code remain outside the theorem. |
| “The modified CTX construction provides strong commitment.” | F* proves the fixed-width extracted pointwise collision witness for arbitrary pure hash and AEAD-open functions, including unequal-key and unequal-context base-AEAD openings; Lean proves the corresponding ideal-model pointwise witness and factor-one probability reduction to BLAKE2b collision advantage. ProVerif separately confirms the intended ideal-hash CTX/no-CTX differential. PPT/runtime preservation, the extracted-to-ideal transcript and adapter bridge, BLAKE2b, libsodium, compiler correspondence, and confidentiality/authenticity preservation remain assumptions or separate obligations. |
| “A ratchet step applies the fixed domain KDF to its old chain and returns the intended key, next chain, and nonce.” | The current phase constructs a private `SymmetricRatchetKdfRequest`, accepts only a typed 76-byte response, and partitions it inside the core as key, next chain, and nonce. Lean's checked `ResponseRefines` is the exact external law equating that parsed response with `cr.kdfChain` and `cr.kdfMsg`; `SendKdf.resume_refines` proves the send resume under that law. The analogous future-receive induction and publication remain open. HKDF-SHA-512 semantics/totality, output noncollision, adapter fidelity, compiler correspondence, panic behavior, and physical erasure remain external. |
| “Peer, counter, and ratchet publication commit atomically.” | The current Rust phase machine makes commit points explicit: send KDF resume advances state even if seal returns `None`; receive KDF work is private and only `ReceiveOpen::finish(Some(_))` publishes, while `None` returns the exact entry kernel. Lean proves direct bound-50 control refinement, non-exhausted send begin/resume/ideal success plus cancellation, and exact state recovery for supplied finite failed-trace witnesses; structural equations prove advanced-state return for either seal result. `begin_receive_cached_refines` constructs the actual cached phase from `KernelRefines` plus an ideal lookup, cached success returns the same plaintext and matches cached `recvStep`, and `finish_receive_with_removal_consumed_refines` proves the control-plane filtered-cache result. Full post-state refinement still assumes the material-array `CachedPublicationRefines`; effect-level future publication and the adapter driver remain open. `PersistentServer` separately performs no successor encoding or CAS for a rejected receive, withholds accepted output until a complete successor snapshot wins external CAS, and poisons a losing accepted branch. Neither proof system establishes driver effects, snapshot codec, trusted payload provenance, store atomicity/durability, panic/crash behavior, or rollback resistance. |
| “Cached receive material belongs to its sequence; send keys are one use; replay is rejected.” | `KernelRefines` relates every live concrete cache slot bidirectionally to an ideal skipped key and requires the unused suffix to be empty; the checked send theorems advance the ideal state under `ResponseRefines`; and `begin_receive_cached_refines` derives the generated cached open and exact material/ideal-removal relation from `KernelRefines` plus the ideal lookup. The consumed control-cache transition is also proved to refine ideal skipped-key filtering. The concrete material-array swap/empty-suffix `CachedPublicationRefines` law remains open, so this is not yet a complete current-production replay theorem. The predecessor F* artifact proves canonical association, consumption, replay, and paired-role derivation for its old concrete layer. The maintained Rust API makes operational state affine and gates it on establishment, while `PersistentServer` provides generation/CAS restoration subject to its trusted-store contract. Concrete key/nonce no-reuse still requires output noncollision and correct external ownership/persistence; neither proof establishes those premises, HKDF/AEAD semantics, serde/store correctness, trusted payload provenance, ephemeral conversion fidelity, external copies, or compiler correspondence. |
| “Counters start at one.” | F* proves that advancing any non-exhausted counter returns old plus one; a counter initialized to zero therefore first returns one. Selecting and preserving that initial production state is an adapter/initialization fact. |
| “Every accepted, bounded input is panic-free.” | Strict F* checking covers safety obligations generated for the selected pure core functions. It is not whole-application panic freedom. |
| “Initial and subsequent messages are secret; replay, unknown-key-share, cross-peer, and concurrent-session attacks are prevented.” | ProVerif proves five named messages and exact correspondences in replicated instances of one fixed five-record schedule. The event arguments support those separation interpretations within that schedule, not an arbitrary unbounded record API theorem. |
| “Forward secrecy after later compromise.” | Two named past messages remain secret after one exact beacon-ratchet snapshot. Cached sequence 2 and future traffic are exposed. Persistence and other compromise times/targets are outside that result. |
| “Authentication failure is state-neutral.” | Lean proves `ReceiveOpen::finish(None)` returns the exact entry kernel and preserves `KernelRefines`; its `ReceiveFailureTrace` theorem extends exact entry equality and refinement preservation to any supplied finite witness ending in admission rejection, KDF cancellation, open rejection, or open failure. It does not yet prove that every generated execution constructs such a witness. An admitted maximum-gap future forgery may still cause up to 51 KDF responses—50 skipped keys plus the separately consumed target—and one open attempt in production. The dedicated ProVerif trace reuses the same explicit state term across two failures before later success/replay/delayed-delivery/capacity witnesses. Primitive semantics and side effects, the adapter driver, panics, timing, logs, allocation, and physical erasure remain outside the theorem. |

### Cryptography and implementation components outside the proof

The corpus does not prove:

- computational security, concrete attack probabilities, or reductions for
  Ed25519, X25519, ML-KEM-768, HKDF-SHA-512, ChaCha20-Poly1305, or BLAKE2b;
- correctness, constant-time behavior, side-channel resistance, fault
  resistance, or memory safety of the concrete primitive implementations;
- constant-time or information-flow behavior of the selected pure core or its
  adapters; even the redundant all-zero-DH array comparison has no formal
  timing guarantee ([documented limitation](impl/formal-verification-stage-4.md#L123-L127));
- a complete behavioral specification for every extracted function and error
  path; extraction checks generated safety conditions, but the beacon abort
  helpers and arbitrary malformed/finishing errors have no handwritten semantic
  theorem;
- BLAKE2b-512 collision resistance, a concrete numerical bound for that primitive, machine-checked PPT/runtime preservation, or the production bridge for the modified CTX construction; F* machine-checks the fixed-width extracted witness and Lean machine-checks the ideal-model probability reduction, while the opaque hash implementation, extracted-to-ideal transcript correspondence, production field provenance, and compiled caller retain their stated assumptions;
- unconditional nonce uniqueness or the cryptographic correctness, secrecy, and physical deletion of actual message-key bytes; F* fixes the concrete kernel to its core-selected lifetime step, proves canonical chain/material iteration, exact KDF request input/label, exact partition, and all-sequence cross-role material equality, but uniqueness still requires noncollision of concrete outputs and authoritative no-fork/no-rollback state;
- entropy quality, fresh-key generation, operating-system RNG behavior, or physical erasure; the core secret-array wrappers now zeroize on `Drop`, but F* does not model those writes, compiler optimization, allocator behavior, or retained copies;
- Cap'n Proto parsing or serialization, serde, allocation, networking, bindings,
  FFI, the compiler, linking, or generated machine code; or
- post-quantum authentication. ML-KEM contributes post-quantum key-establishment
  material, but an active quantum attacker that breaks Ed25519 can impersonate
  the server and mount a man-in-the-middle attack.

The repository's Wycheproof, Rooterberg, known-answer, context-binding, and
multi-opening tests add valuable concrete evidence for primitive usage. They
remain tests, not proofs that discharge the ideal-primitive assumptions.

### State, persistence, and production-path gaps

The corpus also does not prove:

- correct, atomic, crash-safe, confidential, or anti-rollback persistence; the maintained adapter uses canonical snapshots plus a lineage/generation/head CAS, but payload integrity/provenance and the complete external store contract are trusted rather than extracted or proved, and snapshots are neither cryptographically authenticated nor encrypted;
- global registration replay protection across server replicas, independent restored forks, concurrent database owners, or rollback to an old snapshot; `PersistentServer` provides this refinement only for owners sharing one conforming linearizable, rollback-resistant store;
- no-fork, crash-atomic, or stale-rollback-safe persistence through the C, Go, and Python checkpoint helpers; their internal store is in memory, import trusts caller-supplied bytes as current, and independent imports of one export are independent live owners;
- truth of the adapter-supplied `Fresh`/`Consumed` and `Available`/`Occupied`
  classifications;
- atomic check-and-insert or check-and-reserve behavior in real sets and maps;
- correctness and uniqueness of general production Server peer-map selection, or the whole-map update from F*'s theorem about one selected map entry; Beacon registration finish instead checks its sole stored server principal against the binding retained by verified state, and both concrete selection refinements remain outside F*;
- concrete PQXDH root-HKDF and symmetric-ratchet HKDF semantics/totality, noncollision of canonical key/nonce outputs, ephemeral conversion of borrowed core key/nonce arrays into libsodium values, AEAD result provenance, adapter-driver or primitive panic behavior, crash/concurrency atomicity, compiler correspondence, retained copies outside the authoritative concrete kernel, or rollback; the current core makes exact requests and typed partitions explicit, and Lean proves direct bound-50 control refinement, non-exhausted send begin/resume/ideal success plus cancellation, rollback for supplied finite failed-trace witnesses, conditional open-reply consistency, generated cached-open construction, the control-plane half of cached consumption, and conditional cached success, with structural equations for exhaustion and either seal result, but effect-level future receive publication, initial composition, restoration, cached material-array publication, ideal send exhaustion, and adapter interpretation remain open, while predecessor F* concrete theorems apply only to their old executor/callback source snapshot;
- trusted provenance of restored chains, counters, and receive sequence/material pairs as a theorem conclusion; the restoration theorems remain conditional, while production attempts to discharge the premise with a trusted-store payload-integrity/provenance contract, canonical decode/re-encode check, and fresh activation CAS that F* does not verify;
- canonical JSON parsing, duplicate-key rejection, or serialization injectivity; production uses a duplicate-rejecting visitor before `HashMap` insertion, canonical decimal `u64` keys, sorted output, unknown-field rejection, and byte-identical decode/re-encode validation, but these are reviewed adapter behavior rather than proof conclusions;
- byte-level equivalence between ProVerif's admitted symbolic frame and production Cap'n Proto parsing, sender lookup/checks, overhead-length validation, commitment slicing, or malformed-input rejection;
- behavior through direct beaconcrypt-core construction or test-only/crate-private receive-ratchet, peer-map, reset, compatibility, or mutation helpers outside the documented high-level API trace;
- security after an unsafe retained copy, bypass of the affine high-level API, use of an independent store, or rollback of counters and replay history; those cases can repeat the same canonical sequence material even though supported operational types are not `Clone`; or
- physical deletion of old keys. Server snapshots contain current ratchet chains and cached receive keys and are explicitly documented as weakening server-side forward secrecy ([persistence overview](persistence.md#server-state-persistence)). The trusted store, not snapshot cryptography, supplies their integrity and provenance.

The persistent consumed-registration history is also unbounded. A party able
to submit many cryptographically valid registrations can grow memory and stored
state. The local 50-key receive bound is not a general denial-of-service proof.

### Protocol traces and attacker cases outside the model

There is no proof here for:

- an arbitrary number of records or arbitrary out-of-order schedules within one
  session;
- arbitrary retry counts, counter wrap/exhaustion in ProVerif, or all possible receive gaps and cache arrangements; ProVerif covers one exact short rejection/success leg and one exact capacity-50 leg, while the general finite control mechanics are handled by F*;
- compromise at an arbitrary time, repeated compromise, server compromise,
  compromise of long-term identity/prekey/KEM secrets, key-compromise
  impersonation, or recovery after compromise;
- compromise of an identity classified as honest, cross-bundle splicing if one
  honest identity may create multiple independently signed bundles, exact
  replay behavior or post-registration record traffic for attacker-owned
  identities, or correctness of the application's task-routing/broadcast
  policy;
- secrecy of metadata such as visible sequence and key-ID fields, anonymity,
  unlinkability, traffic analysis, or application headers outside beaconcrypt;
- availability, liveness, eventual delivery, fairness, resource exhaustion, or
  denial-of-service resistance; or
- protection if the compiled-in server key is replaced during beacon
  distribution. The server public key is a trust anchor, not something this
  protocol establishes.

## Assumptions made by the proofs

### Cryptographic assumptions

The F* theorems expose most primitive facts as preconditions rather than local
axioms. To lift their conclusions to real protocol runs, the following must be
true:

- honest X25519 computations agree for DH1 through DH4 in the exact modeled
  order, and invalid all-zero outputs are handled as expected;
- ML-KEM encapsulation and decapsulation agree;
- Ed25519 verification authenticates the exact tagged bytes;
- Ed25519-to-X25519 conversion and all primitive calls have the documented
  semantics;
- HKDF is deterministic and supplies the needed PRF and one-way properties. Production must faithfully and totally derive the common PQXDH root from the exact verified root transcript with `PQXDH_INFO`; `authenticated_registration_derives_common_fixed_root` proves equality only for one fixed pure root function in the predecessor F* artifact. For initial-chain and per-step expansion, the current core constructs `SymmetricRatchetKdfRequest` with the exact root or old chain and `SYM_RATCHET_INFO`, and production interprets the typed request. The initial 64-byte role split, each 76-byte material/next-chain split, complementary fresh kernels, and all-sequence cross-role agreement must be re-established for the current phases. Concrete HKDF behavior, output noncollision, ephemeral libsodium conversion fidelity, adapter correctness, and compiler correspondence remain obligations;
- AEAD hides plaintext and reports success only for an authentic ciphertext under the same key, nonce, associated data, and plaintext; distinct messages use secret, nonreused key/nonce pairs and do not leak through another path, with no reuse derived from the F* reachability result only when the stated output-noncollision and authoritative no-fork/no-rollback assumptions hold; and
- BLAKE2b supplies the collision/commitment property assumed for the fixed CTX
  construction.

ProVerif represents these with stronger perfect symbolic constructors and
equations in
[`crypto.pvl`](../beaconcrypt-core/proofs/pro-verif/crypto.pvl). Signatures
are unforgeable, matching DH and KEM always agree, constructors do not collide,
secrets cannot be recovered by inversion, and a frame opens only with exactly
matching material, associated data, sequence, and sender ID. The model uses
separate ideal constructors for the root, both directional chains, ratchet
advance, material, key, and nonce. That is finer domain separation than the two
concrete HKDF labels above.
Real algorithms approximate these properties probabilistically, and the proof supplies no general computational reduction from all real algorithms to this ideal model.
The modified CTX claim instead has a narrow direct ideal-model reduction to collision resistance and a separate F* fixed-width witness; it does not derive computational security from the ProVerif result or yet connect the ideal theorem to the production hash call.

### Adapter and execution assumptions

The current `ConcreteRatchetKernel` owns logical control, both fixed-width directional chains, and fixed slots containing tagged core `RatchetMaterial` records. It owns no cryptographic executor. Affine initial/send/receive phases construct exact requests and stage all uncommitted state, but the checked Lean refinement currently covers the extracted control plane rather than this complete production effect lifecycle. The predecessor F* artifact proves analogous executor/callback properties for its own source snapshot; it does not discharge the current adapter connection. Production therefore still assumes:

- Cap'n Proto registration fields translate exactly to the core's typed and
  role-tagged values, and signature verification authenticates those exact
  bytes before `validate_init_kex` is trusted;
- beacon construction supplies the authentic compiled-in server public key and numeric identity-key ID as the exact `ServerBinding` stored by `BeaconFresh`, and the parsed Phase-2 identity bytes supplied to finish are the response's actual `identityKey` field;
- the authenticated sender ID and eight assigned-ID bytes passed to the post-open core transition are exactly the `CryptoFrame.keyId` and plaintext prefix returned by a successful initial AEAD open;
- the adapter passes the exact F*-verified root input and `PQXDH_INFO` to a deterministic, total, semantically correct root HKDF and uses the exact returned associated data; equal transcripts then yield the common concrete root required by `authenticated_registration_derives_common_fixed_root`;
- `finish_initial_ratchet_kdf` and every send/receive loop invoke HKDF-SHA-512 exactly once for each emitted `SymmetricRatchetKdfRequest`, return the response to its own affine continuation, and do not substitute an input, `SYM_RATCHET_INFO`, output partition, role direction, sequence, or cache slot; HKDF semantics/totality, output noncollision, panic/side effects, and compiler correspondence remain external;
- `seal_frame` and `open_frame` correctly convert the borrowed core key and nonce arrays into ephemeral libsodium values and implement the intended CTX commitment and ChaCha20-Poly1305 operations over the exact material, sequence, and opaque context supplied by the final phase;
- the synchronous driver invokes no effect twice, reinstalls exactly the returned kernel on every normal path, preserves failed-send advancement and failed-receive rollback, and does not retain a concrete key, chain, phase, authoritative kernel, or ephemeral conversion; the maintained types are affine, but Lean does not yet prove this Rust driver, visibility, unsafe/FFI behavior, or absence of memory copies;
- a panic while the driver owns a phase leaves the manager's private slot empty and drops the continuation, and deployment treats that owner as unusable; no normal-return theorem proves panic, unwind, crash, or concurrent atomicity;
- send-target and receive-sender selection uses the ratchet owned by `BeaconState::Established` or one unique Server `EstablishedRemote` entry and preserves all non-selected Server peers; F* does not prove this complete runtime establishment gate or whole-map behavior;
- `Fresh` means the exact semantic ID is absent, successful acceptance inserts
  it monotonically, and `Available` means the exact next peer ID is absent;
- the counter, peer, and staged ratchet are published together only after
  response encryption and serialization succeed, while replay consumption
  intentionally occurs earlier and remains consumed on later failure;
- a fresh beacon emits only one registration bundle, supplies fresh coins, and
  does not reuse the bundle after advancing or aborting;
- production follows the documented high-level registration, encryption, and decryption paths from fresh, successfully validated, or trusted-store-provenance and freshly CAS-activated established state;
- operational pre-send ratchet state is affine in the maintained Rust API, the stack-local operation does not persist or reuse an available send-capability copy, inert `RatchetSnapshot` update views cannot become live managers, and any key/nonce-no-reuse claim still assumes noncollision of canonical outputs at distinct allocations;
- restoration requires the exact five-field ratchet payload, rejects legacy objects containing `send_past`, rejects duplicate and noncanonical numeric map keys before `HashMap` insertion, validates bounds and tags, sorts exact imported receive sequence/material pairs, and rebuilds only through the checked restore functions; the containing `ServerSnapshot` binds lineage/generation/parent digest, requires canonical decode/re-encode equality, receives integrity and provenance from the trusted store rather than snapshot cryptography, and is activated only after an external head CAS; and
- server state and replay history have one authoritative owner because every persistent operation and restoration shares one conforming linearizable, durable, rollback-resistant `SnapshotStore`, and a CAS loser is fenced by poisoning.

The current core supplies a no-exclusion, first-order translation surface: core-owned request input and `SYM_RATCHET_INFO`, typed fixed output sizes and partitions, direct role-bound initialization phases, and explicit send/receive commit points. The maintained adapter adds the still-unproved effect interpretation, affine establishment-gated ownership, inert update snapshots, canonical duplicate-rejecting decoding, and generation/head CAS with fencing. Private Rust fields, consuming APIs, `ZeroizeOnDrop`, compile-time assertions, and tests support these refinements but do not make primitive semantics/totality, adapter/parser/codec fidelity, principal selection, trusted payload provenance, store behavior, output noncollision, crash handling, compiler behavior, physical erasure, or no-fork/no-rollback deployment guarantees into Lean or F* theorems. Binding checkpoint export/import is explicitly outside the durable one-owner premise. Snapshots have no cryptographic authentication or encryption.

### ProVerif protocol-model assumptions

The trace results additionally assume:

- the server public key embedded in each honest beacon is authentic and its
  secret remains uncompromised;
- honest beacons generate fresh identity, prekey, one-time, and KEM secrets;
- the server generates fresh ephemeral X25519 and KEM encapsulation coins for
  each modeled registration;
- honest-beacon identity, prekey, one-time, and KEM secret values remain
  private; each attacker-owned beacon instead publishes all four freshly
  generated secrets before registration;
- the five named honest application plaintexts start unknown to the attacker,
  enter the protocol only at their designated honest message sites, and are
  routed only to their intended honest recipient;
- `MALICIOUS_TASK_SECRET` starts private, enters only the attacker-owned
  registration response, and is expected to become attacker-known;
- one fresh honest beacon identity emits one registration bundle;
- replay state is a private, atomic, single-owner, non-rollback process whose
  first request returns `Fresh` and all later requests return `Consumed` for an
  honest identity; the malicious path conservatively treats requests as fresh
  and makes no malicious-replay claim;
- the private origin tables perfectly classify modeled honest and
  attacker-owned identities for proof events and task routing; production
  authorization and recipient selection are not implemented by those tables;
- fresh abstract key IDs model a collision-free, non-exhausted prefix of the
  concrete `u64` allocator;
- the fixed sequence constructors model the particular record prefix being
  analyzed;
- the state-neutral receive process contains one exact short leg and one exact unrolled capacity-50 leg, and its symbolic forged frames represent inputs that have already passed the production parser, sender, and minimum-length gates;
- an admitted failed open may perform private derivation and callback work but publishes no chain, counter, or cached material, while a successful future target publishes only its skipped entries and consumes its separate target;
- the only honest-party state compromise is the synchronized beacon snapshot or state-neutral receive snapshot described above; each scenario has one synchronized snapshot, and every baseline or receive top level that instantiates attacker-owned registration exposes those beacon secrets from the start; and
- the handwritten event placement, wire constructors, processes, and three
  simplified function definitions faithfully represent the corresponding
  production behavior.

If production later permits multiple registration bundles under one identity,
the one-owner replay refinement is no longer sufficient. The signed fields need
an authenticated bundle nonce or an ordered whole-bundle signature before the
current origin/replay argument can be extended.

### Verification-tool assumptions

The result also trusts the correctness of rustc for the extracted core, hax and
its Rust/F* models, the F* checker, Z3, ProVerif, their libraries, the build
scripts, and the reviewed extraction selection. PQXDH's exact byte-range proofs
specifically rely on three specification-only range-update contracts supplied
by the pinned hax proof library; their stated prefix/range/suffix behavior is
trusted rather than proved in this repository. The little-endian key-ID proof
also relies on a specification-only right-shift lemma equating bounded shifts
with division by the corresponding power of two
([inventory](../beaconcrypt-core/proofs/trusted-boundary.md#proof-library-and-tool-assumptions)).
The handwritten AWK result classifier is likewise trusted to recognize every
required ProVerif query and classify its output correctly. The repository
prevents local proof shortcuts by rejecting `assume` and `admit` in
repository-owned F* files
and rejecting checker flags that would permit missing proofs
([policy gate](../beaconcrypt-core/Makefile#L135-L147)). This does not remove
assumptions or trusted interfaces from external hax/F* libraries.

Stage 9 now records the opaque functions, primitive laws, adapter refinements,
proof-library interfaces, generated exceptions, and handwritten model fragments
in the canonical
[trust-boundary inventory](../beaconcrypt-core/proofs/trusted-boundary.md).
Its manifest and structural checks make unacknowledged boundary drift fail the
verification gate. Updating the recorded hashes can make an intentional change
pass, so this is a review-control improvement, not a proof of the inventoried
assumptions or of the adequacy of a human review
([Stage 9 scope](impl/formal-verification-stage-9.md#result-and-scope)).

## How the theorems yield concrete security statements

No single theorem spans source code, real cryptography, persistence, and an
attacker. The recurring bridge is:

```text
extracted-code theorem + cryptographic assumptions + faithful adapter and state
management + protocol-model theorem = conditional production security claim
```

Concrete statements come from composing those pieces. The following worked
examples make that composition explicit.

### 1. Both honest roles derive matching session material

1. Primitive correctness must give the beacon and server the same ordered DH1 through DH4 values and the same ML-KEM shared secret.
2. F* then proves both roles build the same exact 192-byte root input, and `authenticated_registration_derives_common_fixed_root` proves that authenticated equal transcripts have one common root under the same fixed pure derivation.
3. Production must faithfully and totally implement that derivation as HKDF-SHA-512 over the exact transcript with `PQXDH_INFO`; the theorem does not supply those semantics.
4. In the predecessor F* artifact, `authenticated_registrations_establish_concrete_session` composes that common root with role-bound executor constructors and proves both opposing material equalities at an arbitrary sequence.
5. The current initial KDF continuation records the role direction and constructs the kernel only after a typed response, but Lean still needs to prove that both role phases create related opposing chains and that send/receive phase composition preserves their paired ideal-session invariant.
6. ProVerif's beacon-commit-to-server-commit correspondence adds active-network agreement on both identities, root input, symbolic root, associated data, assigned ID, and session.

The defensible current statement is therefore narrower: **the protocol models and predecessor F* artifact establish the intended complementary-session construction under their assumptions; Lean checks the current initial request, response split, role offsets, send begin/resume/ideal success plus cancellation, structural send outcomes, and the stated receive slices, but it does not yet compose the two initialized roles into a paired ideal session.** Until that composition is checked, one must not claim that Lean already proves current production's all-sequence opposing material equality. No proof here authenticates the complete network run or proves HKDF or AEAD semantics.

### 2. Signed prekey and one-time-key fields cannot be substituted

1. F* proves prekeys and one-time keys have distinct role bytes inside the
   core-produced encodings and that either role is rejected as the other. It
   does not prove which bytes production signs.
2. The adapter must translate the wire fields exactly, sign and verify the
   complete role-bearing encodings, and pass those authenticated bytes to the
   core.
3. ProVerif assumes ideal signature unforgeability and that one fresh honest
   identity emits one bundle, then proves server acceptance corresponds to the
   exact role-bearing initiation of that beacon.

Together these rule out swapping or duplicating those signed fields in the
modeled active-attacker run, under the one-bundle-per-fresh-identity assumption.
The conclusion still depends on real Ed25519 unforgeability and faithful wire
parsing. If one identity can emit multiple bundles, these separate field
signatures do not by themselves rule out cross-bundle splicing.

### 3. The assigned beacon ID cannot be changed independently

1. F* proves the candidate binding is the exact eight-byte little-endian form
   and rejects every unequal eight-byte value.
2. The production Rust API allows state to be finalized only after the binding
   check, provided the adapter passes the value obtained from successful
   authenticated decryption.
3. ProVerif's ideal frame-opening rule requires the exact frame material and
   its commit correspondence includes the same assigned ID on both sides.

Thus an accepted, committing beacon cannot be given one authenticated inner ID
while publishing a different outer ID, subject to AEAD integrity and provided
the surrounding code passes the value obtained from successful authenticated
decryption. The F* byte comparison alone would not prove that the input was
authenticated.

### 4. A registration cannot be accepted twice locally

1. F* proves the semantic replay ID is the exact fixed-width identity/one-time
   key pair and that a `Consumed` status is rejected.
2. The production adapter must atomically and durably refine the real set to
   `Fresh`/`Consumed`, insert before returning a pending token, and never roll it
   back.
3. ProVerif models that obligation as one private replay owner and proves
   injective initiation/consumption/acceptance correspondences.

The resulting claim is local to one honest identity, one bundle, and one
non-rollback persistence owner. It does not extend automatically to replicas,
restored forks, or multi-bundle identities.

### 5. An accepted record has an authentic origin and cannot be replayed

1. The ordinary ideal ProVerif `open_frame` succeeds only with exactly matching key material, associated data, sequence, and sender ID.
   This assumption supports the record correspondence but does not itself demonstrate CTX's benefit.
2. In a separate deliberately multi-opening base-AEAD theory, the identical double-open query is unreachable with CTX and reachable when CTX is removed.
3. F* proves that any two distinct accepted explanations of one fixed ciphertext, tag, and commitment yield an explicit collision between distinct production transcript inputs for arbitrary pure hash and AEAD-open functions.
4. Lean machine-checks a factor-one reduction from the corresponding ideal-model misattribution advantage to BLAKE2b-512 collision advantage and preserves that bound for dedicated record-opening games in which an adversary changes the sequence number, sender identifier, or session associated-data bytes of an honestly sealed record. A separate honest-run eliminator proves that every `beaconFinish` outcome after record admission contains the exact successful target opening, the reordered-first-record and foreign-session games compose it into factor-one transition bounds for a fixed honest run, and the pinned-sender precheck gives the protocol wrong-sender game exactly zero advantage without a cryptographic assumption; session interpretation relies on field provenance, and PPT/runtime preservation, collision resistance itself, and the extracted-to-ideal production bridge are not mechanized.
5. The ordinary model's injective receive-to-send correspondence proves that every accepted record in the fixed schedule has a unique send with the same session, direction, sequence, peers, and plaintext.
6. The current core supplies the exact old chain and `SYM_RATCHET_INFO` in an owned request and constructs fixed 32-byte key, 32-byte next-chain, and 12-byte nonce values from a typed response. Checked Lean equations prove that construction and partition, while `ResponseRefines` states the semantic KDF law and `SendKdf.resume_refines` applies it to the send path; the staged future-receive induction remains open.
7. The predecessor F* artifact links authenticated equal root transcripts to complementary role kernels and preserves its concrete derivational invariants through callback operations. Current Lean proves send begin/resume/ideal success plus cancellation, failed receive traces, and conditional cached success, while structural equations cover exhaustion and either seal result; initial role composition, future receive success, restoration, and the adapter-driver composition remain open.
8. Consequently, if the concrete canonical key/nonce outputs do not collide at distinct allocations and production preserves one authoritative no-fork/no-rollback state, monotonic allocation cannot reuse a key/nonce pair in the claimed stream. The maintained Rust API enforces affine operational ownership, and `PersistentServer` fences restoration and results by external generation/head CAS, but F* proves neither those mechanisms nor the noncollision premise; bypass, a broken store, or rollback can repeat the same sequence material.
9. Production must faithfully and totally implement PQXDH root HKDF with `PQXDH_INFO` and each core-owned symmetric request with HKDF-SHA-512, and its synchronous effect driver must correctly convert borrowed core arrays into ephemeral libsodium values and implement commitment/AEAD semantics. Restoration additionally relies on the canonical codec and on `SnapshotStore` to provide payload integrity/provenance plus a linearizable, durable, rollback-resistant head; none is verified by Lean, F*, or ProVerif, and no cryptographic snapshot authentication or encryption is provided.
10. Production frame parsing, sealing, opening, commitment hashing, and sender lookup must match the models. The extracted builder and F* lemmas establish the exact key, nonce, associated data, AEAD tag, little-endian sequence, and little-endian sender-ID layout; the adapter must still supply those values from the intended authenticated context and hash the returned bytes. Core arrays zeroize on `Drop` as a Rust implementation measure, but physical/compiler erasure and retained external copies are not F* conclusions.

This supports concrete record integrity, peer/session binding, replay rejection, and conditional CTX misattribution resistance on the high-level path only under those primitive, frame, and adapter assumptions.
The production commitment transcript helper and fixed-width pointwise collision implication are F*-proved, and Lean proves the factor-one probability reduction on the ideal-model surface for general misattribution and dedicated wrong-sequence, wrong-sender, and cross-session record-opening games. Lean also extracts pinned-sender equality, nonzero sequence, and exact record-opening success from the ideal beacon's post-record outcomes, proves factor-one reordered-first-record and foreign-session admission bounds for a fixed honest run, and proves exact zero advantage for protocol wrong-sender admission; the lower sender game remains a record-layer fact, while PPT/runtime preservation, the representation bridge, the caller, BLAKE2b, parsing, session interpretation, and field provenance remain computational, adapter, or primitive obligations. The injectivity proof now applies one embedded-segment equality lemma at each of the six transcript offsets instead of repeating the same sequence-extensionality argument for every field; this is a proof-structure refactor and does not alter the transcript layout or injectivity statement.
ProVerif supplies the active-attacker origin argument for its bounded schedule and the supplementary CTX/no-CTX control, F* supplies the fixed-width pointwise collision witness plus general derivational reachability and consumption preservation, Lean supplies the ideal-model computational reduction, and the remaining adapter refinements must connect those facts to concrete frames and keys.

The sequence and key ID are authenticated/bound metadata, not secret metadata:
they remain visible on the wire.

### 6. Deleted-key forward secrecy and lack of recovery

1. From a reachable state, F* proves that refined receive consumption removes the complete record containing the canonical material for the target sequence and preserves reachability for all surviving records; production must still avoid rollback and retained copies outside the authoritative state.
2. The ProVerif compromise process reveals only the live chain and cached key at
   one exact later point.
3. Ideal one-way ratchet constructors prevent deriving old, removed material
   from the live chain, so the initial and sequence-3 secrets remain unknown.
4. The same process gives the attacker the cached sequence-2 key and chains for
   future inbound and outbound keys, producing explicit attacks on those three
   secrecy queries.

The precise statement is: **at this one snapshot, the named initial and
sequence-3 secrets remain secret; cached sequence 2 and the modeled next inbound
and outbound secrets are exposed.** No theorem says that every message whose
key is marked unavailable is forward-secret. This is not arbitrary-time,
server-side, persistence-aware, or physical-erasure forward secrecy.

### 7. Every normally rejected receive is state-neutral

1. Production parsing and sender selection first choose the legitimate peer and reject malformed, short, or wrong-sender frames before ratchet admission, leaving that peer and every unrelated peer unchanged.
2. Production calls `begin_receive` with the entry kernel, parsed target, and opaque `OpenFrameContext`. Admission or lookup rejection returns that exact kernel; an admitted future target emits one `ReceiveKdfRequested` phase per required derivation, and each adapter response updates only the affine continuation's private working control and staged skipped records. The final `ReceiveOpen` exposes exactly one selected material/sequence/context triple to `open_frame`.
3. `ReceiveOpen::finish(None)`, explicit `reject`, and KDF `cancel` return the complete entry kernel, including control, both chains, and every material slot. The checked `ReceiveFailureTrace` theorem proves exact entry recovery and preservation of `KernelRefines` for any supplied finite failure-trace witness, including witnesses with staged KDF resumes; a separate reachability theorem from every `begin_receive` execution is still absent. `finish(Some(plaintext))` alone publishes the prevalidated cached whole-record removal or the future skipped-only cache, final receive chain, and post-target-consumption control. Lean derives the generated cached open from `KernelRefines` plus an ideal lookup, proves conditional open-reply consistency and cached success directly against cached `recvStep`, and proves the consumed control state refines ideal skipped-key filtering. Full post-state refinement remains conditional on the material-array `CachedPublicationRefines`, and effect-level future publication remains open even though the generated control driver directly refines the ideal bound-50 step.
4. The core constructs every request from the exact current chain and `SYM_RATCHET_INFO` and privately partitions typed responses, but the adapter must faithfully compute each response and open result. Restoration establishes derivational reachability only under canonical provenance premises. Concrete HKDF and AEAD semantics, driver side effects or panics, serde/store correctness, trusted payload provenance, compiler and physical-erasure behavior, crash handling, and rollback resistance remain outside the current theorems.
5. The private ProVerif scenario shows that an active network attacker without the legitimate receiver snapshot cannot derive the six named plaintexts even while concurrent attacker-owned registration processes commit a response and expose their own routed canary. Both record legs use standalone fresh roots, so peer/root separation remains an adapter obligation.
6. In the compromise variant, the snapshot repeats the exact same state term before and after rejection and exposes no cached material. Revealing its unchanged live chain still derives the future skipped and target materials, decrypts their public authentic ciphertexts, and enables a forged accepted frame. If the attacker instead forwards the honest ciphertext first, a freshly prepared candidate accepts it, consumes the target on success, rejects replay, and allows delayed skipped-key delivery.

The defensible statement is therefore: **in the combined private symbolic run, an attacker-controlled registered beacon has no path into the independently rooted state-neutral receive sessions, and forged receive rejection neither enlarges nor exposes the legitimate protocol state; under the production role-specific selection and independent-root refinements, direct compromise of the unchanged live chain still exposes its future material and removes the honest-origin guarantee for those keys.** The exact short and capacity orderings provide finite ProVerif cryptographic and schedule witnesses. The predecessor F* artifact gives general rollback/publication evidence for its callback design, while current Lean proves exact rollback for supplied finite failed-phase trace witnesses, generated cached-open construction, the control-plane half of cached consumption, and conditional cached success. It does not yet prove that every execution constructs such a failure witness, prove future success, prove cached material-array publication, or verify the adapter driver. Neither proof supplies production driver fidelity, principal/peer isolation, trusted snapshot provenance, parser correctness, an end-to-end registration-to-record state linkage, concrete output noncollision, memory erasure, availability, or post-compromise recovery by itself.

## Verification and reproducibility

The current proof entry point is:

```sh
make -C beaconcrypt-core verify
```

It enters the locked Nix environment, checks exact tool identities, regenerates F*, ProVerif, and no-exclusion Lean extraction, enforces the local no-`assume`/no-`admit` policy, strictly checks generated and handwritten F*, builds the imported Lean project, and runs all ProVerif scenarios through separate targets. Each ProVerif scenario can also be checked directly with `make -C beaconcrypt-core check-proverif-<scenario>`, while `make -C beaconcrypt-core verify-lean` regenerates and builds Lean in the pinned environment. After intentional boundary diffs have been reviewed and their hashes refreshed, the separate `make -C beaconcrypt-core check-inventory` command checks the trust-boundary inventory. The reviewed F*/ProVerif tool bundle is recorded in the [Stage 8 document](impl/formal-verification-stage-8.md#locked-proof-bundle).

The historical Stage 3 through Stage 9 documents describe how the predecessor boundary was built. Older tool versions, hashes, test counts, executor/callback architecture, and failure-retention behavior describe their stage at that time. The checked current claims add the Lean control-to-ideal refinement, `RatchetEffect.lean` structural phase equations, and the imported `RatchetEffectRefinement.lean` semantic results described above to the retained F*/ProVerif results. The old F* concrete specialization is no longer a current-production theorem. Stage 9's maintained [trust-boundary inventory](../beaconcrypt-core/proofs/trusted-boundary.md) records that split explicitly.

The result gate requires exactly:

- the shared weak-AEAD multi-opening query to be true (unreachable) with CTX and false (witnessed) without CTX;
- all 11 baseline queries to be true: five secrecy and six correspondence results;
- all seven negated reachability/non-vacuity queries to be false, including a committed attacker-owned registration and attacker recovery of its routed canary;
- exactly two true and three false original late-compromise secrecy results;
- all 17 private state-neutral receive queries to be true (six secrecy and eleven state/origin correspondences), with all twelve receive reachability negations false (ten rejection/success phases plus malicious-registration commit and malicious-canary recovery); and
- in the nine-query state-neutral receive compromise run, consumed-past and all three independently rooted capacity-leg secrecy results plus both compromise-order correspondences are true, short-leg skipped/target secrecy and honest-origin correspondence are false, and both unchanged-state compromise and later-honest-delivery reachability negations are false.

The dated validation records below predate the first-order effect refactor and establish only their named repository snapshots. They must not be used as evidence that the new no-exclusion Lean extraction or phase laws were checked; the current change requires its own successful canonical run and reviewed generated diff.

During final receive-slot conformance verification on 11 August 2026, `cargo test --locked -p beaconcrypt-core`, `cargo test --locked`, `make -C beaconcrypt-core verify`, and `make -C beaconcrypt-core check-inventory` completed successfully against the repository state represented by this report. Repeating extraction after the reviewed generated update produced no additional generated diff. All F* verification conditions were discharged, every ProVerif classification matched the reviewed result set above, and the refreshed trust-boundary inventory matched the reviewed adapter, core, and proof inputs.

After the subsequent derivational-reachability update on 11 August 2026, `cargo fmt --all -- --check`, `cargo test --locked -p beaconcrypt-core`, `cargo test --locked`, `cargo clippy --locked -p beaconcrypt-core --tests -- -D warnings`, `make -C beaconcrypt-core CACHE_DIR=/tmp/beaconcrypt-fstar-cache verify`, and `make -C beaconcrypt-core check-inventory` completed successfully. The full locked proof run regenerated no changed F* or ProVerif artifact, discharged every F* verification condition including the new reachability and conditional-restoration lemmas, and matched every reviewed ProVerif classification.

After the ratchet work and Server/Beacon split were combined on the `proof` branch on 11 August 2026, the inventory tripwire detected changes in `beaconcrypt/build.rs`, `beaconcrypt/src/cbinds.rs`, `beaconcrypt/src/lib.rs`, `beaconcrypt/src/pqxdh.rs`, `beaconcrypt/src/pybinds.rs`, `beaconcrypt/src/shared.rs`, and `beaconcrypt/tests/protocol.rs`. Substantive review confirmed that the split preserved the extracted-core calls, authenticated transcript layouts, ratchet helpers, five-field persistence format, and registration commit ordering, but also found that the merge had dropped adapter regressions for signed Phase-1 field/type/role mapping and registration-key disposal. Those regressions were restored in `beaconcrypt/src/pqxdh.rs`, the trust-boundary mappings were updated to the concrete role APIs, and the eight affected fingerprints, including `proofs/trusted-boundary.md`, were refreshed. The resulting baseline was accepted only after the full Rust suite, clippy, both role-only builds, `check-inventory`, and `check-generated` passed. F* and ProVerif extraction remained unchanged, so this reconciliation changes no theorem, symbolic model, or proof result.

The workspace-layout migration renamed the proof module namespace from `Beaconcrypt_protocol_core` to `Beaconcrypt_core` without changing any theorem statement, model rule, query, or expected result. That symbol rename perturbed one previously implicit F* refinement discharge in `receive_control_prefix_matches_for_equal_prefix`; its proof body now states the already-derived `v slot < 50` fact explicitly before assigning the bounded cache index. This changes neither the theorem preconditions nor its conclusion and makes the proof independent of solver behavior tied to generated symbol names.

The checker rejects missing or substituted queries, timeouts, unknown or
inconclusive results, and any changed classification
([checker](../beaconcrypt-core/proofs/pro-verif/check-results.awk)).

For CI and reviewed generated artifacts, use:

```sh
make -C beaconcrypt-core check-generated
```

That runs the same suite and rejects tracked or untracked extraction drift. The dedicated formal-verification workflow distributes the equivalent F* and per-scenario ProVerif generated checks across independent matrix jobs, then reports the established aggregate status only when every component passes. Run `make -C beaconcrypt-core check-inventory` separately to check monitored trust-boundary membership and fingerprints. Together, those commands make the proof reproducible and prevent a query, monitored trust-boundary file, or generated file from silently disappearing or changing without an explicit baseline update. They do not prove that the handwritten model is faithful to production or that the reviewed assumptions hold; those conclusions still require substantive review beyond the mechanical Stage 9 gate.

## Safe summary wording

In ordinary language: the proof gives strong evidence that selected core
bookkeeping follows its specification and that a simplified protocol resists
an active network attacker for the particular exchanges modeled. The guarantee
depends on real cryptography, surrounding code, storage, and deployment
preserving the assumptions; those parts are not proved end to end.

For an audit or security statement that needs exact scope, use:

> Beaconcrypt formally verifies selected extracted PQXDH and symmetric-ratchet
> control functions for exact transcript construction, checked state
> transitions, bounds, and logical key lifecycle. A complementary ProVerif
> model proves fixed-trace secrecy and injective authentication properties
> against an active symbolic network attacker. Replicated attacker-owned
> beacons can submit valid self-signed registrations; the server can commit
> their responses and the attacker can recover their routed canary without
> exposing the five honest-session canaries. The model also
> precisely documents two named deleted-key secrecy results at one snapshot,
> cached-key exposure, and absence of post-compromise security. These guarantees
> are conditional on ideal cryptographic assumptions, faithful adapters and
> handwritten modeling, correct application recipient routing, high-level
> non-rollback execution, and the stated replay-owner and compromise scope; the
> complete application and primitive implementations are not formally verified.
> For the symmetric ratchet specifically, production stores one affine `ConcreteRatchetKernel` with direct fixed-width chains and a sequence-tagged fixed cache but no executor or function pointer. The core emits typed initial, per-step KDF, seal, and open phases; the adapter interprets each request synchronously, commits send advancement even when sealing fails, and publishes receive advancement only when opening succeeds. The target is consumed separately and never occupies the 50-entry skipped-key cache. The complete default core translates to Lean without module exclusions, and the generated control driver directly refines the ideal `Ratchet.recvStep` at that bound. Imported Lean theorems precisely relate the concrete kernel to ideal send/receive state, assume an explicit ideal KDF-response law, prove non-exhausted send begin/resume/ideal success plus cancellation and rollback for supplied finite failed-trace witnesses, conditionally relate open replies to the selected material and ideal decryption, construct the generated cached-open phase from `KernelRefines` plus an ideal lookup, prove the control-plane half of cached consumption, and prove conditional cached success against cached `recvStep`; structural equations separately cover exhaustion and advanced-state return for either seal result. Remaining work is to prove the cached material-array swap/empty-suffix publication relation, prove effect-level future KDF staging and publication, compose initialization and restoration, verify the adapter driver, and model ideal send exhaustion. The maintained high-level Rust adapter permits messaging only from establishment-gated state, returns inert update snapshots, and provides canonical snapshots plus generation/head CAS and loser fencing through `PersistentServer`. Its `SnapshotStore` is trusted for payload integrity and provenance, linearizable CAS, durability, and rollback resistance; snapshots have no cryptographic authentication or encryption. Lean, F*, and ProVerif do not prove the cryptographic interpreter, ownership, codec, store, panic/crash, or deployment mechanisms. Real key/nonce no-reuse remains conditional on faithful HKDF execution, output noncollision, and no fork/rollback, while physical/compiler erasure and absence of retained copies also remain outside the proof.
>
> A dedicated state-neutral receive trace rejects a forged future frame twice from the exact same receiver state, later accepts the authentic target while publishing only its skipped key, rejects replay, and accepts delayed delivery. A separate exact capacity leg advances from sequence 1 to sequence 52 with 50 skipped keys, consumes sequence 52 separately, rejects sequence 54 while the cache is full, consumes cached sequence 51, and then accepts sequence 54 while publishing sequence 53. Explicit compromise after rejection discloses the unchanged live chain and empty cache: future material is exposed because it remains derivable from that chain, not because rejection retained anything. The predecessor F* artifact proves general rollback, preparation, publication, replay, retry, and capacity properties for the callback-bearing source snapshot; current Lean proves the direct bound-50 control refinement, rollback for supplied finite failed-trace witnesses, generated cached-open construction, the control-plane half of cached consumption, and the conditional cached-success slice, while trace reachability, effect-level future success, and unconditional material-array cached publication remain open. The finite ProVerif traces supply concrete cryptographic and exact-schedule witnesses; byte-level parsing, adapter-driver fidelity, and arbitrary successful receive schedules remain outside them.
>
> F* proves the exact fixed-width production transcript, its injectivity, and the pointwise theorem that two distinct accepted explanations of one fixed payload produce an explicit collision witness for arbitrary pure hash and AEAD-open functions.
> Lean machine-checks the corresponding factor-one ideal-model probability reduction to BLAKE2b-512 collision advantage and dedicated factor-one wrong-sequence, wrong-sender, and cross-session record-opening specializations; the sender result is below the beacon's earlier pinned-sender check and cross-session interpretation relies on associated-data provenance, while PPT/runtime preservation and the extracted-production bridge remain unmechanized.
> A supplementary differential ProVerif control gives the base AEAD two distinct valid openings: CTX makes the double-open event unreachable, and removing CTX makes the same query produce a witness.
> The resulting real-world strong-commitment claim remains conditional on BLAKE2b collision resistance, correct libsodium behavior, production field provenance, and adapter/compiler correspondence.

Statements such as “the whole implementation is proven secure,” “all application messages are proven confidential,” “the cryptographic primitives are verified,” “F* proves replay or rollback impossible across replicas,” “the complete CTX implementation and BLAKE2b security are formally proved end to end,” or “beaconcrypt is post-quantum secure against active attackers” are not supported by the current proof corpus.
