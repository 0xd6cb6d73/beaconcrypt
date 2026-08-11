<!-- SPDX-License-Identifier: 0BSD -->

# What beaconcrypt's formal verification proves

## Purpose and bottom line

This document explains the formal-verification results in plain language. It is
an audit of the proof sources currently in the repository, not a list of future
goals. It compares the claims in the formal-verification documentation with the
F* and ProVerif files under
[`crates/protocol-core/proofs`](../crates/protocol-core/proofs).

The short conclusion is:

- F* proves useful, universal facts about selected deterministic Rust functions: exact PQXDH byte layouts and state transitions, ratchet bounds, receive sequence-to-slot lookup, append/removal/restoration slot shape, logical key consumption, replay behavior, checked counter handling, and the CTX transcript and pointwise collision-witness properties described below.
- The receive-slot theorems remove independent production decisions about where a logical sequence belongs, but concrete HKDF output, key/nonce association, Rust array mutation, serde, authentication-result provenance, and publication atomicity remain adapter obligations.
- ProVerif proves secrecy and authentication properties for an active-attacker
  symbolic model of registration and a fixed record-exchange schedule. It also
  demonstrates the expected exposure of cached and future keys after one
  precisely timed beacon-state compromise.
- A dedicated failed-active-receive model makes the pre-authentication ratchet/cache transition explicit, exercises the exact 50-slot boundary, and distinguishes private retained state from compromise of that state before a later honest delivery.
- A separate ProVerif negative control deliberately gives one base-AEAD ciphertext and tag two valid openings under distinct keys, nonces, associated-data contexts, and plaintexts.
  The identical multi-opening query is proved unreachable with CTX and is deliberately reachable when the CTX check is removed.
- F* proves the exact 229-byte production commitment transcript layout, injectivity of both `u64` encodings and the complete six-field input, and that two distinct accepted explanations of one fixed payload yield an explicit collision witness for arbitrary pure hash and AEAD-open functions.
- These results do **not** constitute an end-to-end proof of the complete Rust
  application, its adapters, the cryptographic libraries, persistence, or the
  deployed executable. The strongest production claims are conditional on the
  assumptions and implementation-to-model connections listed below.
- The proof does **not** establish general computational or post-quantum security of the primitive implementations.
  The CTX result has a conventional computational lifting from its machine-checked pointwise collision witness, but the probability and runtime theorem is not mechanized and remains conditional on BLAKE2b-512 collision resistance and faithful production refinement.
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
| F* theorem | A fact holds for all inputs satisfying the theorem's preconditions, for the selected Rust functions translated by hax. | Cryptographic security, adapter correctness, persistence, or behavior outside the extracted functions. |
| ProVerif result | No attack exists, or a stated attack does exist, in the handwritten symbolic protocol and ideal-cryptography model. | Computational security or automatic correspondence with the full Rust program. |
| Rust regression, known-answer, or Wycheproof test | The tested implementation behaves correctly on finitely many concrete examples. | A universal proof for all possible inputs and executions. |
| Assumption or refinement obligation | A fact needed to connect one verified layer to another. | Nothing by itself; it must be justified by implementation review, testing, another proof, or an operational control. |

Some terms used below are worth defining:

- **F*** is a programming language and proof checker. Here, hax translates a
  selected subset of the Rust protocol core to F*, and handwritten lemmas state
  facts about those translated functions.
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

The two proof systems have different source connections:

```text
selected deterministic protocol-core Rust
              |
              +---- hax F* extraction ---- generated F* definitions
              |                                      |
              |                                      +---- handwritten F* lemmas
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

The F* path is the stronger source connection. The build selects the exact
commitment, ratchet, and PQXDH Rust items in the
[`HAX_ITEMS` list](../crates/protocol-core/Makefile#L13-L45), regenerates their
F* definitions, then checks the generated modules and handwritten lemmas
with every proof obligation required—the checker is not allowed to accept a
missing proof. Subject to trusting hax and its Rust model, these lemmas are about
those selected Rust functions rather than a second handwritten protocol
implementation.

The generated F* view exposes some record constructors and fields that are
private in Rust, so a lemma can construct states that ordinary Rust callers
cannot. The composed handshake theorem explicitly calls the authentication
transition, but an isolated field-preservation lemma is not by itself proof
that a value came through the production validation path
([exception](../crates/protocol-core/proofs/trusted-boundary.md#generated-code-exceptions)).

The ProVerif branch is parallel to, not generated from, the F* branch. Hax emits
the selected data-type declarations, but its three relevant operations—
registration-ID construction, root-input construction, and associated-data
construction—use trusted handwritten simplified function definitions embedded
in the Rust source. The root-input definition models only the successful path;
it omits Rust's all-zero-DH error, which F* checks separately.
The wire protocol, ideal cryptographic rules, honest participants, replay
owner, compromise schedule, proof-bookkeeping events, and security questions
are also handwritten. This boundary is described in the
[Stage 7 implementation record](formal-verification-stage-7.md#generated-proverif-boundary)
and the [generated-code exceptions](../crates/protocol-core/proofs/trusted-boundary.md#generated-code-exceptions),
and the resulting rules are visible in
[`lib.pvl`](../crates/protocol-core/proofs/pro-verif/extraction/lib.pvl#L347-L357).
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

After registration, each direction uses a **symmetric ratchet**: a one-way
chain advances to a new key for each sequence number. If sequence 3 arrives
before sequence 2, the receiver may derive both keys, use key 3, and temporarily
cache key 2 for the delayed record. The cache is bounded to 50 entries. This
report distinguishes proofs about the ratchet's counters and bookkeeping from
proofs about the secret key bytes that production code associates with that
bookkeeping.

Production parses the frame, checks the sender and minimum protected-payload length, and then performs receive admission. Once a correctly shaped future frame is admitted, the receiver derives through the attacker-selected sequence and caches the intermediate and target keys before checking the commitment or AEAD. A failed open retains that complete post-admission state. The retry is state-neutral only relative to the retained state, not relative to the state before the first forged frame.

## Concrete properties proved by F*

### Commitment transcript and collision witness

The production BLAKE2b wrapper delegates byte construction to the selected `no_std` [`build_commitment_transcript`](../crates/protocol-core/src/commitment.rs) helper.
The checked [`Commitment.Lemmas.fst`](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Commitment.Lemmas.fst) module proves that its 229 output bytes are exactly the 32-byte key, 12-byte nonce, 153-byte associated data, 16-byte AEAD tag, little-endian 64-bit sequence, and little-endian 64-bit sender ID in that order.
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
[`Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst`](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst).

| Area | Exact machine-checked result | Important qualification |
| --- | --- | --- |
| Public-key encodings | The Ed25519, ML-KEM-768, and X25519 type markers and the two X25519 role markers have the documented distinct byte values. Each encoding preserves the key bytes exactly; encoder/decoder pairs round-trip; a prekey encoding is rejected as a one-time key and vice versa ([marker and role lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L74-L178)). | Signature verification occurs outside the core. The theorem proves what bytes are tagged and decoded, not that Ed25519 authenticated them. |
| Honest `InitKex` construction | A value made by `beacon_start` is accepted by `validate_init_kex` and yields exactly the four original public keys and expected pending state ([theorem](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L180-L207)). | This is a constructor/validator round trip, not an attacker-controlled wire theorem and not a proof that only one bundle can ever be emitted. |
| Server trust-anchor binding | `BeaconFresh` stores the expected server public key and numeric identity-key ID together. `beacon_start` preserves both fields in `BeaconInitSent`; a different response public key is rejected; a successful finish copies both fields into the candidate and derives associated data from the stored public key; post-open authentication rejects a different sender ID; and commit preserves the pair in `BeaconEstablished` ([state preservation](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L180-L221), [finish and authentication](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L482-L634), [acceptance-implies-agreement theorem](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L764-L816)). | The constructor must still receive the authentic compiled-in binding, and the adapter must truthfully pass the parsed response key plus the sender ID and assigned-ID prefix returned by the successful initial open. The acceptance theorem assumes no stored/accepting binding equality: successful key and ID checks derive both fields' equality with the accepting server candidate. The proof prevents later mutable-map replacement from redefining the expected binding; it cannot repair a trust anchor replaced before construction. |
| Registration identifier | The identifier is exactly the fixed-width beacon identity followed by the one-time X25519 key ([theorem](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L223-L230)). | This avoids a hash-collision assumption for the encoding. Freshness, one-time use, persistent insertion, and absence of rollback are not established by this theorem. |
| Root-key input | When none of the four 32-byte DH outputs is the all-zero array, the 192 bytes are exactly `0xff` repeated 32 times, followed by DH1, DH2, DH3, DH4, and the ML-KEM shared secret in that order. If any DH output is all zero, construction returns `InvalidDhOutput` ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L232-L338)). | The KEM secret is not required to be nonzero. This proves the input to later key derivation, not the HKDF implementation or its output. |
| Honest-role input agreement | If the adapters supply byte-identical DH1 through DH4 values and byte-identical ML-KEM secrets, the two roles return the same root-input result ([theorem](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L340-L353)). | X25519 and ML-KEM agreement are preconditions. Equal concrete root keys additionally require both adapters to apply the same deterministic HKDF with the intended `PQXDH_INFO` label. |
| Associated data | The 153 bytes are exactly the tagged server identity, tagged beacon identity, `PQXDH_INFO`, and `SYM_RATCHET_INFO`, in that order. Equal role identities give equal associated data ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L355-L478)). | The adapter must actually supply the returned bytes to authenticated encryption (AEAD). The theorem does not prove AEAD security. |
| Ratchet direction | Beacon-send matches server-receive at offset 32, and beacon-receive matches server-send at offset 0, for the two halves of a 64-byte result ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L525-L547)). | The actual HKDF operation, byte buffer, slicing, and storage are outside F*. |
| Authenticated response IDs | The assigned-ID binding is the exact eight-byte little-endian encoding of the `u64`. The authentication transition requires both the initial frame's sender ID to equal the candidate's pinned server identity-key ID and the assigned-ID bytes to equal the candidate binding; either mismatch is rejected, and commit preserves the complete server binding plus assigned ID ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L549-L634)). | The numeric sender and eight assigned-ID bytes must really be the values returned by a successful initial AEAD open. F* accepts those values as inputs; it does not prove their wire or AEAD provenance. |
| Replay status and pending acceptance | `Fresh` is admitted, `Consumed` is rejected, and a fresh successful `server_accept` returns the exact pending values without advancing the live core counter ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L636-L686)). | The persistent set lookup and insertion are outside F*. The adapter supplies the `Fresh` or `Consumed` classification. |
| Allocation and server transaction shape | The next key ID is mathematical increment by one or explicit exhaustion at `u64::MAX`; it cannot wrap. A different server binding and an adapter-reported occupied ID are rejected. An available ID produces the exact proposed state and peer; pure commit returns that proposal and pure abort returns the previous state ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L688-L762)). | The adapter supplies truthful availability. F* proves return values, not atomic mutation of the production counter, map, ratchet, or persistent storage. |

In plain language, these results remove ambiguity from the bytes both sides are
supposed to use, reject several dangerous boundary cases instead of wrapping or
silently continuing, and show that the pure state machine returns the intended
pending or committed values. They matter because swapping a key role, changing
an identity, reusing a registration, or assigning a different ID should change
or stop the run. They do not establish that the surrounding code performed the
cryptography, database operation, or state publication correctly.

For the server trust anchor specifically, the deployment assumption now enters the verified state once rather than being re-created by a peer-map lookup during finish. The F* lemmas follow the original public-key/ID pair from fresh state through `BeaconInitSent`, candidate, authenticated response, and established state. A focused theorem assumes no equality between that stored pair and an accepting server candidate; when response-key preparation and sender-ID authentication both succeed, it derives equality of both fields throughout those states. Production still has to construct the initial pair from the intended compiled-in values and accurately report the response fields authenticated by the initial open.

The broadest PQXDH theorem is
[`conditional_honest_run_correspondence`](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L818-L941).
It assumes a non-exhausted counter, a registration whose beacon identity matches the pending beacon state, four valid and pairwise-equal DH results, an equal KEM secret, `Fresh` replay status, an `Available` next ID, and field-by-field equality between the accepting server binding and the binding already retained in beacon state so that it can state a complete honest successful run. The response public key and successfully opened sender ID are still checked by the beacon transitions, and this broad theorem invokes the separate acceptance-implies-agreement result in its successful server-candidate branch. The production adapter, not either theorem, must authenticate the wire provenance of those values. Under those conditions the broad theorem proves equal root inputs, equal associated data, equality of both server-binding fields, the same assigned peer ID and binding bytes, complementary ratchet directions, successful binding authentication, and matching committed core peer data.

That theorem describes the result after inputs have already been validated and
both parties follow the protocol. It does not itself verify signatures, wire
provenance, secret agreement, AEAD, set/map lookups, actual network behavior,
or actual publication. It should not be read as an active-attacker handshake
proof; that is the separate ProVerif layer.

### Symmetric-ratchet control state

The F* ratchet deliberately models sequence numbers and **logical key capabilities**, not the secret chain bytes, concrete message keys, or nonces. A logical capability is bookkeeping that says “the key for sequence 2 should be available”; it is not the key itself. The logical receive cache is a packed fixed array, and production stores opaque `KeyMaterial` in a parallel fixed array. For example, after sequence 3 arrives first, the model may contain capabilities for sequences 2 and 3. Successful authentication of sequence 3 consumes capability 3 while capability 2 remains for the delayed record. Production code separately has to derive, retain, move, and delete the matching secret bytes.

The ratchet invariant says the active receive cache has at most 50 entries; every active entry is nonzero, no greater than the receive counter, and unique ([ratchet lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst)). Uniqueness is what makes a successful sequence lookup identify one current physical slot even after an earlier swap-removal has moved entries.

The following properties are proved:

- Empty-cache constructors establish the invariant for arbitrary supplied counters.
- A successful send allocation increments the counter by exactly one, returns a capability for that same sequence, does not touch receive state, and cannot wrap. Exhaustion at `u64::MAX` changes no state.
- Sequentially finishing an available send capability marks the returned value unavailable; finishing that returned value again fails without changing it.
- A successful future receive plan reports a derivation count equal to the numeric gap; the plan itself derives nothing. Admission requires both a gap of at most 50 and total outstanding capacity of at most 50. Larger gaps and capacity overflow are rejected with a count of zero. An old or current target requires zero new derivations, but that result does not say its key is still present in the cache.
- Each successful receive advancement increments once, appends the exact new sequence, preserves the send counter and invariant, and reports the old cache length as the append slot. A full cache or exhausted counter is state-neutral.
- `lookup_receive_key` is characterized in both directions for valid states. A `Some(slot)` result names an active slot holding the requested sequence, a `None` result means the sequence is absent from the active cache, and uniqueness makes the returned active slot the only matching slot. Production can therefore treat `None` as authoritative instead of reproducing the scan in adapter code.
- `finish_receive_with_removal` is the sole detailed logical completion transition, and the compatibility `finish_receive` function is proved to return the same state and disposition. A wrong sequence/slot pair produces `Missing`, no removal, and unchanged state. Authentication failure produces `Retained`, no removal, and unchanged logical state. Authentication success produces `Consumed`, reduces the cache length by one, reports the target slot and the previous last slot, removes the target, preserves every other logical sequence exactly once, and moves the previous last entry into the target slot when the two slots differ.
- For a future sequence, planning and admitted advancement may already have moved the receive counter and cached bounded intermediate keys before authentication. Failure retains that advanced state and is not neutral relative to the start of decryption, so those advances can consume cache/window capacity. The composed failed-receive lemmas prove one-step pre-authentication advancement, zero-cost retry, later single consumption, replay rejection, exact full-cache rejection, and capacity release after consumption for arbitrary valid logical states satisfying their numeric preconditions.
- `restore_receive_key_with_slot` performs the checked ordered append and returns the old logical cache length as the slot containing the restored sequence. Successful restoration preserves validity, and the compatibility `restore_receive_key` function is proved to have the same accept/reject behavior and projected state. Finishing a valid restoration returns a valid state.
- Pointwise replacement leaves a peer record with a different ID unchanged. Mismatched send advancement returns no sequence and an unavailable capability; for the selected peer, the peer ID, ratchet, and sequence match direct send advancement.

The last result is pointwise: it does not prove that a production whole-map lookup selects one unique entry or updates the complete map correctly.

These facts prove the control algorithm and its physical logical-array decisions, not the secret-byte refinement or global ownership. In Rust, `RatchetState` and `SendKey` are copyable values. The “one-use” theorem threads the returned unavailable capability into the second call; it does not stop a caller from retaining a copy of the original available capability or forking old ratchet state. Concrete one-use and replay resistance therefore require one authoritative, non-rollback state and the adapter invariant

```text
for n = control.receive_cache_len():
    slot < n  => recv_slots[slot] contains the concrete key and nonce for the logical sequence in slot
    slot >= n => recv_slots[slot] is empty
```

The core-returned append, lookup, removal, and restoration slots eliminate independent adapter decisions about where a logical sequence belongs. The proof still cannot inspect `KeyMaterial`, so production must perform exactly one correct HKDF step after each successful logical advancement, store its output in the returned slot, use the current lookup result for the intended sequence, apply the exact returned swap/take before publishing the new logical state, and place persisted material in the returned restoration slot. Serialization and deserialization, authentication-result provenance, crash atomicity, physical erasure, and the compiled array operations remain outside F*.

The proof also accepts the `authenticated` flag as an input. The adapter must derive it from a sound commitment and AEAD check. `Retained` must cause no concrete slot mutation, while `Consumed` must drop only the concrete target identified by the verified plan.

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
([model](../crates/protocol-core/proofs/pro-verif/environment.pvl)). The separate
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

The ordinary record model's [`open_frame`](../crates/protocol-core/proofs/pro-verif/crypto.pvl) rule already requires an exact key, nonce-derived material, associated data, sequence, sender ID, tag, and ciphertext term.
Its record correspondence therefore establishes origin only under that ideal exact-opening rule; by itself it does not show what CTX adds to a non-key-committing AEAD.

The dedicated [`aead-commitment-negative-control.pvl`](../crates/protocol-core/proofs/pro-verif/aead-commitment-negative-control.pvl) instead defines one ciphertext/tag term with two successful reductions to distinct fresh plaintexts under structurally distinct key, nonce, and associated-data terms.
Both top-level scenarios run the exact same [`WeakAeadMultiOpened` query](../crates/protocol-core/proofs/pro-verif/aead-commitment-negative-control-queries.pvl): [`aead-commitment.pv`](../crates/protocol-core/proofs/pro-verif/aead-commitment.pv) must report the event unreachable because the one collision-free `ctx_commitment` term cannot validate both contexts, while [`aead-no-commitment.pv`](../crates/protocol-core/proofs/pro-verif/aead-no-commitment.pv) removes those checks and must produce a trace reaching the event.
The result classifier requires those exact opposite classifications.

This differential result supplements the F* pointwise theorem with an explicit ideal-hash CTX/no-CTX counterfactual and does not assume that the base AEAD is key committing.
It remains a symbolic result for one explicit multi-opening theory, not a computational proof of BLAKE2b or an end-to-end theorem about compiled Rust.
The [computational lifting](ctx-commitment.md) conventionally turns the F*-proved witness into an advantage bound under the separate collision-resistance assumption.

### Baseline secrecy

The five baseline secrecy queries in
[`queries.pvl`](../crates/protocol-core/proofs/pro-verif/queries.pvl#L7-L11)
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
[`queries.pvl`](../crates/protocol-core/proofs/pro-verif/queries.pvl#L13-L174).
The last correspondence is the basis for the modeled record-authentication,
cross-direction, cross-peer, cross-session, replay, and “a party cannot be
tricked about who shares the key” claims. Those are consequences of the event
arguments being equal, not separate general-purpose theorems. The modeled
schedule attempts each receive only once at each fixed sequence; general
duplicate receive-key consumption is instead the F* ratchet theorem plus the
production adapter invariant.

### Reachability checks

An implication can be vacuously true if its later event can never occur. For
example, “every accepted message was sent honestly” says nothing if the model
can never accept any message. Seven separate queries provide non-vacuity
controls
([queries](../crates/protocol-core/proofs/pro-verif/reachability-queries.pvl)).
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

### Failed active receive state and compromise

The dedicated [`failed-receive.pv`](../crates/protocol-core/proofs/pro-verif/failed-receive.pv) scenario addresses authentication failure after receive admission in the server-to-beacon direction. It gives the attacker public authentic ciphertexts and the ability to construct a syntactically admitted frame with an attacker-selected protected component. The receiver's ready, retained, full-cache, consumed, and refilled states are explicit symbolic terms, so a failed `open_frame` takes an `else` branch that publishes proof events and continues with the mutated state instead of silently blocking the process. F* proves the corresponding control transitions without a role/direction parameter, but ProVerif does not duplicate this cryptographic compromise trace in the beacon-to-server direction.

The finite execution exercises these transitions in order:

| Phase | Modeled state effect |
| --- | --- |
| Consumed past | An earlier honest record succeeds and its material is no longer in receiver state. |
| First forged future receive | Admission derives through the selected future target and caches both skipped and target material before authentication; failed authentication retains that post-admission state. |
| Exact cache fill | A farther correctly shaped forgery derives the remaining entries until all 50 slots are occupied; its failed authentication retains the full cache. |
| Capacity rejection | The immediately following future target is rejected without another chain or cache transition because no slot remains. |
| Retry and honest delivery | Repeating the first invalid target performs no further derivation; later forwarding the already published honest target ciphertext opens with the retained key and consumes only that entry. |
| Replay and refill | Replaying the consumed honest frame is rejected, and the freed slot permits the formerly capacity-rejected future target to be admitted; its failed authentication retains the refilled state. |

The private-state queries require all four named application values—consumed past, skipped, failed target, and live future—to remain secret. They also preserve the receive-to-send origin correspondence for every successful open in that scenario. The accompanying reachability queries prevent the failed transition, retry, cache-fill rejection, honest delivery, replay rejection, and post-release admission path from succeeding only vacuously; two further witnesses require an attacker-owned registration commit and attacker recovery of its routed canary.

The repository threat model permits the attacker to register and fully control separate malicious beacons, but excludes access to a legitimate beacon's execution state. The private failed-receive top level runs those malicious registration processes concurrently: their canary is attacker-readable while all four failed-receive canaries remain secret. This is direct symbolic composition of the capabilities, but not an end-to-end handshake/record trace—the failed-receive session begins from its own fresh symbolic root. Interpreting the disjoint symbolic states as distinct production peers still depends on the reviewed peer-selection and independent-root adapter refinements. Registering a malicious beacon does not trigger the separate failed-receive compromise process.

The separate [`failed-receive-compromise.pv`](../crates/protocol-core/proofs/pro-verif/failed-receive-compromise.pv) scenario synchronizes compromise after the forged future failure and before the target is consumed. The already consumed past value remains secret. The skipped and target values are deliberate negative secrecy results because their exact message material is retained in the cache; the live-future value is another deliberate negative result because its material is derivable from the revealed forward chain. In particular, the attacker has the legitimate target ciphertext on the public network and, after receiving the retained target material, can both recover its plaintext and manufacture a different frame that passes the ideal open rule. The honest receive-to-send correspondence is therefore deliberately false after compromise.

Compromise does not make later honest delivery impossible. A separate reachability witness schedules the attacker to forward the original honest target ciphertext after compromise, and the receiver can still accept it using the retained key. This is possibility, not liveness: the active attacker may block delivery or use the compromised target key first, in which case its forged frame consumes the slot and the honest ciphertext will later be rejected.

This ProVerif result is one exact, unrolled capacity-50 execution under ideal cryptography. It is not a quantification over every gap, cache arrangement, retry count, or interleaving. The general control-state statements come from the extracted F* ratchet lemmas, which quantify over states satisfying their invariant and relate planning, advancement, failed completion, successful consumption, capacity, and replay. Conversely, F* models logical capabilities rather than secret bytes and cannot establish the secrecy, compromise, or forgery conclusions of the symbolic trace.

The ProVerif attacker starts at the post-parser admission boundary. A symbolic `crypto_frame` represents a frame whose constructor, sender, sequence, and protected component are available to the network attacker; it does not represent Cap'n Proto byte parsing or an arbitrary byte length. Therefore the model does not prove that frames which are empty, truncated, unparsable, from an unknown or wrong sender, or carry no more than the production overhead are rejected before ratcheting. Production ordering at [`decrypt_message_with_ratchet`](../src/shared.rs#L924-L979) and the boundary/truncation regressions in [`tests/protocol.rs`](../tests/protocol.rs#L421-L550) support those separate adapter claims.

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
[beacon process](../crates/protocol-core/proofs/pro-verif/environment.pvl#L516-L531),
and the [compromise process](../crates/protocol-core/proofs/pro-verif/environment.pvl#L1065-L1085)
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

In the original late-compromise suite, the events named
`MessageKeyUnavailable`, `MessageKeyCached`, and `StateCompromised` document
the process but are not premises of its secrecy queries. (The separate
failed-receive suite does query its target `MessageKeyCached` event.) The
secrecy conclusions follow from which symbolic values each process retains or
reveals, not from a universal theorem of the form “every unavailable key is
forward-secret,” and not from proof of physical memory erasure.

## What is not proven

The modified CTX justification has three deliberately separated layers.
F* machine-checks `ctx_distinct_openings_imply_hash_collision`, which constructs a pointwise collision witness from two distinct accepted explanations of one fixed production-format `C || T || U` payload for arbitrary pure hash and AEAD-open functions.
The conventional computational lifting runs an adversary and returns that witness, giving the displayed advantage inequality under BLAKE2b-512 collision resistance, but the probability and runtime theorem itself is not mechanized.
ProVerif supplies a supplementary explicit ideal-hash negative control in which the base AEAD deliberately multi-opens and removing CTX reverses the query result.
None of these layers proves BLAKE2b, the libsodium call, production field provenance, hax/compiler correctness, or compiled machine code.

### Intended claims that require narrower wording

The main [formal-verification plan](formal-verification.md#proof-inventory) mixes
an intended inventory with completed work. Comparing it to the current proof
sources gives these important qualifications:

| Broadly worded inventory claim | What the current corpus actually supports |
| --- | --- |
| “The commitment input is exactly `(key, nonce, associated data, AEAD tag, sequence, sender ID)`.” | Production delegates its hash input to the extracted fixed-size builder, and F* proves its exact six ranges plus both little-endian encodings ([Rust helper](../crates/protocol-core/src/commitment.rs), [lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Commitment.Lemmas.fst)). The caller's field provenance, BLAKE2b call, hax/compiler correctness, and machine code remain outside the theorem. |
| “The modified CTX construction provides strong commitment.” | F* proves the pointwise collision witness for arbitrary pure hash and AEAD-open functions, including unequal-key and unequal-context base-AEAD openings; the conventional computational lifting bounds misattribution advantage by BLAKE2b-512 collision advantage. ProVerif separately confirms the intended ideal-hash CTX/no-CTX differential. The probability/runtime lifting is not mechanized, and BLAKE2b, libsodium, adapter provenance, compiler correspondence, and confidentiality/authenticity preservation remain assumptions or separate obligations. |
| “Peer, counter, and ratchet publication commit atomically.” | F* proves the pure candidate's returned state and peer shape. Actual atomic mutation of the counter, peer map, ratchet, and persistent storage is an adapter obligation covered by implementation structure and regression tests, not the pure theorem. |
| “Send keys are one use” and “replay is rejected.” | F* proves sequential logical-capability consumption. Global one-use and concrete replay rejection additionally require one authoritative state, no copying or rollback, and exact logical-to-concrete key refinement. |
| “Counters start at one.” | F* proves that advancing any non-exhausted counter returns old plus one; a counter initialized to zero therefore first returns one. Selecting and preserving that initial production state is an adapter/initialization fact. |
| “Every accepted, bounded input is panic-free.” | Strict F* checking covers safety obligations generated for the selected pure core functions. It is not whole-application panic freedom. |
| “Initial and subsequent messages are secret; replay, unknown-key-share, cross-peer, and concurrent-session attacks are prevented.” | ProVerif proves five named messages and exact correspondences in replicated instances of one fixed five-record schedule. The event arguments support those separation interpretations within that schedule, not an arbitrary unbounded record API theorem. |
| “Forward secrecy after later compromise.” | Two named past messages remain secret after one exact beacon-ratchet snapshot. Cached sequence 2 and future traffic are exposed. Persistence and other compromise times/targets are outside that result. |
| “Authentication failure is state-neutral.” | This is false for a syntactically admitted future frame. F* proves that failed completion retains the already advanced state, and the dedicated ProVerif trace exercises advancement, exact cache fill, retry, later success, replay rejection, and one-slot refill. Only pre-admission rejection and a repeated failure relative to the retained state are neutral. |

### Cryptography and implementation components outside the proof

The corpus does not prove:

- computational security, concrete attack probabilities, or reductions for
  Ed25519, X25519, ML-KEM-768, HKDF-SHA-512, ChaCha20-Poly1305, or BLAKE2b;
- correctness, constant-time behavior, side-channel resistance, fault
  resistance, or memory safety of the concrete primitive implementations;
- constant-time or information-flow behavior of the selected pure core or its
  adapters; even the redundant all-zero-DH array comparison has no formal
  timing guarantee ([documented limitation](formal-verification-stage-4.md#L123-L127));
- a complete behavioral specification for every extracted function and error
  path; extraction checks generated safety conditions, but the beacon abort
  helpers and arbitrary malformed/finishing errors have no handwritten semantic
  theorem;
- BLAKE2b-512 collision resistance, a concrete numerical bound for that primitive, or a mechanized probability/runtime theorem for the modified CTX construction; F* machine-checks the pointwise collision witness and transcript injectivity, while the conventional [computational lifting](ctx-commitment.md), opaque hash implementation, production field provenance, and compiled caller retain their stated assumptions;
- nonce uniqueness or the equality, uniqueness, secrecy, and deletion of actual
  message-key bytes;
- entropy quality, fresh-key generation, operating-system RNG behavior, or
  physical erasure/zeroization;
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

- correct, atomic, crash-safe, confidential, or anti-rollback persistence;
- global registration replay protection across server replicas, independent
  restored forks, concurrent database owners, or rollback to an old snapshot;
- truth of the adapter-supplied `Fresh`/`Consumed` and `Available`/`Occupied`
  classifications;
- atomic check-and-insert or check-and-reserve behavior in real sets and maps;
- correctness and uniqueness of general production peer-map selection, or the whole-map update from F*'s theorem about one selected map entry; registration finish now checks that the selected concrete entry equals the binding retained by verified state, but the concrete map operation remains outside F*;
- concrete HKDF call labels and buffer slicing, AEAD result provenance, association of each returned logical slot with the correct concrete key and nonce bytes, exact execution of the returned concrete swap/take, or atomic publication of the logical and concrete results;
- byte-level equivalence between ProVerif's admitted symbolic frame and production Cap'n Proto parsing, sender lookup/checks, overhead-length validation, commitment slicing, or malformed-input rejection;
- behavior through direct low-level ratchet, key, peer-map, compatibility, or
  mutation helpers outside the documented high-level API trace;
- security after cloning a pending capability, forking provider state, or
  rolling counters and replay history backward; or
- physical deletion of old keys. Exported server persistence contains live
  ratchet state and cached keys and is explicitly documented as breaking
  server-side forward secrecy ([persistence overview](persistence.md#overview)).

The persistent consumed-registration history is also unbounded. A party able
to submit many cryptographically valid registrations can grow memory and stored
state. The local 50-key receive bound is not a general denial-of-service proof.

### Protocol traces and attacker cases outside the model

There is no proof here for:

- an arbitrary number of records or arbitrary out-of-order schedules within one
  session;
- arbitrary retry counts, counter wrap/exhaustion in ProVerif, or all possible receive gaps and cache arrangements; ProVerif covers one exact capacity-50 failed-receive schedule, while the general finite control mechanics are handled by F*;
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
- HKDF is deterministic and supplies the needed PRF and one-way properties.
  Production uses `PQXDH_INFO` for root derivation and `SYM_RATCHET_INFO` for
  both initial-chain derivation and per-step ratcheting; its two directions are
  separated by taking different halves of the initial 64-byte output, which the
  adapter must preserve;
- AEAD hides plaintext and reports success only for an authentic ciphertext
  under the same key, nonce, associated data, and plaintext; distinct messages
  use secret, nonreused key/nonce pairs and do not leak through another path;
  and
- BLAKE2b supplies the collision/commitment property assumed for the fixed CTX
  construction.

ProVerif represents these with stronger perfect symbolic constructors and
equations in
[`crypto.pvl`](../crates/protocol-core/proofs/pro-verif/crypto.pvl). Signatures
are unforgeable, matching DH and KEM always agree, constructors do not collide,
secrets cannot be recovered by inversion, and a frame opens only with exactly
matching material, associated data, sequence, and sender ID. The model uses
separate ideal constructors for the root, both directional chains, ratchet
advance, material, key, and nonce. That is finer domain separation than the two
concrete HKDF labels above.
Real algorithms approximate these properties probabilistically, and the proof supplies no general computational reduction from the real algorithms to this ideal model.
The modified CTX claim instead uses its narrower direct lifting from the F*-proved collision witness and does not derive computational security from the ProVerif result.

### Adapter and execution assumptions

The production connection assumes:

- Cap'n Proto registration fields translate exactly to the core's typed and
  role-tagged values, and signature verification authenticates those exact
  bytes before `validate_init_kex` is trusted;
- beacon construction supplies the authentic compiled-in server public key and numeric identity-key ID as the exact `ServerBinding` stored by `BeaconFresh`, and the parsed Phase-2 identity bytes supplied to finish are the response's actual `identityKey` field;
- the authenticated sender ID and eight assigned-ID bytes passed to the post-open core transition are exactly the `CryptoFrame.keyId` and plaintext prefix returned by a successful initial AEAD open;
- the adapter passes the exact F*-verified root input and labels to HKDF, uses
  the exact returned associated data, and applies the complementary ratchet
  offsets correctly;
- each admitted logical ratchet step causes exactly one concrete KDF step, its output is stored in the append slot returned by `advance_receive`, every existing sequence is accessed through the current slot returned by `lookup_receive_key`, and every active logical slot contains exactly its corresponding concrete key and nonce while every inactive slot is empty;
- after one send key is allocated, the adapter finishes the logical capability
  and removes the concrete key after that one encryption attempt even if AEAD
  or serialization fails;
- authentication success/failure is truthfully passed to `finish_receive_with_removal`, retained or missing outcomes cause no concrete slot mutation, and a consumed outcome applies exactly the returned target/old-last swap/take before publishing the returned logical state;
- authenticated sender/target lookup selects one unique peer-map entry and
  preserves all non-selected peers;
- `Fresh` means the exact semantic ID is absent, successful acceptance inserts
  it monotonically, and `Available` means the exact next peer ID is absent;
- the counter, peer, and staged ratchet are published together only after
  response encryption and serialization succeed, while replay consumption
  intentionally occurs earlier and remains consumed on later failure;
- a fresh beacon emits only one registration bundle, supplies fresh coins, and
  does not reuse the bundle after advancing or aborting;
- production follows the documented high-level registration, encryption, and
  decryption paths from fresh or successfully validated state;
- pending capabilities and authoritative state are not cloned into independently
  usable forks;
- restoration validates bounds and uniqueness, sorts imported receive sequence/material pairs, rejects malformed or oversized state, places each material value in the slot returned by `restore_receive_key_with_slot`, and serialization rejects both missing active material and populated inactive slots; and
- server state and replay history have one owner and are not rolled back.

Compile-time size assertions, private Rust fields, consuming APIs, and
regression tests support these assumptions. They are not substitutes for a
machine-checked refinement proof of the adapter.

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
- the failed-receive process is one exact unrolled 50-slot schedule, and its symbolic forged frames represent inputs that have already passed the production parser, sender, and minimum-length gates;
- an admitted failed open retains the derived concrete material represented by every logical skipped/target cache entry, while consuming a successful target removes that material and creates exactly one free slot;
- the only honest-party state compromise is the synchronized beacon snapshot or failed-receive snapshot described above; each scenario has one synchronized snapshot, and every baseline or failed-receive top level that instantiates attacker-owned registration exposes those beacon secrets from the start; and
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
([inventory](../crates/protocol-core/proofs/trusted-boundary.md#proof-library-and-tool-assumptions)).
The handwritten AWK result classifier is likewise trusted to recognize every
required ProVerif query and classify its output correctly. The repository
prevents local proof shortcuts by rejecting `assume` and `admit` in
repository-owned F* files
and rejecting checker flags that would permit missing proofs
([policy gate](../crates/protocol-core/Makefile#L135-L147)). This does not remove
assumptions or trusted interfaces from external hax/F* libraries.

Stage 9 now records the opaque functions, primitive laws, adapter refinements,
proof-library interfaces, generated exceptions, and handwritten model fragments
in the canonical
[trust-boundary inventory](../crates/protocol-core/proofs/trusted-boundary.md).
Its manifest and structural checks make unacknowledged boundary drift fail the
verification gate. Updating the recorded hashes can make an intentional change
pass, so this is a review-control improvement, not a proof of the inventoried
assumptions or of the adequacy of a human review
([Stage 9 scope](formal-verification-stage-9.md#result-and-scope)).

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

1. Primitive correctness must give the beacon and server the same ordered DH1
   through DH4 values and the same ML-KEM shared secret.
2. F* then proves both roles build the same exact 192-byte root input.
3. The adapter must call deterministic HKDF with that input and the same
   `PQXDH_INFO` label, so equal concrete root material follows.
4. F* proves the associated-data identities and ratchet half offsets match.
5. ProVerif's beacon-commit-to-server-commit correspondence adds active-network
   agreement on both identities, root input, symbolic root, associated data,
   assigned ID, and session.

The defensible statement is therefore: **under primitive correctness, faithful
adapter use, uncompromised identities, and the symbolic model assumptions, a
committing honest beacon agrees with a unique earlier server commit on the
modeled session data.** F* alone does not authenticate that network run.

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
4. Conventionally lifting that pointwise witness bounds real misattribution advantage by BLAKE2b-512 collision advantage, but the probability/runtime lifting and collision-resistance assumption are not mechanized.
5. The ordinary model's injective receive-to-send correspondence proves that every accepted record in the fixed schedule has a unique send with the same session, direction, sequence, peers, and plaintext.
6. Separately, F* proves successful logical receive consumes exactly the target key and that retrying that target is rejected.
7. The adapter must map logical sequences one-to-one to concrete keys and preserve one authoritative, non-rollback state.
8. Production frame parsing, sealing, opening, commitment hashing, and sender lookup must match the models.
   The extracted builder and F* lemmas establish the exact key, nonce, associated data, AEAD tag, little-endian sequence, and little-endian sender-ID layout; the adapter must still supply those values from the intended authenticated context and hash the returned bytes.

This supports concrete record integrity, peer/session binding, replay rejection, and conditional CTX misattribution resistance on the high-level path only under those primitive, frame, and adapter assumptions.
The production commitment transcript helper and pointwise collision implication are F*-proved, while the probability/runtime lifting, caller, BLAKE2b, parsing, and field provenance remain computational, adapter, or primitive obligations.
ProVerif supplies the active-attacker origin argument for its bounded schedule and the supplementary CTX/no-CTX control, F* supplies the pointwise collision witness and general local consumption step, and the adapter refinements connect those facts to concrete frames and keys.

The sequence and key ID are authenticated/bound metadata, not secret metadata:
they remain visible on the wire.

### 6. Deleted-key forward secrecy and lack of recovery

1. F* proves when a logical receive capability is consumed; the adapter must
   remove the corresponding concrete material and avoid rollback or retained
   copies.
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

### 7. A failed admitted future frame mutates the selected receiver state

1. Production parsing and sender selection must first choose the legitimate peer and reject malformed, short, or wrong-sender frames before ratchet admission.
2. For the logical receiver state selected by the adapter, F* proves the admitted plan/one-step advancement relationship, that failed authentication retains the complete post-admission state, and that filling capacity blocks another future plan without mutation. F* does not prove the production peer-map selection itself.
3. F* proves the append, current lookup, successful target/old-last removal, and restoration slots for the logical cache. The remaining adapter invariant must place the corresponding concrete key and nonce bytes in those returned slots, apply the returned swap/take exactly, and retain every byte on failure.
4. The private ProVerif scenario then shows that an active network attacker without the legitimate receiver snapshot cannot derive the four named plaintexts even while concurrent attacker-owned registration processes commit a response and expose their own routed canary. The record trace uses a standalone fresh root, so peer/root separation remains an adapter obligation.
5. In the compromise variant, explicitly revealing the legitimate receiver's retained state exposes the skipped and target keys and the live future chain; this both decrypts the public honest target ciphertext and enables a forged accepted frame.
6. If the attacker forwards the honest ciphertext before spending the target key on a forgery, the retained key still accepts it, consumes only that slot, rejects replay, and permits one later derivation.

The defensible statement is therefore: **in the combined private symbolic run, an attacker-controlled registered beacon has no path into the independently rooted failed-receive state, and a failed forged future frame does not by itself expose that state; under the production peer-selection and independent-root refinements, direct compromise of the legitimate retained state does expose every material still represented there and removes the honest-origin guarantee for those keys.** The exact cache-fill and delivery ordering is a finite ProVerif witness, while the state-transition relationships are general F* results under the adapter invariant. Neither proof supplies production peer-map isolation, parser correctness, an end-to-end registration-to-record state linkage, memory erasure, availability, or post-compromise recovery by itself.

## Verification and reproducibility

The current proof entry point is:

```sh
make -C crates/protocol-core verify
```

It enters the locked Nix environment, checks exact tool identities, regenerates both proof backends, enforces the local no-`assume`/no-`admit` policy, strictly checks generated and handwritten F*, and runs all ProVerif scenarios. After intentional boundary diffs have been reviewed and their hashes refreshed, the separate `make -C crates/protocol-core check-inventory` command checks the trust-boundary inventory. The reviewed tool bundle is recorded in the [Stage 8 document](formal-verification-stage-8.md#locked-proof-bundle).

The historical Stage 3 through Stage 9 documents describe how this boundary was built. Older statements such as “semantic proofs remain future work,” older tool versions, hashes, and test counts describe their stage at that time. The current proof claims are the Stage 6 F* results plus the composed failed-receive lemmas, the current ProVerif model (which extends the Stage 7 baseline with attacker-owned registrations and explicit failed-receive scenarios), and Stage 8 reproducibility controls. Stage 9 adds a mechanically checked [trust-boundary inventory](../crates/protocol-core/proofs/trusted-boundary.md); its historical snapshot changed no theorem, symbolic rule, security question, or production behavior, while the maintained inventory now records the later proof extensions. Stage 8 likewise explicitly changed no theorem, model, or expected query result ([Stage 8 scope](formal-verification-stage-8.md#result-and-scope)).

The result gate requires exactly:

- the shared weak-AEAD multi-opening query to be true (unreachable) with CTX and false (witnessed) without CTX;
- all 11 baseline queries to be true: five secrecy and six correspondence results;
- all seven negated reachability/non-vacuity queries to be false, including a committed attacker-owned registration and attacker recovery of its routed canary;
- exactly two true and three false original late-compromise secrecy results;
- all 13 private failed-receive queries to be true (four secrecy and nine state/origin correspondences), with all eleven failed-receive reachability negations false (nine receive-state phases plus malicious-registration commit and malicious-canary recovery); and
- in the seven-query failed-receive compromise run, consumed-past secrecy and both compromise-order correspondences to be true, skipped/target/future secrecy and honest-origin correspondence to be false, and both compromise and later-honest-delivery reachability negations to be false.

During final receive-slot conformance verification on 11 August 2026, `cargo test --locked -p beaconcrypt-protocol-core`, `cargo test --locked`, `make -C crates/protocol-core verify`, `make -C crates/protocol-core check-inventory`, and `make -C crates/protocol-core check-generated` completed successfully against the repository state represented by this report. All three generated F* modules and the ProVerif extraction matched their tracked reviewed outputs, all F* verification conditions were discharged, every ProVerif classification matched the reviewed result set above, and the refreshed trust-boundary inventory matched the reviewed adapter, core, and proof inputs.

The checker rejects missing or substituted queries, timeouts, unknown or
inconclusive results, and any changed classification
([checker](../crates/protocol-core/proofs/pro-verif/check-results.awk)).

For CI and reviewed generated artifacts, use:

```sh
make -C crates/protocol-core check-generated
```

That runs the same suite and rejects tracked or untracked extraction drift. The dedicated formal-verification workflow runs this command. Run `make -C crates/protocol-core check-inventory` separately to check monitored trust-boundary membership and fingerprints. Together, those commands make the proof reproducible and prevent a query, monitored trust-boundary file, or generated file from silently disappearing or changing without an explicit baseline update. They do not prove that the handwritten model is faithful to production or that the reviewed assumptions hold; those conclusions still require substantive review beyond the mechanical Stage 9 gate.

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
> For the receive cache specifically, F* characterizes sequence lookup, exact successful swap-removal, compatibility wrappers, and restoration append slots; production still has to derive the correct secret material, store and move it in those returned slots, serialize it faithfully, and publish state without rollback or inconsistent partial updates.
>
> A dedicated exact capacity-50 trace models a forged future frame advancing and retaining receiver state before authentication, a neutral retry and full-cache rejection, later honest consumption, replay rejection, and admission after one slot is freed. The retained state preserves the named secrets while private; its explicit compromise exposes skipped, target, and future material, permits forgery, and leaves honest delivery reachable but not guaranteed. General control-state relationships come from F*, while byte-level parsing and arbitrary schedules are outside this finite ProVerif trace.
>
> F* proves the exact fixed-width production transcript, its injectivity, and the pointwise theorem that two distinct accepted explanations of one fixed payload produce an explicit collision witness for arbitrary pure hash and AEAD-open functions.
> The conventional computational lifting bounds misattribution advantage by BLAKE2b-512 collision advantage, but its probability and runtime theorem is not mechanized.
> A supplementary differential ProVerif control gives the base AEAD two distinct valid openings: CTX makes the double-open event unreachable, and removing CTX makes the same query produce a witness.
> The resulting real-world strong-commitment claim remains conditional on BLAKE2b collision resistance, correct libsodium behavior, production field provenance, and adapter/compiler correspondence.

Statements such as “the whole implementation is proven secure,” “all application messages are proven confidential,” “the cryptographic primitives are verified,” “replay is impossible across replicas or rollback,” “the complete CTX implementation and BLAKE2b security are formally proved end to end,” or “beaconcrypt is post-quantum secure against active attackers” are not supported by the current proof corpus.
