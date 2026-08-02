<!-- SPDX-License-Identifier: 0BSD -->

# What beaconcrypt's formal verification proves

## Purpose and bottom line

This document explains the formal-verification results in plain language. It is
an audit of the proof sources currently in the repository, not a list of future
goals. It compares the claims in the formal-verification documentation with the
F* and ProVerif files under
[`crates/protocol-core/proofs`](../crates/protocol-core/proofs).

The short conclusion is:

- F* proves useful, universal facts about selected deterministic Rust functions:
  exact PQXDH byte layouts and state transitions, ratchet bounds, logical key
  consumption, replay behavior, and checked counter handling.
- ProVerif proves secrecy and authentication properties for an active-attacker
  symbolic model of registration and a fixed record-exchange schedule. It also
  demonstrates the expected exposure of cached and future keys after one
  precisely timed beacon-state compromise.
- These results do **not** constitute an end-to-end proof of the complete Rust
  application, its adapters, the cryptographic libraries, persistence, or the
  deployed executable. The strongest production claims are conditional on the
  assumptions and implementation-to-model connections listed below.
- The proof does **not** establish computational or post-quantum security. In
  particular, the protocol still uses classical Ed25519 authentication and is
  not safe against an active quantum attacker, as the project already records
  in its [known gaps](rationale.md#known-gaps).

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
ratchet and PQXDH Rust items in the
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

## Concrete properties proved by F*

### PQXDH registration and key establishment

The PQXDH lemmas are checked against the generated Rust translation in
[`Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst`](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst).

| Area | Exact machine-checked result | Important qualification |
| --- | --- | --- |
| Public-key encodings | The Ed25519, ML-KEM-768, and X25519 type markers and the two X25519 role markers have the documented distinct byte values. Each encoding preserves the key bytes exactly; encoder/decoder pairs round-trip; a prekey encoding is rejected as a one-time key and vice versa ([marker and role lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L74-L178)). | Signature verification occurs outside the core. The theorem proves what bytes are tagged and decoded, not that Ed25519 authenticated them. |
| Honest `InitKex` construction | A value made by `beacon_start` is accepted by `validate_init_kex` and yields exactly the four original public keys and expected pending state ([theorem](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L180-L203)). | This is a constructor/validator round trip, not an attacker-controlled wire theorem and not a proof that only one bundle can ever be emitted. |
| Registration identifier | The identifier is exactly the fixed-width beacon identity followed by the one-time X25519 key ([theorem](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L205-L212)). | This avoids a hash-collision assumption for the encoding. Freshness, one-time use, persistent insertion, and absence of rollback are not established by this theorem. |
| Root-key input | When none of the four 32-byte DH outputs is the all-zero array, the 192 bytes are exactly `0xff` repeated 32 times, followed by DH1, DH2, DH3, DH4, and the ML-KEM shared secret in that order. If any DH output is all zero, construction returns `InvalidDhOutput` ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L214-L320)). | The KEM secret is not required to be nonzero. This proves the input to later key derivation, not the HKDF implementation or its output. |
| Honest-role input agreement | If the adapters supply byte-identical DH1 through DH4 values and byte-identical ML-KEM secrets, the two roles return the same root-input result ([theorem](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L322-L335)). | X25519 and ML-KEM agreement are preconditions. Equal concrete root keys additionally require both adapters to apply the same deterministic HKDF with the intended `PQXDH_INFO` label. |
| Associated data | The 153 bytes are exactly the tagged server identity, tagged beacon identity, `PQXDH_INFO`, and `SYM_RATCHET_INFO`, in that order. Equal role identities give equal associated data ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L337-L460)). | The adapter must actually supply the returned bytes to authenticated encryption (AEAD). The theorem does not prove AEAD security. |
| Ratchet direction | Beacon-send matches server-receive at offset 32, and beacon-receive matches server-send at offset 0, for the two halves of a 64-byte result ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L462-L484)). | The actual HKDF operation, byte buffer, slicing, and storage are outside F*. |
| Assigned key ID | The binding is the exact eight-byte little-endian encoding of the `u64`. Equal bytes authenticate the candidate; every unequal byte string is rejected with `KeyIdMismatch`; commit preserves the candidate IDs ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L486-L555)). | The eight bytes must really be the prefix returned by a successful AEAD open. F* accepts an input array; it does not prove that provenance. |
| Replay status and pending acceptance | `Fresh` is admitted, `Consumed` is rejected, and a fresh successful `server_accept` returns the exact pending values without advancing the live core counter ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L557-L607)). | The persistent set lookup and insertion are outside F*. The adapter supplies the `Fresh` or `Consumed` classification. |
| Allocation and server transaction shape | The next key ID is mathematical increment by one or explicit exhaustion at `u64::MAX`; it cannot wrap. A different server binding and an adapter-reported occupied ID are rejected. An available ID produces the exact proposed state and peer; pure commit returns that proposal and pure abort returns the previous state ([theorems](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L609-L683)). | The adapter supplies truthful availability. F* proves return values, not atomic mutation of the production counter, map, ratchet, or persistent storage. |

In plain language, these results remove ambiguity from the bytes both sides are
supposed to use, reject several dangerous boundary cases instead of wrapping or
silently continuing, and show that the pure state machine returns the intended
pending or committed values. They matter because swapping a key role, changing
an identity, reusing a registration, or assigning a different ID should change
or stop the run. They do not establish that the surrounding code performed the
cryptography, database operation, or state publication correctly.

The broadest PQXDH theorem is
[`conditional_honest_run_correspondence`](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Pqxdh.Lemmas.fst#L685-L763).
It assumes a non-exhausted counter, matching identity bytes, four valid and
pairwise-equal DH results, an equal KEM secret, `Fresh` replay status, and an
`Available` next ID. The production adapter, not this theorem, must have
authenticated those identity bytes. Under those conditions the theorem proves
equal root inputs, equal associated data, the same assigned peer ID and binding
bytes, complementary ratchet directions, successful binding authentication,
and matching committed core peer data.

That theorem describes the result after inputs have already been validated and
both parties follow the protocol. It does not itself verify signatures, wire
provenance, secret agreement, AEAD, set/map lookups, actual network behavior,
or actual publication. It should not be read as an active-attacker handshake
proof; that is the separate ProVerif layer.

### Symmetric-ratchet control state

The F* ratchet deliberately models sequence numbers and **logical key
capabilities**, not the secret chain bytes, concrete message keys, or nonces. A
logical capability is bookkeeping that says “the key for sequence 2 should be
available”; it is not the key itself. For example, after sequence 3 arrives
first, the model may contain capabilities for sequences 2 and 3. Successful
authentication of sequence 3 consumes capability 3 while capability 2 remains
for the delayed record. Production code separately has to derive, retain, and
delete the matching secret bytes.

The ratchet invariant says the active receive cache has at most 50 entries;
every entry is nonzero, no greater than the receive counter, and unique
([invariant](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L9-L32)).

The following properties are proved:

- Empty-cache constructors establish the invariant for arbitrary supplied
  counters ([constructors](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L53-L61)).
- A successful send allocation increments the counter by exactly one, returns a
  capability for that same sequence, does not touch receive state, and cannot
  wrap. Exhaustion at `u64::MAX` changes no state
  ([send lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L63-L103)).
- Sequentially finishing an available send capability marks the returned value
  unavailable; finishing that returned value again fails without changing it
  ([finish lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L105-L126)).
- A successful future receive plan reports a derivation count equal to the
  numeric gap; the plan itself derives nothing. Admission requires both a gap
  of at most 50 and total outstanding capacity of at most 50. Larger gaps and
  capacity overflow are rejected with a count of zero. The adapter is assumed
  to perform exactly the reported number of core and concrete KDF advances
  ([planning lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L128-L178)).
  An old or current target requires zero new derivations, but that result does
  not say its key is still present in the cache.
- Each successful receive advancement increments once, appends the exact new
  sequence, preserves the send counter and invariant, and reports the correct
  cache slot. A full cache or exhausted counter is state-neutral
  ([advancement lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L180-L224)).
- A wrong sequence/slot pair consumes nothing. Given a valid state and matching
  target/slot, authentication failure retains the entire logical state passed
  to `finish_receive` for retry. For a future sequence, planning and admitted
  advancement may already have moved the receive counter and cached bounded
  intermediate keys; failure retains that advanced state and is not neutral
  relative to the start of decryption. Those advances can consume cache/window
  capacity. Authentication success removes exactly the target, retains every
  other cached key, preserves the invariant, and a second use of the old
  target/slot is rejected as missing
  ([completion and replay lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L226-L315)).
- Successful, ordered restoration preserves the invariant, and finishing a
  valid restoration returns a valid state
  ([restore lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L317-L332)).
- Pointwise replacement leaves a peer record with a different ID unchanged.
  Mismatched send advancement returns no sequence and an unavailable
  capability; for the selected peer, the peer ID, ratchet, and sequence match
  direct send advancement
  ([peer lemmas](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Ratchet.Lemmas.fst#L334-L372)).

The last result is pointwise: it does not prove that a production whole-map
lookup selects one unique entry or updates the complete map correctly.

These facts prove the control algorithm, not global ownership. In Rust,
`RatchetState` and `SendKey` are copyable values. The “one-use” theorem threads
the returned unavailable capability into the second call; it does not stop a
caller from retaining a copy of the original available capability or forking
old ratchet state. Concrete one-use and replay resistance therefore require one
authoritative, non-rollback state and the adapter invariant

```text
concrete receive-key sequences == logical receive-cache sequences
```

The proof also accepts the `authenticated` flag as an input. The adapter must
derive it from a sound commitment and AEAD check, perform exactly the planned
KDF steps, associate each logical sequence with exactly one concrete key, and
delete the matching concrete key when the core consumes it.

For the selected functions, strict checking also proves the array-bound and
similar safety conditions that hax generates. This is not a proof that the
entire application, all adapter error paths, allocation, FFI, or machine code is
panic-free. Nor does extraction and typechecking give every selected function a
complete behavioral specification: the beacon abort helpers, arbitrary
malformed `InitKex` inputs, and all registration-finishing error paths do not
have handwritten semantic theorems.

## Concrete properties proved by ProVerif

### The modeled attacker and execution

All protocol traffic crosses an attacker-controlled network. Protected payloads
are still symbolically encrypted, but the attacker may observe ciphertexts and
may block, replay, reorder, modify, and synthesize network data. Honest beacons
and server processes are replicated, so the model considers unbounded
concurrent instances of its modeled session. Each instance nevertheless
executes one fixed record schedule: four server-to-beacon records and one
beacon-to-server record, with server sequence 3 received before sequence 2
([beacon side](../crates/protocol-core/proofs/pro-verif/environment.pvl#L207-L468),
[server side](../crates/protocol-core/proofs/pro-verif/environment.pvl#L573-L739)).

The modeled server path is limited to uncompromised identities created by the
honest beacon process. It looks up the received identity in the private
`honest_origin` table before it continues past registration parsing
([gate](../crates/protocol-core/proofs/pro-verif/environment.pvl#L475-L512)).
For an attacker-created identity the process stops at that lookup, so such an
identity cannot exercise the rest of the modeled server path at all. The model
therefore proves agreement for the honest-identity case; it does not analyze
the server's behavior for malicious or compromised beacon identities.

The named events and private tables in this section are annotations inside the
proof model. They are not production log entries, database tables, or data sent
on the wire.

### Baseline secrecy

The five baseline secrecy queries in
[`queries.pvl`](../crates/protocol-core/proofs/pro-verif/queries.pvl#L3-L8)
all succeed. The symbolic attacker cannot derive these named application
values in the uncompromised model:

| Modeled value | Position in the fixed schedule |
| --- | --- |
| `INITIAL_SECRET` | Initial server-to-beacon registration message. |
| `CACHED_SECRET` | Server sequence 2, whose key is temporarily cached because sequence 3 is received first. |
| `ADVANCE_SECRET` | Server sequence 3, consumed during out-of-order advancement. |
| `FUTURE_SECRET` | Server sequence 4 in the uncompromised baseline. |
| `BEACON_RECORD_SECRET` | First beacon-to-server record. |

This is symbolic confidentiality of five fixed message positions. It is not a
computational indistinguishability result and is not a ProVerif proof for an
arbitrary-length application stream.

### Authentication, agreement, and replay correspondences

Six injective correspondences are proved in the baseline:

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
[`queries.pvl`](../crates/protocol-core/proofs/pro-verif/queries.pvl#L10-L170).
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
can never accept any message. Five separate queries show that the model can
reach server acceptance, registration replay rejection, abort after
consumption, beacon commit, and a message receive
([queries](../crates/protocol-core/proofs/pro-verif/reachability-queries.pvl)).

ProVerif prints each positive reachability request as a negated statement. The
required result is therefore `false`: “the event never occurs” is false because
a trace to the event exists. These are consistency/non-vacuity witnesses, not
failed security proofs. They do not separately establish reachability of every
one of the five secret-bearing record sites.

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
[beacon process](../crates/protocol-core/proofs/pro-verif/environment.pvl#L343-L395),
and the [compromise process](../crates/protocol-core/proofs/pro-verif/environment.pvl#L767-L787)
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

The events named `MessageKeyUnavailable`, `MessageKeyCached`, and
`StateCompromised` document the process, but no query refers to them. The
secrecy conclusions follow from which symbolic values the process retains or
reveals, not from a universal theorem of the form “every unavailable key is
forward-secret,” and not from proof of physical memory erasure.

## What is not proven

### Intended claims that require narrower wording

The main [formal-verification plan](formal-verification.md#proof-inventory) mixes
an intended inventory with completed work. Comparing it to the current proof
sources gives these important qualifications:

| Broadly worded inventory claim | What the current corpus actually supports |
| --- | --- |
| “The commitment input is exactly `(key, nonce, associated data, AEAD tag, sequence, sender ID)`.” | This order appears in the handwritten ideal ProVerif `seal_frame`/`open_frame` model ([source](../crates/protocol-core/proofs/pro-verif/crypto.pvl#L86-L195)). No commitment or record builder is selected for F* extraction, and no F* theorem checks the production `build_commitment` Rust function. Production layout is supported by tests, not by these formal proofs. |
| “Peer, counter, and ratchet publication commit atomically.” | F* proves the pure candidate's returned state and peer shape. Actual atomic mutation of the counter, peer map, ratchet, and persistent storage is an adapter obligation covered by implementation structure and regression tests, not the pure theorem. |
| “Send keys are one use” and “replay is rejected.” | F* proves sequential logical-capability consumption. Global one-use and concrete replay rejection additionally require one authoritative state, no copying or rollback, and exact logical-to-concrete key refinement. |
| “Counters start at one.” | F* proves that advancing any non-exhausted counter returns old plus one; a counter initialized to zero therefore first returns one. Selecting and preserving that initial production state is an adapter/initialization fact. |
| “Every accepted, bounded input is panic-free.” | Strict F* checking covers safety obligations generated for the selected pure core functions. It is not whole-application panic freedom. |
| “Initial and subsequent messages are secret; replay, unknown-key-share, cross-peer, and concurrent-session attacks are prevented.” | ProVerif proves five named messages and exact correspondences in replicated instances of one fixed five-record schedule. The event arguments support those separation interpretations within that schedule, not an arbitrary unbounded record API theorem. |
| “Forward secrecy after later compromise.” | Two named past messages remain secret after one exact beacon-ratchet snapshot. Cached sequence 2 and future traffic are exposed. Persistence and other compromise times/targets are outside that result. |

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
- the modified CTX/BLAKE2b commitment construction's computational strong
  commitment property, collision resistance, or production argument order;
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
- correctness of the production peer-map lookup, uniqueness of map keys, or the
  whole-map update from F*'s theorem about one selected map entry;
- concrete HKDF call labels and buffer slicing, AEAD result provenance, or the
  logical-cache/concrete-key-map equality;
- equality between the numeric ID that the beacon stores for the server and the
  numeric identity-key ID in the server's own accepting binding; production
  expects both to name that server, but the composed F* theorem does not relate
  them;
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
- repeated duplicate receive calls in ProVerif, counter wrap/exhaustion in
  ProVerif, or all possible receive gaps—the finite mechanics are handled only
  in F*'s pure control model;
- compromise at an arbitrary time, repeated compromise, server compromise,
  compromise of long-term identity/prekey/KEM secrets, key-compromise
  impersonation, or recovery after compromise;
- malicious or compromised beacon identities, cross-bundle splicing if one
  identity may create multiple independently signed bundles, or application
  task-routing/broadcast policy;
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
concrete HKDF labels above. Real algorithms approximate these properties
probabilistically; the proof supplies no computational reduction from the real
algorithms to this ideal model.

### Adapter and execution assumptions

The production connection assumes:

- Cap'n Proto registration fields translate exactly to the core's typed and
  role-tagged values, and signature verification authenticates those exact
  bytes before `validate_init_kex` is trusted;
- the configured server identity, received response identity, and live server
  binding are checked to be the same key;
- the eight assigned-ID bytes passed to the core come from a successful initial
  AEAD open;
- the adapter passes the exact F*-verified root input and labels to HKDF, uses
  the exact returned associated data, and applies the complementary ratchet
  offsets correctly;
- each admitted logical ratchet step causes exactly one concrete KDF step and
  each cached logical sequence corresponds to exactly one concrete key;
- after one send key is allocated, the adapter finishes the logical capability
  and removes the concrete key after that one encryption attempt even if AEAD
  or serialization fails;
- authentication success/failure is truthfully passed to `finish_receive`, and
  concrete keys are retained or removed in step with logical capabilities;
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
- restoration validates bounds and uniqueness, sorts imported receive
  sequences, rejects malformed or oversized state, and rebuilds through the
  proved restore steps; and
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
- beacon identity, prekey, one-time, and KEM secret values remain private; the
  model publishes only their corresponding public values and signatures;
- the five named application plaintexts start unknown to the attacker and enter
  the protocol only at their designated modeled message sites;
- one fresh honest beacon identity emits one registration bundle;
- replay state is a private, atomic, single-owner, non-rollback process whose
  first request returns `Fresh` and all later requests return `Consumed`;
- fresh abstract key IDs model a collision-free, non-exhausted prefix of the
  concrete `u64` allocator;
- the fixed sequence constructors model the particular record prefix being
  analyzed;
- the only state compromise is the synchronized beacon snapshot described
  above; and
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

1. The ideal ProVerif `open_frame` succeeds only with exactly matching key
   material, associated data, sequence, and sender ID.
2. Its injective receive-to-send correspondence proves that every accepted
   record in the fixed schedule has a unique send with the same session,
   direction, sequence, peers, and plaintext.
3. Separately, F* proves successful logical receive consumes exactly the target
   key and that retrying that target is rejected.
4. The adapter must map logical sequences one-to-one to concrete keys and
   preserve one authoritative, non-rollback state.
5. Production frame parsing, sealing, opening, commitment construction, and
   sender lookup must match the handwritten frame model. In particular, the
   concrete CTX commitment must receive the key, nonce, associated data, AEAD
   tag, little-endian sequence, and little-endian sender ID in that exact order,
   and the sequence, sender, and associated data must come from the intended
   authenticated context.

This supports concrete record integrity, peer/session binding, and replay
rejection on the high-level path only under those frame and adapter assumptions.
The production commitment layout is tested but not F*-proved. ProVerif supplies
the active-attacker origin argument for its bounded schedule; F* supplies the
general local consumption step; the adapter refinements connect those facts to
concrete frames and keys.

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

## Verification and reproducibility

The current proof entry point is:

```sh
make -C crates/protocol-core verify
```

It enters the locked Nix environment, checks exact tool identities, regenerates
both proof backends, enforces the local no-`assume`/no-`admit` policy, strictly
checks generated and handwritten F*, checks the reviewed trust-boundary
inventory, and runs all ProVerif scenarios. The reviewed tool bundle is recorded
in the [Stage 8 document](formal-verification-stage-8.md#locked-proof-bundle).

The historical Stage 3 through Stage 9 documents describe how this boundary was
built. Older statements such as “semantic proofs remain future work,” older
tool versions, hashes, and test counts describe their stage at that time. The
current proof claims are the Stage 6 F* results, Stage 7 ProVerif results, and
Stage 8 reproducibility controls. Stage 9 adds a mechanically checked
[trust-boundary inventory](../crates/protocol-core/proofs/trusted-boundary.md)
but changes no theorem, symbolic rule, security question, or production
behavior. Stage 8 likewise explicitly changed no theorem, model, or expected
query result ([Stage 8 scope](formal-verification-stage-8.md#result-and-scope)).

The result gate requires exactly:

- all 11 baseline queries to be true: five secrecy and six correspondence
  results;
- all five negated reachability queries to be false, meaning witnesses exist;
  and
- exactly two true and three false late-compromise secrecy results.

During preparation of this report on 2 August 2026, the command completed
successfully with both regenerated extraction artifacts unchanged. All F*
verification conditions were discharged, all three ProVerif classifications
matched the counts above, and the trust-boundary inventory matched its recorded
baseline.

The checker rejects missing or substituted queries, timeouts, unknown or
inconclusive results, and any changed classification
([checker](../crates/protocol-core/proofs/pro-verif/check-results.awk)).

For CI and reviewed generated artifacts, use:

```sh
make -C crates/protocol-core check-generated
```

That runs the same suite and rejects tracked or untracked extraction drift. The
dedicated formal-verification workflow runs this command. These controls make
the proof reproducible and prevent a query, monitored trust-boundary file, or
generated file from silently disappearing or changing without an explicit
baseline update. They do not prove that the handwritten model is faithful to
production or that the reviewed assumptions hold; those conclusions still
require substantive review beyond the mechanical Stage 9 gate.

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
> against an active symbolic network attacker, and precisely documents
> two named deleted-key secrecy results at one snapshot, cached-key exposure,
> and absence of post-compromise security. These guarantees are conditional on
> ideal cryptographic assumptions, faithful adapters and handwritten modeling,
> high-level non-rollback execution, and the stated replay-owner and compromise
> scope; the complete application and primitive implementations are not
> formally verified.

Statements such as “the whole implementation is proven secure,” “all
application messages are proven confidential,” “the cryptographic primitives
are verified,” “replay is impossible across replicas or rollback,” “the CTX
implementation is formally proven,” or “beaconcrypt is post-quantum secure
against active attackers” are not supported by the current proof corpus.
