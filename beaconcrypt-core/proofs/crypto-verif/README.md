<!-- SPDX-License-Identifier: 0BSD -->

# CryptoVerif protocol models

These executable CryptoVerif 2.12 models investigate how much of beaconcrypt's computational protocol argument can be discharged automatically. They deliberately do not prove the underlying primitives and have no dependency on the F*/Lean implementation-correctness layers.

The main result is that CryptoVerif can automatically handle useful active, polynomially replicated protocol games that are substantially broader than the repository's fundamentals-oriented SSProve proof of concept. The checked models cover multi-session registration agreement, registration-task confidentiality, bidirectional established-channel secrecy and injective record origin, replay rejection, and context separation. They still abstract important parts of the production protocol, so their results are conditional model theorems rather than an end-to-end beaconcrypt theorem.

## Developer interpretation

In functional terms, the registration-agreement model says that when a modeled honest beacon finishes registration, its accepted assigned ID, initial task, protected response, and handshake data came from one unique matching modeled honest-server registration. For an exact bundle in the model's private honest set, an honest-server commit also has one unique matching beacon initiation, but that classification is proof bookkeeping rather than application authorization. The network may still block the response after the model consumes the registration identifier, so the server cannot infer that the beacon finished and no retry or recovery property is proved. A separate privacy model says that observing complete registration responses does not reveal which of two equal-length initial tasks was selected, but that model does not let the attacker feed modified responses into a beacon and observe whether they were accepted.

For an already established abstract channel with authenticated fresh directional keys, an accepted record must match one unique send in the same session, direction, peer context, associated data, and sequence. For each session and receiving direction, the same sequence cannot be accepted twice, and moving or modifying a frame cannot make it valid in another bound context without breaking the assumed record transform. The attacker also cannot distinguish the selected equal-length application messages across many active sessions. Message lengths and public metadata remain visible.

These statements are proved about the handwritten models, not about the compiled Rust library. A valid self-signed registration proves no application authorization; enrollment and routing policy remain external. The models also omit the exact PQXDH root, registration-to-channel composition, exact ratchet and nonce derivation, skipped-key cache, persistence, and model-to-code connection. The [developer-facing result table](../../../doc/impl/cryptoverif-evaluation.md#what-the-checked-results-mean-for-developers) states each operational guarantee beside its required qualification.

## Automated protocol models

- `automated-registration-first-record.ocv` models polynomially many honest beacon initializations and server registrations under active Phase-2 scheduling. It preserves three separately signed Phase-1 fields, a pinned server static-DH identity, consumed-registration state, unique assigned IDs, and the encrypted assigned-ID check. CryptoVerif proves injective honest-bundle origin and `BeaconCommitted`-to-`HonestServerCommitted` agreement under signature EUF-CMA, multi-session PRF-ODH, key splitting, and registration-record integrity assumptions.
- `automated-registration-confidentiality.ocv` gives the adversary polynomially many honest Phase-1 publications and registration calls, attacker-chosen equal-length task pairs, and complete Phase-2 responses. CryptoVerif proves one global challenge bit secret under signature EUF-CMA, multi-session PRF-ODH, key splitting, and registration-record IND-CPA assumptions.
- `automated-established-channel.ocv` creates polynomially many attacker-parameterized sessions and permits chosen-message sends, arbitrary delivery, modification, replay, direction swapping, and cross-session routing in both directions. CryptoVerif proves a global left/right challenge bit secret and proves both injective acceptance-to-send correspondences under the assumed privacy and integrity of the composed record transform.
- `assigned-id-binding-negative-control.ocv` differs from the registration-agreement model only by omitting equality between the clear outer assigned ID and the encrypted assigned ID. CryptoVerif still proves honest Phase-1 origin but cannot prove beacon-to-server commit agreement. The concrete modeled mismatch is to forward a valid protected response under a distinct outer ID, causing the weakened beacon event and server event to disagree. The tool's `Could not prove` classification is retained as a regression control, not treated by itself as an attack theorem.

The authentication and confidentiality registration games are intentionally separate. CryptoVerif 2.12 automated the integrity-first correspondence game and the encryption-only privacy game, but it did not automatically compose the library's IND-CPA and INT-CTXT transformations into CCA-style privacy in the combined process with an active `BeaconFinish` decryption oracle. The suite does not silently turn those two proofs into a stronger composed theorem.

Automation is guided by the short `proof` blocks in each model: they select the intended primitive transformations and ordering, while CryptoVerif performs the replicated game rewrites, index and collision accounting, correspondence reasoning, and bound construction. The processes and primitive interfaces remain handwritten and review-critical.

## Focused assumption probes

- `passive-post-quantum-one-record.ocv` proves equal-length confidentiality for one registration record when all four X25519 contributions are public. Its bound contains ML-KEM IND-CCA2, a PRF assumption for the hybrid root combiner keyed by the ML-KEM shared secret, two uses of the shared symmetric-KDF PRF, and nonce-based AEAD privacy.
- `ratchet-forward-secrecy.ocv` proves one-step, erasure-conditioned confidentiality after revealing the successor chain. Its bound contains the ratchet-KDF PRF and nonce-based AEAD privacy advantages.
- `record-authentication-replay.ocv` proves injective acceptance-to-send correspondence for one record under repeated receive attempts. It binds associated data, sequence, and sender in a protected context and inserts the accepted tuple only once.

The post-quantum probes load `pq.ocvl`. The active-classical registration models load `default.ocvl` because their authentication core uses a Diffie-Hellman PRF-ODH assumption. The established-channel abstraction remains in `pq.ocvl` because it starts after authenticated registration and assumes only the symmetric record transform. The policy gate rejects locally declared equivalences, equations, collision statements, and security statements. Typed `[data]` functions idealize injective deterministic encodings; they are explicit protocol-model assumptions rather than primitive proofs.

## Interpretation boundary

The registration models authenticate one static-DH contribution and bind the other public handshake fields into the transcript. The other three production DH contributions, the ML-KEM shared secret, the exact hybrid combiner, and the exact ratchet initialization are not yet composed into that active model. The KEM cannot replace the classical authentication contribution: an attacker can encapsulate to a public KEM key and learn the resulting shared secret.

Registrations outside the private honest-bundle set are abstracted by an adversary-supplied untrusted Phase-2 frame. This exposes arbitrary frame values but removes the real server DH/root/encryption computation and its chosen-key/oracle effects, so the model does not establish that this abstraction preserves every honest-agreement or confidentiality behavior. Beacon finish is terminal and exposes no public success distinction. Assigned IDs are attacker-selected but uniqueness-checked, which abstracts the production allocator. The established-channel model uses fresh directional traffic keys and an ideal composed record interface rather than the exact sequential ratchet, derived nonce, BLAKE2b CTX construction, or 50-entry skipped-key cache.

None of the models covers Rust correspondence, serialization, malformed parsing, persistence, rollback, forked state, physical erasure, side channels, availability, principal corruption, full forward secrecy, post-compromise security, or active post-quantum registration/key establishment and end-to-end authentication. The symmetric established-channel abstraction is separately active-network and PQ-capable conditional on already authenticated fresh directional keys. Concrete security of Ed25519, X25519, ML-KEM, HKDF, ChaCha20-Poly1305, and BLAKE2b remains assumed and out of scope.

## Reproducing the results

Run the isolated suite from the repository root with:

```sh
make -C beaconcrypt-core verify-cryptoverif
```

This target enters the flake's minimal `cryptoverif` shell and does not build or invoke the F*/Lean proof toolchain. Logs are written under `target/formal-verification/crypto-verif/`.

CryptoVerif can exit successfully after reporting some input errors, so `check-results.sh` rejects errors, warnings, unknown or reordered results, changes to the complete reviewed advantage bounds, and missing completion markers. Positive models must prove every listed query; the assigned-ID negative control must reproduce its exact reviewed failure.

See [`../../../doc/impl/cryptoverif-evaluation.md`](../../../doc/impl/cryptoverif-evaluation.md) for the comparison with SSProve, the precise theorem scope, and recommended next steps.
