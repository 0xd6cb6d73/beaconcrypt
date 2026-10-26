# Complete R1 session and record authentication

`PqxdhServerAuthCommonAuthentication.common_authentication_with_resources` bounds the probability that the target Beacon accepts its initial response without a corresponding earlier Server publication carrying both the complete retained eleven-field session and the accepted decoded record. The experiment executes the original R1 source operations in production generation order. It assumes no honest selected candidate, partner, matching seal, successful Server publication or unchanged signed tuple. Those event conditions are discharged by proved source implications and the constructed cryptographic reductions.

This closes the numerical join between the R1 server-authentication components and their actual source common event. It is one designated target registration with adaptive Server attempts. The replicated global protocol experiment, arbitrary reused honest signing identities, later-record security and full symbolic transfer remain separate obligations.

## Exact accepted failure

`CommonEvent.Failure` requires an actual nonempty acceptance annotation and absence of `Authenticated`. This annotation is a private trace of the running experiment, not saved state or a persistence interface. `Authenticated` requires one source coordinate whose `RootCommon.Common` event and `RecordPublished` event both hold. The common event retains the actual successful Phase1 generation, matching preacceptance seal, earlier successful public response, consumed pending token, original root callbacks, both native initializations and publications, and equality of the eleven retained fields. The record event additionally retains the accepted public raw response's decoded sequence, sender and encrypted payload in an earlier successfully published response at that same coordinate.

The eleven fields are Server identity, Beacon identity, unsigned Phase1 `InitKex`, registration ID, prekey, one-time key, ML-KEM public key, actual initializer root, associated data, pinned Server identifier and the designated R1 generation occurrence. Outer assigned-ID equality, response ephemeral encoding, raw KEM ciphertext and pre-Extract input equality are not added to that projection. No equality of installed keys is used to reconstruct roots or identify source occurrences.

The earlier component event retains both `SealedAt` and decoded-record publication. Its actual same-index seal lies in the frozen preacceptance log and therefore in the final source log. The proved source invariant places that seal below the actual allocation count, and the adversary's accept-attempt cap places that count below `Q`. The original owner theorem then identifies a real partner at the same coordinate. Associated data comes from the actual seal receipt, not from equality of decoded frames. The published `RootCommon.game_common` supplies the complete source event when the all-attempt signed-field substitution event is false.

If the complete accepted failure occurs, either the stronger same-owner seal/record event fails or the existing all-attempt substitution event holds. This inclusion is proved on the same sampled annotated execution. The exact joint public/full-state projection recovers the existing record experiment, and the exact signed-field projection recovers the existing joint-EUF source experiment. The constructor-order law quantifies over the whole evaluated continuation, including private state, both caches, all logs, optional writers and public replies. There is one probability union and no additional authentication or disclosure charge.

## Six checked statements

| Statement | Plain-English content |
| --- | --- |
| `CommonEvent.owner_matching` | Actual reachability, ownership and the combined seal/record event supply the partner and earlier publication required by the source common event. |
| `CommonEvent.failure_cases` | Accepted failure of the complete common event is included in the existing same-owner record failure or signed-field substitution event, on the same run. |
| `CommonProbability.failure_split` | The probability of that supported union is at most the sum of its two probabilities in the identical sampled experiment. |
| `CommonProbability.ordered_split` | Both probabilities are exactly the already studied source events, retaining production generation order and complete continuations. |
| `CommonAuthentication.common_authentication` | The two source probabilities are replaced by their concrete constructed primitive reductions and statistical terms. |
| `CommonAuthentication.common_authentication_with_resources` | That exact inequality is conjoined with the complete bills for the same signature, Gap-DH, schedule and record reductions. |

## Losses and constructed reductions

Write `U = entryReductionBudget caps qCoin Q qHash qH` and `H = U + 76`. The bound is

```text
Pr[accepted without complete source session and earlier decoded-record publication]
  ≤ AdvGapDH(scanClient extractor)
    + choose(Q, 2) * 64 / 2^256
    + sum over j : Fin(Q + 1) of [recordLoss(j, H) + scheduleLoss(j)]
    + AdvJointEUF(all-attempt signed-field extractor).
```

Every advantage is that of an explicitly constructed reduction of the same source adversary. The signature term uses `JointIdentityEuf.reduction`, the existing ordinary joint Ed25519/converted-X25519 weak-EUF endpoint, with coefficient one. It charges accepted same-identity changed signed fields once; its all-attempt scan may also charge rejected candidates with valid changed fields. It introduces no guessed signed field, accept attempt or candidate-key factor. Stand-alone EUF-CMA does not replace the joint-use contract.

For each owner, `recordLoss` expands to three separately constructed modified nonce-AEAD IND$ advantages, twice the constructed modified nonce-AEAD INT-CTXT advantage, `(2H + 1) / 2^128`, and `1 / 2^512`. The IND$ clients cover ordinary validation, unpublished-prefix validation and the private prefix view. `scheduleLoss` contains the five reductions constructed with the exact `SessionRecord.observers codec Q` family: root HMAC expansion, initial Extract, initial HMAC expansion, step Extract and step HMAC expansion. The sum has `Q + 1` coordinates, including the original Beacon-owner coordinate; it is not silently reduced to `Q`. There is no additional selection factor at the final join.

The full expressions, samplers and winning events remain in the linked endpoint definitions. In particular, the record bound is not inferred from deterministic seal provenance: writer refusal and guessing a withheld valid record retain their actual privacy and verification charges. See [the record loss and resource guide](server-authentication-record-publication.md), [the stronger seal/record observation](server-authentication-session-record.md) and [the source common event](server-authentication-root-common-event.md).

## Query accounting

The final `ReductionBills` includes the existing complete publication ledger for this exact observer family and the concrete joint-EUF ledger. Source caps quantify over every possible original reply and every attempted API call. They are resource premises, not security conclusions. `qTotal` counts all source calls; `qFinish` counts every attempted finish, including rejection. `Q` bounds accept attempts, `qCoin` public coin requests, `qH` restricted root-input HMAC observations and `qHash` hash requests.

For the signature reduction, define `G = gU + B*gB`, `E = eU + B*eB`, and `D = dU + B*dB`, where each primitive cap accounts for both its direct uniform requests and all interpreted base work. The checked bounds are:

| Resource | Bound |
| --- | --- |
| Signing requests | `3`, in the original source order even when Phase1 publication refuses |
| Converted static-DH requests | `qFinish` |
| Local uniform requests | `96 + G + qTotal*(128 + E + D)` |
| Whole joint-EUF game uniform requests | `128 + G + qTotal*(128 + E + D)`, including the challenger's 32-byte identity sampler |

The original finish collection separately has at most one logical KEM decapsulation per attempted callback; the full numerical simulation bills its actual direct/base work in `D`. The reduction receives no separate target identity seed argument; original public replies and equal-byte aliases remain possible. The local deterministic detached-signature scan inspects at most three fields per original journal entry; no zero runtime claim is made for that scan or arbitrary byte-string processing.

The publication bill retains `U = 256 + qCoin + 160Q + 64(qHash + qH) + gU + Q*eU + dU + B*(gB + Q*eB + dB)`. Its component has total/uniform/hash cap `H`, selected-seal cap one and selected-raw-attempt cap one. The captured unpublished prefix has the same `H` caps, selected-seal cap one and raw cap zero. The three HMAC distinguishers have caps 1, 1 and 2. The full Gap-DH, Extract sampler, HMAC, ordinary validation/integrity, private validation/view and interpreted-game figures are retained verbatim in `PublicationResources.ReductionBills`, with their explicit formulas in the linked resource guide. No source call, local primitive sampler or base callback is declared free.

## Contracts and scope

The theorem uses the existing approved joint twist-inclusive Gap-DH and X25519 class/spread contracts; ordinary joint Ed25519/X25519 weak-EUF; the full arbitrary-buffer attached-verification adapter; the actual source HKDF correctness and component games; the restricted 192-byte zero-salt Extract programmable ROM; and the shared programmable classical CTX/BLAKE2b ROM. Collision resistance alone is not substituted for either ROM. Public HMAC/Expand evaluations retain their original semantics, and repeated projections of the same expansion are not independent samples. No new primitive or protocol-authentication assumption is introduced.

The abstract message contracts remain `ReadWritable`, `Phase2ReadBack` and `FrameReadBack`. They express successful readback without writer totality, canonical encodings, codec injectivity or a serialization implementation proof. Production primitive implementations and their validation are trusted. Persistence, restoration and physical copies remain outside the proof scope.

The actual R1 interface permits attacker-owned and changed candidates, adaptive accepts/builds, arbitrary raw finishes, public primitive queries, original writer and parser rejection, and installed-kernel reveals. The Server identity seed is not revealed in this endpoint (`revealSeed = false`), and the target Beacon seed is not exported by this API. The observer takes no separate selected secret argument; it still sees the original journal, including permitted reveals and equal byte strings. This is not a theorem for current-chain compromise recovery, KCI, arbitrary additional honest signing bundles under the target identity, or a replicated global scheduler. The source enforces the target Beacon's initial sequence-one admission; the result does not claim the known-false later assigned-ID equality.

Validation consists of six exact standard-axiom guards, focused complete-module checks and forbidden-placeholder/custom-axiom scans. The source closure is the exact already reviewed and published 19-module dependency port. Root imports, inventory reconciliation, the central integration and its complete final matrix remain distinct work; an earlier aggregate receipt is not attributed to this new proof tree.
