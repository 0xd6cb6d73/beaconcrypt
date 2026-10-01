# Retain same-session seal fields in the record-publication bound

`PqxdhServerAuthSessionRecord.session_record_with_resources` bounds an accepted R1 run that lacks either a matching authenticated seal or an earlier response containing the accepted decoded record at its actual source owner. Both conditions are retained in one event, over one complete sampled execution. This is the stronger component needed by the eleven-field session consumer: equality of a decoded frame alone does not establish equality of associated data, registration plaintext or the source's pending token.

## Event and actual source receipt

`SealedAt index ghost` requires a seal at that exact source index before the original acceptance, with `sealed context = snap.accepted`. These fields are the authenticated target key ID, the payload following the eight-byte binding, and the complete associated data. `Published codec index ghost journal` conjoins that fact with the earlier `RecordPublished` predicate: a successful earlier build at the same index returned bytes whose inner frame decodes to the accepted sequence, sender and encrypted payload. The frozen acceptance annotation is a private execution trace; it is unrelated to saved state or restoration.

The observer tests failure of this conjunction. It receives only the root-erased analysis trace and original public journal, with a fixed source coordinate. It takes no separate selected root, PRK, challenge key or pending secret slot argument, and no recovered plaintext is injected into an attacker target. The original public replies, including permitted installed-kernel reveals and any equal byte strings, remain in that journal. Root erasure is proved to preserve the new seal condition. The terminal observation can therefore use the existing five key-schedule simulations on their exact allowed observation interface.

`PublicationOccurrence.journal_receipt` already proves a stronger actual receipt than decoded-frame equality: the accepted key ID, plaintext and associated data match a preacceptance seal by the same input partner, and the original owner/collision reasoning identifies its index. The new proof retains these fields. On the branch where ordinary authentication has not failed, this yields `SealedAt`; failure of the combined event must then be missing decoded-record publication. The existing `RecordPublicationJoin.accepted_clean` supplies its ordinary-authentication or unpublished-matched-attempt alternative on that same complete marked run. There is one union of these events, so no second authentication or disclosure bound is charged.

## Ten checked statements

| Module and statement | Plain-English content |
| --- | --- |
| `SessionRecordEvent.sealed_erase` | Removing all derived root replies leaves the matching authenticated seal condition unchanged. |
| `SessionRecordEvent.published_erase` | The combined seal/record condition also survives root erasure. |
| `SessionRecordEvent.observer_true` | The actual root-erased observer tests exactly failure of that conjunction. |
| `SessionRecordEvent.receipt_sealed` | The original same-owner component receipt provides all the accepted seal fields. |
| `SessionRecordEvent.accepted_clean` | Failure of the stronger event lies in the same ordinary-authentication/unpublished-match union on the actual supported callback run. |
| `SessionRecordProbability.full_winning` | The actual context and residual samplers preserve this inclusion, including refusal and complete final state. |
| `SessionRecordProbability.winning_split` | The union is bounded inside the same sampled key/context/component game. |
| `SessionRecordProbability.uniform_bound` | The new uniform endpoint has the existing concrete record loss, with ordinary authentication charged once. |
| `SessionRecord.session_record_bound` | The original generation-order source experiment is bounded using this stronger observer's own five schedule reductions. |
| `SessionRecord.session_record_with_resources` | The inequality and full `ReductionBills` concern those exact constructed reductions and the same source adversary. |

## Reductions and query counts

Let `U = entryReductionBudget caps qCoin Q qHash qH` and `H = U + 76`. The bound is the original concrete joint Gap-DH extractor advantage, plus `choose(Q, 2) * 64 / 2^256`, plus the sum over `j : Fin(Q + 1)` of `recordLoss(j, H)` and the five schedule losses constructed with `SessionRecord.observers codec Q`. The observer family is new; it is not silently replaced by the older missing-frame or missing-outer-response family.

The record reductions are unchanged executable clients. `recordLoss_expanded` still contains three separately constructed modified nonce-AEAD IND$ advantages, twice the modified nonce-AEAD INT-CTXT advantage, `(2H + 1) / 2^128`, and `1 / 2^512`. The three IND$ advantages respectively cover ordinary validation, unpublished-prefix validation and the private prefix view. The five schedule terms cover root HMAC expansion, initial Extract, initial HMAC expansion, step Extract and step HMAC expansion at their actual correlated interfaces and samplers.

The complete uniform bill remains `U = 256 + qCoin + 160Q + 64(qHash + qH) + gU + Q*eU + dU + B*(gB + Q*eB + dB)`, including every declared direct KEM draw and interpreted base callback. The source component still has total/uniform/hash cap `H`, selected-seal cap one and selected-raw-attempt cap one. Its captured unpublished prefix has the same `H` caps, selected-seal cap one and raw cap zero. The constructed HMAC distinguishers have query caps 1, 1 and 2. The complete Gap-DH, Extract sampler, HMAC, ordinary validation/integrity, private validation/view and interpreted-game figures are the unchanged proved `ReductionBills`, explained explicitly in [the record-publication resource guide](server-authentication-record-publication.md#query-accounting). The final theorem instantiates those bills with this new observer family. Local deterministic scans are not claimed to have zero runtime.

## Scope, contracts and validation

This strengthens one original R1 target registration with arbitrary adaptive accepts, builds, finishes, public primitive queries and the existing installed-kernel reveals. It preserves attacker-owned candidates, raw rejection, writer refusal, the original public replies and private state. The endpoint uses `revealSeed = false` for the Server seed; the target Beacon identity seed is not exported by this R1 API. It does not generalize to additional honestly signed bundles under a reused target identity or the replicated global interface.

There is no new primitive, authentication or event-inclusion assumption. The proof uses the original approved joint twist-inclusive Gap-DH and X25519 class/spread contracts, actual source HKDF correctness and component games, restricted 192-byte zero-salt Extract programmable ROM, and shared programmable classical CTX/BLAKE2b ROM. Collision resistance alone is not claimed to justify that ROM. Public HMAC/Expand evaluation keeps its original semantics. Existing one-way `ReadWritable`, `Phase2ReadBack` and `FrameReadBack` laws supply abstract message readback without requiring total writers, canonical encodings or a serialization implementation proof.

The retained matching seal condition is necessary evidence for the full session consumer, but these ten statements do not yet claim the eleven-field session equality, source Phase1 signed-field provenance or global symbolic transfer. That consumer must join the actual earlier accept, consumed pending token, native initializer root, generation occurrence and successful finish in the same execution, then charge the existing joint-use weak-EUF reduction for changed target-identity signed fields. Outer assigned-ID equality, primitive implementation proofs, persistence and snapshots remain outside the claims.

Validation for this focused package consists of direct Lean 4.34 checks, ten exact guarded axiom statements and forbidden-placeholder/custom-axiom scans. No Rust or ProVerif source changes occur here. Root imports, inventory updates, source/common-event integration and the complete final verification matrix remain integration work.
