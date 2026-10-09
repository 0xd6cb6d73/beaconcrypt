# Later fresh-message guessing and left-or-right secrecy

This increment proves both remaining later confidentiality facts of the record layer. The run adversary makes the same adaptive record, test and fresh-message requests as before. At the end of that run, an arbitrary function of the environment state is disclosed and a post adversary continues through the restricted `PostSpec` interface, using the same environment and shared random-oracle state. The target definitions were accepted for the CE-12 consumer in coordination message 260 on 2026-10-09. All four modules are new `PqxdhRecordFacts*` modules; no existing target or proof changes.

`PqxdhRecordFactsLaterTargets.LaterFreshGuessStatement` bounds the probability of a final post-output claim matching an admitted fresh message on a hidden handle by `2^{-bounds.min}`. The claim selects both its message index and guessed bytes after the post phase. `LaterLorStatement` states that a public decision guesses the test bit with probability exactly one half of public eligibility together with hiddenness of every admitted test. Both statements quantify over every environment, E-only disclosure and pair of adversaries, without a `Frame`, query-budget or cryptographic-contract premise. These are facts of the ideal record world; applying the computational record lift incurs its separately stated primitive advantages and query bounds. Neither definition asserts later authentication, origin or binding.

| Module | Checked statements | Result |
| --- | --- | --- |
| `PqxdhRecordFactsLaterTargets` | two definitions | Frozen exact target statements for the CE-12 consumer |
| `PqxdhRecordFactsLaterFlat` | 3 | Complete post-execution flattening and preservation of caller-known kernels |
| `PqxdhRecordFactsLaterLor` | 6 | Full post continuation of the bit-swap coupling, halving and `later_idealRecords_lor` |
| `PqxdhRecordFactsLaterFresh` | 6 | Full post continuation of the byte-shift coupling, adaptive claim weighting and `later_idealRecords_fresh` |

## Complete source-shaped continuation

`LaterFlat.postRun_source` proves that the flattened native post execution is the existing nested environment, protocol and CTX execution on every complete input state. `laterCtxRun_flat` then identifies the whole later world with startup, the flattened run-phase secrecy-ledger execution, and that post execution. These are equalities of computations, not only marginal distributions. They retain the complete environment, control, CTX private state and shared cache, and retain the original run ledger exactly. `postRun_known` proves that caller-known kernels remain caller-known throughout the post phase, including administrative capabilities requested by the environment.

The post interface is the existing E-only interface: it permits coins, shared hashes and the environment's HMAC handler. The existing `PqxdhRecordLiftLaterWorlds.post_schedule` establishes which private services these requests can generate. The new source equality explicitly uses `postEmbed`, `PqxdhRecordLiftLater.post` and `laterCtxRun_split`; it does not replace the post phase with an uncharged or state-free observer. The post phase may install new handles, so the proof does not assume that the final handle map is unchanged.

## Left-or-right proof

`LaterLor.post_escaped` shows that a test sent on a caller-known handle remains excluded by the hidden-test event after the post phase. `post_couple` extends the existing run-phase relation to the complete post phase: on related runs the adversary output and complete native state are equal, so both post phases start from identical output, disclosure and state and execute identically. The run ledgers differ only in the test bit, which the post phase does not read or change. On escaped runs the persistent caller-known handle makes the hidden-test event false on each side.

`world_couple` joins this continuation to the existing adaptive run-phase bit-swap coupling, including startup failure. `lor_zeros` observes that the decision's win and its negation have the same probability, are disjoint and together equal eligible hidden tests. Each therefore has exactly half that probability. `law_zeros` transports every observation that factors through the hiding projection across the already proved later plaintext-replacement equality. It retains the secrecy ground truth used by the event, including the test bit, while the public decision itself receives only `PublicHiding`. `later_idealRecords_lor` applies those facts to prove the frozen `LaterLorStatement` exactly.

## Fresh-message proof

`LaterFresh.post_escaped`, `post_couple` and `world_couple` extend the existing run-phase byte-shift coupling in the same way. For any fixed message index, message length and vector of byte offsets, the hidden fresh message is shifted by those offsets while related native states and post outputs remain equal. If the message was sent on a caller-known handle, that exclusion remains true after the post phase. All other run-ledger entries stay as specified by the existing shift relation.

`hitAt_bound` averages over the `256^length` possible shifts. Distinct shifted hits are disjoint, each implies the same claimed index and length, and messages shorter than `bounds.min` cannot be eligible. The bound for one index and length is thus `256^{-bounds.min}` times the probability of that claim, in the complete later execution. `fresh_zeros` sums these bounds over the countable set of possible index-and-length claims. Those claims are disjoint, so their probabilities add to at most one; there is no extra factor for choosing the target index. The resulting `256^{-bounds.min}` bound is weakened to the frozen target's `2^{-bounds.min}`. `later_idealRecords_fresh` uses the later hiding equality and proves `LaterFreshGuessStatement` exactly.

## Assumptions, costs and scope

No new contract, security endpoint, reveal command or freshness rule is introduced. Each new theorem has no primitive-contract hypothesis; the arguments use the existing native-state correspondence, the existing run-phase swap couplings, and the existing ideal-world later hiding equality. The primitive record and BLAKE2b random-oracle model remain the inherited definitions of the world. No proof of a primitive algorithm or implementation is attempted. Snapshot, persistence and restoration remain outside scope.

These ideal-world facts introduce no constructed primitive reduction or oracle-query bill. They hold for every finite adaptive program and therefore need no finite numerical query cap. Every native post request still executes in the equality and coupling, including its counters and shared-cache effects. When these facts are used for real-world secrecy, the separate later chain and CTX lifts charge all run and post work in `LaterChainBills`, `LaterCtxBills` and their loss terms. This increment adds zero statistical loss to the later LOR fact and only the stated fresh-message guessing term, with no session, record or index selection multiplier.

## Validation and review

All fifteen new theorems have exact axiom guards allowing only `propext`, `Classical.choice` and `Quot.sound`. Direct Lean 4.34 checks pass for all four modules in an isolated owned artifact mirror. All fifteen statements, the frozen targets and the stage documentation have independent semantic and hygiene approval. The receipt in `doc/impl/proof-receipts/record-facts-later.json` records the review and the focused root-import, inventory and transcript-fidelity publication checks. No Rust, ProVerif, primitive implementation, codec implementation or deployment-storage file changes in this increment.
