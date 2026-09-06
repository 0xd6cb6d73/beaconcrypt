# Record-state compromise in the replicated experiment

The HB-93 follow-on adds twenty statements about actual record-state compromise and its query accounting. `RawCtxProtocolReveals` extends the same replicated Server/Beacon record experiment with reads of an owner's current send chain, current receive chain or one requested skipped material. `RawCtxRevealBudgets` charges these reads alongside all previous source operations. The interface is a computational experiment capability used to state adversarial compromise; it does not add a public network API to production or claim that target material remains secret after disclosure.

## Actual selected state and replies

A Server owner handle contains its existing API-instance index and the original peer identifier. `selectedKernel` reads that peer's actual current map entry. A Beacon handle contains its existing API-instance index and reads only its established variant. Missing peer entries and inactive Beacons provide no kernel. Neither selection assumes identity uniqueness, assigned-ID agreement or independent initial states.

`skippedKey` uses the unique result of the already proved total extracted `refined_receive_key` operation. `skipped_exact` identifies that normalization with the actual RustM result. The operation retains logical sequence lookup, bounded slot access and material-tag checks. It has no successful-lookup or valid-state premise. `skipped_reveal_exact` transfers the same result to the selected-owner interface. Both key and nonce are disclosed when the original material lookup succeeds; a request cannot synthesize an absent skipped material.

`chain_reveal_exact` identifies both returned chains with the actual extracted current-chain accessors. `missing_reveals` establishes rejection for every reveal kind when no kernel exists. The source and native role fields remain the same fields used by record sending and opening. Reads do not advance the chain, consume a cached key, change a peer identity, change lifecycle phase or replace a source state. These facts specify the read capability; whether a physical compromise also exposes other copies or runtime state remains an explicit deployment/threat-model question.

## One adaptive execution and private history

`protocolImpl` and `sourceImpl` retain both complete role families and the same shared primitive state used in HB-93. Ordinary record/public requests execute through the existing handlers and return the same dependent result. The adversary may choose a reveal after any observed reply, repeat it, address a missing owner, or stop. `protocol_interpretation` and `schedule_interpretation` prove complete equality between backend interpretation and this actual source experiment through all such continuations, up to the displayed tuple reassociation. The primitive auxiliary state and commitment cache remain present after failures and later reads.

A private `History` contains the global API position and a chronological list of reveal observations. An observation records the original reveal request and its actual optional reply at the position before increment. All source operations increment the position, including rejected operations; only reveals append an observation. `reveal_step` and `source_reveal_step` identify those exact state changes and show that a read leaves every native role field and the entire primitive state unchanged. The reply remains the original returned option, including rejection.

`step_history` proves the exact position increment and zero-or-one appended entry in every supported step. `schedule_history` preserves the entire earlier observation prefix through an arbitrary adaptive run and bounds position and list growth by its total source-query cap. Its support premise describes an actual completed execution; it is not a cryptographic success or probability-one termination premise. The old history may be supplied at entry. A later event/freshness monitor must establish any additional invariant it needs on that earlier history.

The history is private analysis instrumentation, not extra network observation. Its stored secret replies duplicate only the explicitly requested disclosures, and the full interpreter state is never handed to the adversary. No root, unopened skipped slot, identity seed or earlier KDF instrumentation is added to a reveal result. A snapshot or persistence interface must not automatically serialize this ghost state. Physical erasure, foreign-runtime copies and storage ownership remain separate contracts.

## Complete resource ledger

`RawCtxRevealBudgets.Bounded` has six structural coordinates over every possible reply continuation. Let S count sends, R raw attempts, U caller uniform requests, H public commitments, K real public HKDF projections and E compromise reads. `permitted` requires the original coordinate to be available, and `remaining` decrements that coordinate. Failed or repeated operations spend it normally.

`bill_step` and `weighted_bound` compose actual per-step costs through the full private state. `backend_step` derives native costs from the already checked replicated record handlers; `source_uniform_step` derives the uniform cost from the same fixed functional HKDF and shared commitment cache. A read has no cryptographic callback or uniform request. `backend_bound` and `schedule_uniform` therefore retain the previous explicit ledgers under all compromise continuations:

| Resource | Bound |
| --- | --- |
| Native ratchet KDF callbacks | S + 51R |
| Native AEAD seals | S |
| Native AEAD opens | R |
| Shared private/public commitment queries | S + R + H |
| Native frame-writer callbacks | S |
| Real public HKDF projections | K |
| Caller uniform requests | U |
| Complete interpreted uniform requests | U + 64(S + R + H) |
| Compromise read attempts | E |
| All source API operations | S + R + U + H + K + E |

`reveal_bound` projects the E cap, including missing-owner and repeated requests. `source_bound` projects each original service cap. `total_bound` and `total_bill` prove the final sum, which can instantiate `schedule_history`. This is an oracle-call ledger. Lookup traversal, material copying, state access, byte processing, append work and actual deterministic primitive evaluations remain computation. A zero cryptographic-query cost never makes those operations free. Existing instance routing introduces no additional operational selection factor; security reductions must still account for their own identity/session/record choices.

## Remaining composition

This addition covers record-material reads in supplied role states. Identity, prekey/KEM and root compromise require their actual source interfaces; role creation and registration must supply these states with their actual costs and distributions. Snapshot capture, copies, restore, persistence integrity, rollback resistance, crash behavior and linearizable ownership/CAS retain their separate source and deployment obligations. The unkeyed snapshot digest does not supply those properties.

The actual position invariant must connect each returned current chain and skipped material to its directional history. Freshness must exclude disclosed target material and the descendants of a revealed current chain where appropriate. The public fixed HKDF remains real, so this ratchet provides no post-compromise recovery by merely advancing its current chain. The adjacent evolving-key and multi-key CTX hybrids still need to preserve these explicit disclosure replies and histories. The common network experiment must also separate privileged application plaintext from public network observation. These twenty operational/resource statements do not establish those remaining security reductions or a new ProVerif correspondence.

## Focused validation

The two modules pass direct Lean checking with all twenty persistent dependency guards; an independent repeat produces no diagnostics. The complete library passes 3,277 jobs. Independent semantic/integration review approves the exact source accessors, full-state adaptive equations, history preservation, six source caps and native/uniform accounting, and rehashes all 391 unique inventory entries while preserving the earlier 389 paths and their order. The inventory records 227 handwritten Lean files and forty HB-93 statements. Lean policy/root, inventory and whitespace gates pass. Fresh formatting and all sixteen transcript-fidelity tests pass; the fidelity run takes 12.20 seconds. Fetched and direct `origin/vcvio` both identify `8330cdef4f4659931b6764a026cd90c4caf833a4`. No Rust or ProVerif file changes in this milestone, so the user's current validation policy requires no Rust mutation run. These focused results do not replace the complete final matrix on the eventual integrated security theorem and exact merge result.
