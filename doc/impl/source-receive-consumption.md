# Source receive consumption

`RawCtxReceiveConsumption` supplies the operational consumption law needed before a persistent symbolic receiver may treat a successful record position as consumed. It executes the original extracted source receive/send interfaces and their actual shared fixed-HKDF/CTX interpretation. It does not impose an ideal authentication predicate or prevent a request by checking a new history. This is an HB-91 follow-on based on the reviewed source material-position checkpoint `a8d3209b67e56f68a1686b84cbd4b59300ab160d`.

## Actual state transitions

`Transition` separates actual optional rejection, cached success and future success. Rejection retains the receive state. Cached success requires the actual stored target material and removes only that index. Future success advances to the actual source `futureReceiveState`, including the corresponding skipped positions. The abstract future constructor deliberately omits the source window/cache-room guard, so it permits additional transitions. `receive_transition` derives this relation from every supported actual source execution, retaining the real capacity branch and complete primitive/log poststate. It does not alter source admission or prove the converse inclusion.

A consumed index is below the current receive counter and absent from the live cache. `Spent` describes exactly those facts. Source cached and future publication preserve them. Consequently a later successful source receive cannot select an earlier consumed index, even if unrelated positions happen to have equal material bytes. No key, nonce, chain or root injectivity is assumed.

| Checked statement | Established fact |
| --- | --- |
| `receive_transition` | Every actual generic receive outcome refines its cached/future/rejection transition with the complete callback state retained. |
| `Transition.success_fresh` | The selected successful target was absent from the previously consumed indices. |
| `Transition.preserves_past` | Every retained cache index stays below the actual receive counter. |
| `Transition.preserves_spent` | Cached/future success records the selected target; rejection preserves the previous consumed-index invariant. |
| `Transition.spent_nodup` | Recording the actual result preserves a history with no duplicate successful positions. |
| `native_receive_transition` | The exact shared native callback interpreter has the same source transition after erasing only the private KDF log. |
| `native_receive_spent` | The native receive result preserves the whole kernel/origin/consumption relation and actual primitive poststate. |
| `recordReply_eq` | The actual successful reply's sequence agrees with the decoded target when supplied the already checked source metadata equality. |
| `raw_spent` | Every raw parsing, pin, validation and source-opening outcome preserves the consumption invariant, recording the actual returned sequence. |
| `native_send_spent` | Actual source sending preserves receive consumption, including failed sealing and send exhaustion. |
| `send_spent` | Empty requests and the complete send wrapper preserve receive history and all actual source effects. |
| `shared_receiveNative` | The receive handler is the actual common shared-state handler used by the mixed owner. |
| `tracked_step_spent` | Recording after one original mixed operation preserves the complete owner invariant. |
| `tracked_schedule_spent` | Arbitrary adaptive mixed send/raw continuation preserves that invariant through every actual optional reply. |
| `tracked_erasure` | Erasing only the private history yields the identical full `OracleComp` computation and complete final source state. |
| `tracked_step_length` | A raw operation adds at most one position and a send adds none, including every rejected attempt. |
| `tracked_schedule_length` | Any all-continuation raw-query cap bounds the history's total growth. |
| `initialized_spent` | Either actual source initializer establishes its own oriented origins and empty consumption history for the supplied root. |
| `ConsumedRefines.spent_nodup` | The retained source invariant projects to duplicate-free recorded positions. |
| `source_supported_history` | Every supported original initialized source execution has the same complete result with a private duplicate-free history of length at most `qRaw`. |
| `tracked_query_bounds` | Every selective underlying uniform-oracle query bound is exactly equivalent before and after adding the private monitor. |
| `tracked_raw_success_fresh` | The sequence in an actual successful raw API reply was not previously recorded, derived from source execution rather than imposed on the request. |

## Full source execution and observation

`ConsumedRefines` combines the existing complete kernel/material relation, the original send-origin alignment and the consumed-index invariant. The exact native receive callback is the published source handler with the same fixed HKDF function and shared commitment cache. The generic receive theorem permits arbitrary callback plaintext and state effects; the concrete raw theorem retains the actual native optional opening, source-selected target and full primitive state. It uses source metadata provenance to identify the sequence in a real returned `Decrypted`, rather than inserting a recovered plaintext into an adversarial target.

The private `trackedImpl` executes `RawCtxMixedOwner.sourceImpl` first, then records only the position from its actual successful raw reply. It never inspects the history to authorize, reject or change a reply. Source sends still allocate and publish their advanced kernel after failed sealing, while their receive fields and history remain intact. Failed raw calls restore only the source owner state; any hash/cache effects remain in the actual primitive result. The complete adaptive erasure equality retains these effects and all optional API returns, not merely their marginal distributions.

The actual source initializer establishes the empty history at either role's own directional origins for every supplied root. No honest, uniform or independent root premise is needed for these operational statements. Subsequent continuations contain mixed send/raw operations on this same uninterrupted owner. Record-position uniqueness does not imply uniqueness of key/nonce bytes or identify a cryptographic session. The real API plaintext is retained; whether an adversary may observe it remains a separate network/declassification policy.

## Queries and private state

The original structural send/raw budgets remain on the unchanged source program. The private list adds no primitive oracle request, and `tracked_query_bounds` proves an exact equivalence for every selective underlying uniform-query predicate. In the concrete shared fixed-source interpretation, the inherited source bounds remain `S + 51R` KDF callbacks, `S` seals, `R` openings, `S + R` commitment hashes and `S` writer calls. The complete shared random-oracle interpreter costs at most `64(S + R)` uniform-byte draws; the deterministic KDF contributes no uniform query. Those bounds belong to the existing source programs and all their continuations, not to an inference from evaluated marginal equality. Every raw attempt counts toward `R`; the private history grows by at most `R`.

The private history and earlier KDF logs are analysis artifacts, excluded from all adversary replies, reveals, snapshots and persistence. Full theorem state is not public network output. Native HKDF/HMAC, hash/AEAD, parsing, copying, list operations, logging and any lookup work remain real computation. The proof supplies no new runtime or memory complexity bound.

## Remaining bridge

A persistent ProVerif abstraction must still map each original raw attempt, optional result and successful-consumption transition into the same symbolic owner/position process while retaining actual directional material correlations. The broader `Transition` relation is one component of that mapping, not an already proved process simulation. Existing saturation timeouts and allocation failures of the full persistent symbolic worker remain unclassified; the completed finite general-admission family is separately scoped and is not reinterpreted as persistent proof coverage.

This checkpoint has no restore, snapshot-copy, crash, concurrent-owner or lifecycle transition. Restoring an earlier kernel may make an already consumed position available again; a global theorem needs explicit storage integrity, rollback resistance, linearizable publication and ownership premises, or appropriate freshness exclusions. No unkeyed digest supplies those premises. Native primitive, decoder, representation, compiler and deployment contracts remain external as documented. A fresh-output evolving-key interpretation, correlated multi-key AEAD reduction, global registration/reveal schedule and computational-symbolic event correspondence remain separate obligations. No cryptographic algorithm implementation is proved here.

## Focused validation

The complete Lean library passes 3,220 jobs. The changed module, all 22 persistent dependency reports and the complete root pass direct checking; an independent reviewer repeated the 22 guards and reviewed the actual source statements, query accounting and scope. Inventory validation passes with 170 handwritten Lean modules and 319 unique reviewed artifacts, preserving all 318 preceding paths and their order. Fresh transcript fidelity passes all sixteen tests in 11.73 seconds. Formatting, whitespace and forbidden-placeholder/custom-axiom scans pass. Full Rust 1.96 workspace/all-target/all-feature locked Clippy passes in 19.80 seconds with the existing core warnings. Initial pinned-vector setup was blocked by sandbox access to worktree Git metadata; the authorized setup then completed under approval with both exact pinned revisions, and the complete Clippy command ran successfully. No Rust or ProVerif source changes in this checkpoint; the user's current mutation policy requires no new Rust mutation run. Fresh fetched and direct `origin/vcvio` both identify `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. These are focused operational checks, not a fresh full integrated runtime/ProVerif matrix or a completed global security proof.
