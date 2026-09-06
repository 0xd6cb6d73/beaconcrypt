# Adaptive observation of a private source chain (HB-84)

`PqxdhAdaptiveChainObservation` connects the source's iterative 76-byte derivation to arbitrary bounded adaptive clients. A client may use every returned message-key/nonce pair, request explicit randomness, choose its next action from earlier replies and stop early. The exact correspondence retains its complete result and actual derivation count. The same ordered Extract/HMAC reductions then compare this execution with a finite independent material tape, without an additional stopping-time selection factor.

This follows `3cc6747da054dcaa1fd3c9d26466d279d367de1d`. Its entry is one uniform 32-byte chain sampled independently of the context. It is a private derivation capability for a later protocol interpreter, not a new public key-reveal API. The result does not yet supply native ratchet admission/consumption, initial authenticated-root sampling, two-direction interleaving, snapshots, current-chain reveals, evolving-key aliases or global session/freshness composition.

## Exact source and observation

`sourceImpl` has two request classes: the caller's original finite uniform request and a private next-material request. The former is forwarded unchanged and preserves the chain and derivation counter. The latter performs the same source `productionStream` for the ratchet domain, returns its 32-byte key and 12-byte nonce together, installs its 32-byte next chain and increments the counter once. It never uses an independent message-key table.

`tapeImpl` forwards identical caller randomness and reads one material pair from a retained list for each private derivation. Its arbitrary exhausted-list fallback is unreachable under the theorem's remaining-request bound. This bound is VCVio's structural `IsQueryBoundP`: it covers every possible reply continuation, including ones that may not occur in the real source. There is no successful-target or honest-client premise.

`sourceView_tapeView` proves equality of whole `OracleComp` observations for every starting chain and counter. An adaptive source loop and a tape containing the exact `realEvolution` material history return the same original client result and derivation count, with the same explicit randomness requests in the same order. The induction follows the actual next source output and decrements the remaining derivation budget. It does not substitute a marginal output distribution. Intermediate private chains and the unused tape suffix are projected before comparison; a client can retain its complete returned transcript in its result. A public current-chain reveal is not silently added to this interface.

`tapeObserver` runs this original client on a finite history, then invokes the entire supplied probabilistic final observation on its result and count. `sourceGame_eq_hybrid` is complete computation equality with the initial ordered-chain hybrid for that observer. `final_hybrid_eq_eager` identifies the final hybrid with a separate finite random-tape game; only the independent unused final live-chain draw is removed using its proved losslessness. The tape contains exactly the requested maximum number of material pairs, so this comparison does not enumerate an exponential table.

## Reductions and accounting

`adaptive_advantage_bound` applies the existing ordered bound to that exact observer. For a derivation budget B it gives the sum, over every i from 0 through B−1, of the named `hopLoss` at cut i and remaining length B−i−1. Each summand is one fixed-zero-salt whole-PRK Extract distinguishing advantage plus one ordinary uniform-secret-key HMAC PRF advantage for the constructed sampler and complete adaptive observer. Each has coefficient one. There is no extra adaptive stopping or target-position factor. The existing `SourceFullCorrect` functional contract is unchanged; no new primitive endpoint or protocol-security premise is introduced.

`sourceImpl_requests` proves the exact per-request counter change. `sourceRun_requests_bound` proves that every supported complete source result uses at most B derivations above its entry count, including its final requested step before stopping. Support assertions do not assert losslessness for any separately supplied final observer.

Let S bound context-sampling uniform requests, C bound every caller continuation's explicit uniform requests and F bound every possible final observation. One material draw consists of 44 byte-valued uniform requests; the caller's explicit uniform request may instead have any finite range. The checked counts are uniform-oracle requests, not a claim that all requests are byte-valued or that deterministic work is free.

| Checked statements | Query scope |
| --- | --- |
| `sourceRun_uniform_bound` and `tapeRun_uniform_bound` | At most C uniform requests for the complete client run from any source/tape state. Source derivations and tape lookups add no random draw. |
| `tapeObserver_uniform_bound` | At most C + F for every finite history, context and possible client result. |
| `sourceGame_uniform_bound` | At most S + 32 + C + F, including the actual initial chain. |
| `eagerGame_uniform_bound` | At most S + 44B + C + F. Every reserved material pair is charged, including the unused suffix after early stopping. No live-chain draw occurs in this separate comparison game. |
| `adaptiveReduction_query_bounds` | Each exact HMAC reduction has two challenge queries and at most S + 44i + 32 + C + F local uniform requests. |
| `adaptiveChallenger_query_bounds` | With J = S + 44i + 32 and O = C + F, real Extract costs J + O; uniform Extract J + 64 + O; real HMAC 64 + J + O; random HMAC J + 128 + O; and independent full output J + 76 + O. Ignored chain draws and both random HMAC blocks remain charged in these endpoint worlds. |

The source performs one deterministic 76-byte HKDF operation for each counted private derivation. The reductions also evaluate their remaining real suffixes and final observer, while the eager comparison constructs and reads a finite list. Those public primitive evaluations, byte/list operations, input construction and copies remain real local computation. The query lemmas do not establish native runtime bounds or a compiled reduction. All ambient source services must be included when a later interpreter supplies the context, client or final observer; zero declared randomness does not make such services free.

## Remaining source and trust boundary

The actual source root/chain distribution must be connected through the authenticated-root and initialization reductions inside the same experiment. This result starts from its explicitly independent uniform chain. Neither arbitrary raw traffic nor source rollback permits assuming that every installed record key is independently fresh. Native callback routing must identify the actual material handle, nonce, sequence and full context; the separate effectful receive proofs preserve those operational fields but do not by themselves establish the combined reduction.

The existing source fact that knowledge of a current chain determines its descendants remains valid. This theorem has no current/intermediate-chain reveal operation and claims no recovery after compromise, persistence rollback security or resistance to copied snapshots. Complete bidirectional scheduling, key aliases, target selection, declassification of application plaintext, network capabilities and deployment freshness still belong to the common protocol experiment. Perfect primitive implementation, compiler, storage, physical erasure, foreign-copy and deployment contracts remain external. No primitive algorithm or implementation proof is attempted, and the deprecated public-HKDF/random-table interpretation is not used.

## Focused validation

The new module and all thirteen persistent guarded dependency reports pass direct Lean checks. The root import passes directly and the full `lake build` passes all 3,172 jobs. The reviewed inventory passes with 124 handwritten Lean modules and 273 unique entries. Rust formatting, forbidden-placeholder/custom-axiom and diff-whitespace scans pass. Independent review covers the exact source/observation, reduction and resource scope; final integration into `vcvio` remains separate. Production Rust, schemas, bindings, symbolic models, runtime tests and mutation inputs are unchanged in this topic. This validation does not substitute for the complete matrix on the eventual exact integration result.
