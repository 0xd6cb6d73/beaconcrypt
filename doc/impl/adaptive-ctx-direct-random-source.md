# Independent adaptive CTX random source (HB-85 continuation)

`AdaptiveCtxDirectReplay` specifies the comparison source independently at the ordinary nonce-AEAD sealing interface. It has no record key or base-opening operation. The source commits the actual ciphertext returned by that oracle, retains its public and private digest caches, and answers raw requests from its complete successful CTX tuple history. Every well-formed raw request performs its original private suffix lookup before that reply, including requests that fail or repeat. An exact full-continuation theorem connects this source to the reviewed guarded reduction before choosing either a real or random encryption interpreter.

This closes the separate direct-source interpretation left by the privacy-view checkpoint `62b40906fe54b122bb652bbbbe41c0b6506ee913`. It remains a one-key chosen-plaintext component with the existing typed raw decoder. It does not supply native Cap'n Proto correspondence, consuming ratchet semantics, independent evolving keys, reveals, target/session selection or the common global protocol experiment.

## Exact interface and full-state equality

`directImpl` accepts the unchanged four source request classes: arbitrary finite uniform requests, public hash bytes, sealing input with original plaintext/nonce/context, and arbitrary raw bytes. `directPublic` runs the existing public cache operation. `directPrivate` runs the actual private suffix dictionary and records its input. `directSeal` forwards the original ordinary sealing input once; rejection leaves source sealing history unchanged, while success commits the actual returned body/tag and appends that entire CTX tuple. `directRaw` increments the attempt counter, rejects decoder failure, and otherwise performs the same private lookup before returning an issued full-tuple plaintext or rejection. That plaintext comes only from an earlier successful source sealing input; no secretly opened plaintext is inserted into an adversarial target.

The direct program accepts arbitrary ordinary sealing replies. In particular, none of the simulation equalities assumes real-world AEAD correctness, nonce uniqueness, consistency of an externally supplied prior log, or a relation between the ordinary reply and a hidden key. This is necessary because the same program must work under ordinary random sealing. The ordinary random interpreter itself enforces its per-key nonce-use rule; the source does not infer nonce freshness from equality across unrelated keys.

The following statements preserve the complete result and state, not merely ciphertext marginals:

| Statements in `AdaptiveCtxDirectReplay` | Checked meaning |
| --- | --- |
| `runLogged_eq_adapter`, `adapter_uniform`, `adapter_primitive` | The retained log simulator equals an explicit ordinary adapter. Every original ordinary request and internal random draw executes in source order before its complete continuation; only actual successful ordinary seals enter the base log. |
| `adapter_private`, `adapter_public`, `adapter_seal`, `adapter_raw`, `adapter_query` | Each guarded source request equals the separately specified direct operation. Both caches, failed private lookups, raw counter, private input history and complete ordinary seal log are retained. Only the raw optional reply is replaced by the already-reviewed public guard. |
| `directPrivate_history`, `directPublic_history`, `directSeal_history`, `directRaw_history`, `directImpl_history` | The direct source's successful CTX history is exactly reconstructed from the actual sealing replies under every supported ordinary response. Raw and hash operations preserve that history, even while updating caches. |
| `recordReply_guarded`, `guarded_query_expand`, `guarded_query_complete` | Guard bookkeeping and nested state association agree for a complete query. Replacing a raw reply does not alter sealing history; no initial base-log consistency premise is needed. |
| `guarded_run_complete`, `sourceClient_direct` | Every adaptive continuation has the same complete ordinary execution. The original result, full source state and entire base log remain; only redundant guard history and tuple association are projected. |
| `interpreted_complete` | Any stateful ordinary interpreter preserves that equality jointly with its own entire final state. This theorem precedes selection of the random interpreter. |
| `viewReduction_direct`, `randomView_direct` | The reviewed Boolean reduction is exactly the original decision of the direct program, and its ordinary random game is exactly the new direct random view. Private terminal state is projected only after full-state equality. |
| `canonical_directRandom_advantage_bound` | The existing canonical shared-ROM privacy bound reaches this independently specified random source with the same reductions and loss coefficients. |

`directWithBase` retains the redundant ordinary history explicitly. `directClient` starts the complete source and that history empty. `directRandomGame` interprets it by the existing ordinary random sealing oracle, retaining both source and challenger state; it samples no record key. `directRandomView` returns only the original adversary's Boolean decision. The retained private state is analysis output, not an adversary reveal. The program is not a separately sampled random table of record keys or independent projections of one expansion.

## Reductions, losses and resource units

For the same source client with public-hash cap `qHash`, seal cap `qSeal`, raw-attempt cap `qRaw` and `qSeal < 2^96`, the checked bound is:

```
Adv(canonical source decision, direct random source decision)
  <= AdvIND$(prefix validationReduction)
   + qHash / 2^128
   + 2 * sum(i < qRaw, AdvINTCTXT(indexedReduction i))
   + qRaw / 2^512
   + AdvIND$(ciphertext viewReduction).
```

These are the existing concrete reductions, with unchanged input distributions and winning events. The two IND$ terms belong to different reductions. The integrity term is twice the same indexed family: one copy pays for adaptive optional-opening replacement and one pays for prefix-event transport. Every malformed, rejected, repeated and successful raw slot remains in its original index range; the private-alias term counts those slots once. The prefix validation uses one additional fresh-nonce empty-message seal, while the ciphertext-view reduction uses only the source sealing requests. Each indexed integrity reduction makes at most `qSeal` seals and one final ordinary verification. No coefficient, failed cache effect or final-state correlation is omitted by the new equality.

`AdaptiveCtxDirectReplayQueryBounds` proves five resource statements. `directClient_seal_bound` retains `qSeal`. `directClient_uniform_bound` retains `qCoins + 64*(qHash + qSeal + qRaw)` uniform-oracle requests. `directClient_plaintext_bound` retains the weighted total submitted plaintext cap `qBytes` through every possible adaptive reply. `directRandomGame_uniform_bound` bounds the complete retained-state random execution by `qCoins + 64*(qHash + qSeal + qRaw) + qBytes + 16*qSeal`; `directRandomView_uniform_bound` preserves that cap after the public decision projection. Each digest miss contributes 64 byte-valued draws, whereas a separately counted source uniform request may use another finite range. Used-nonce rejection and cache hits can reduce actual sampling. The random game has no additional key draws; the unchanged real view challenger still pays its separate 32 key-byte draws. The prefix-validation random challenger retains its separate `16*(qSeal+1)` tag cap and the same `qBytes`, because its added validation message is empty.

These are oracle and submitted-byte bounds. Public verification, commitment serialization, input parsing, finite log/dictionary lookup, ciphertext construction and candidate-key evaluation remain actual local work. The mathematical implementations inherit noncomputable oracle/cache representations; no compiled Lean reduction or complete machine-runtime bound is claimed. No exponentially large analysis table is executed by the direct source. Native callers must eventually supply their own complete input-byte, record/session and local-work budgets.

## Source and deployment boundary

The source request wiring is the existing reviewed one-key CTX interface, including `outerSuffix`, actual optional replies and the `RawDecoder` boundary. A native raw receive adapter must separately connect source-selected material, nonce, sequence, sender and associated data to that input, preserve primitive effects across rollback, and consume ratchet material exactly as production does. The comparison's full-tuple replay reply is an ideal-component operation; it does not itself consume production replay state.

The source sealing interface is chosen-plaintext. If a common experiment exposes an unknown target plaintext through a native optional receive result, its freshness or declassification rules must reflect that disclosure. ProVerif's public network observation does not automatically include honest application return values. Dynamic sessions, correlated evolving material, snapshots, erased past keys, reveals and compromise must be composed in the same global experiment before using this component as a protocol theorem.

Perfect primitive implementations, compiler behavior, allocator/OS behavior, physical erasure, foreign copies and durable storage remain external contracts. The random oracle assumption remains the stated programmable classical ROM interface, not a consequence of collision resistance. Persistence integrity, rollback resistance, linearizable CAS, ownership and crash behavior remain explicit deployment premises; an unkeyed digest supplies none of them.

## Focused validation

Both new modules directly check all twenty-seven persistent guarded dependency reports, and the root import checks. The full `lake build` passes all 3,198 jobs; the reviewed inventory passes all 297 entries with 148 handwritten Lean modules. Formatting, forbidden-placeholder/custom-axiom and diff-whitespace scans pass. Existing proof gates are retained, and no production Rust, schema, binding, ProVerif model, query, runner or mutation-tested runtime source changes. These are focused component checks; the entire runtime, symbolic and mutation matrix remains required on the eventual exact integrated `vcvio` result. A fresh fetch and direct private-remote check still identify `origin/vcvio` as `8330cdef4f4659931b6764a026cd90c4caf833a4`, already an ancestor of this topic. No Nix garbage collection runs while the proof lanes use the saved environment.
