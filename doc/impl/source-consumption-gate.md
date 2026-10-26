# Exact source consumption guard

The published [receive-consumption component](source-receive-consumption.md), `df11bc5c222684ceedb687f30afa22a83dfe3781`, records actual successful receive positions without changing source execution. `RawCtxConsumptionGate` now proves that an explicit private guard against those consumed positions is the same reachable source computation. The guard is derived from the actual source state; it is not a new authentication, fresh-key or capability assumption.

## Derive rejection from the source

A consumed position is below the native receive counter and absent from its live skipped-material cache. `receive_spent` follows the existing extracted zero/replay admission rules to prove exact rejection before any KDF or opening capability is requested. It permits target zero explicitly and does not presume an ideal decryption result. The source kernel remains unchanged.

`rawReceive_spent` lifts this equation through the functional decoder, sender pin, frame validation and actual raw wrapper. The result is the original `None` and original owner with its raw-attempt counter incremented once. `rawGame_spent` then retains arbitrary complete primitive state: because the actual consumed branch requests no primitive operation, the entire primitive state is unchanged. This does not reset or discard any failed commitment or AEAD effects; those failures belong to different source branches and continue to execute normally.

`tracked_raw_spent` identifies the same result in the existing private monitor. An actual `None` adds no history entry. These four equations retain the complete source computation, rather than infer state behavior from a marginal rejection probability.

## Explicit guard and complete continuation

`gatedImpl` uses the same pure decoder to identify the submitted sequence. If that position is already in the private history, it returns exactly the proved source rejection/publication. Otherwise it invokes the original monitored operation. Sending is the unchanged original operation, including advancement after failed sealing. This definition does not introduce a different record-opening predicate or inspect a secretly recovered plaintext.

| Checked statement | Established fact |
| --- | --- |
| `receive_spent` | Actual consumed-target core admission rejects before all callbacks, including target zero. |
| `rawReceive_spent` | The original raw wrapper returns exact rejection and raw-attempt publication for a consumed decoded target. |
| `rawGame_spent` | The same branch retains arbitrary complete primitive state with no query. |
| `tracked_raw_spent` | The actual private monitor returns the same rejection and leaves its history unchanged. |
| `gated_step` | The explicit private guard equals the original full source step on the derived kernel/history relation. |
| `gated_schedule` | Every adaptive mixed send/raw continuation has identical full replies, history, owner and primitive state. |
| `gated_source_erasure` | Erasing only private history gives the original complete source oracle program. |
| `gated_query_bounds` | Every selective underlying uniform-oracle query cap is exactly equivalent to the source cap. |
| `initialized_erasure` | Either actual core initializer derives the empty-history equivalence for any supplied root. |

The schedule proof preserves the existing source invariant through every supported original reply before applying its induction hypothesis. It does not assume the final no-replay conclusion or require successful opening. The initialization corollary uses the actual source initializer equality and derives the required directional origins and empty history internally. It does not impose an honest, uniform or independent root distribution.

## Accounting and observation

The full adaptive equality is at `OracleComp` before a final observation is projected. Both successful and rejected raw operations retain all effects; any original callback or public action remains in the underlying source computation. The inherited fixed-source mixed budgets therefore remain `S + 51R` KDF callbacks, `S` seals, `R` openings, `S + R` commitment hashes and `S` writer calls, with `64(S + R)` interpreted uniform-byte draws. The source history length remains at most `R`. The exact selective query equivalence adds no uncharged cryptographic oracle request or distributional cost shortcut.

The guard can perform extra pure decoding and list membership work before delegating. Its equality is about functional outcomes and primitive queries, not equality of native parser traversal, timing, allocation or total local instruction traces. Native codec resource/error behavior retains its existing functional library boundary; ordinary byte copying, history lookup, parsing and monitoring are local work. No constant-time or runtime bound follows from unchanged uniform counts.

The private history is excluded from adversary replies, reveals, snapshots and persistence. Actual plaintext remains the original optional API result; whether it becomes a network observation is a separate declassification/freshness policy. No new public rejection oracle, key disclosure or state-inspection capability is added to the source experiment by this private proof wrapper.

## Remaining persistent mapping

This is one uninterrupted initialized owner with the existing fixed functional KDF, original material correlations and complete shared primitive state. Distinct positions may use equal key/nonce bytes. A snapshot restore or copied earlier kernel can make a past target available again and does not automatically preserve the current history relation. The global theorem must supply actual ownership, persistence integrity, rollback resistance, linearizable publication, crash behavior and freshness policies where needed. An unkeyed snapshot digest supplies none of those properties.

The guard provides a justified one-use position boundary for a future stronger symbolic receiver. It does not yet remove the source kernel from the non-consumed branch, establish the per-position process's full raw/optional-reply trace inclusion, or justify any fresh independent symbolic key labels. That process mapping must also preserve source input routing, all failed primitive effects, exact context, both directional material positions and permitted send schedules. The completed finite registration-admission family and the unclassified persistent ProVerif saturation diagnostics remain separately scoped. Actual registration/lifecycle handoffs, source evolving-output hybrid consistency, compromise/restore behavior and the global computational-symbolic correspondence remain required. No protocol or primitive implementation changes are made here.

## Focused validation

The final candidate passed the full locked Lean build (3,221 jobs), direct checking of the new module and its nine persistent dependency reports, the root import check, and the inventory check (171 Lean files and 320 unique entries). All 16 source-fidelity tests passed in 11.98 seconds; formatting, forbidden-proof scans and whitespace checks passed. Independent review directly checked all nine reports, rehashed all 320 entries and confirmed that the prior 319 paths and their order remain. The immediately preceding unchanged Rust inputs inherit the published `df11bc5c222684ceedb687f30afa22a83dfe3781` Rust 1.96 workspace Clippy result (19.80 seconds, with the documented existing warnings); no Rust or ProVerif source changed in this checkpoint, and no new mutation run was required under the user’s proof-only testing instruction.

A fresh private fetch and direct remote query both returned `8330cdef4f4659931b6764a026cd90c4caf833a4` for `vcvio`, which remains an ancestor of this topic. These are current focused operational-proof results. The earlier finite registration, symbolic and mutation results remain inherited evidence with their recorded scopes; this checkpoint does not classify any persistent ProVerif query or establish the global computational-symbolic correspondence.
