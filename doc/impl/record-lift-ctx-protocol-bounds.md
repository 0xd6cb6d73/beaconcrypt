# Actual global CTX reduction query accounting

`PqxdhRecordLiftCtxProtocolBounds` supplies the query accounting for the concrete ordinary reduction constructed in `PqxdhRecordLiftCtxProtocol`. Its sixteen theorems examine the actual ten private protocol services, then carry their costs through the complete adaptive continuation and the existing dynamic known-key wrapper. This is an operational accounting result; it introduces no primitive or security assumption.

## Per-service costs

The four columns below count requests at the ordinary selected-key CTX interface. The hash column includes shared public and caller-known hashing. The last two columns count selected-key sealing and raw verification attempts, including rejected attempts. A hidden record that routes to a known nonselected key contributes its possible hash request through the same dynamic wrapper.

| Private service | Explicit uniform queries | Hash queries | Selected seals | Selected raw attempts |
| --- | ---: | ---: | ---: | ---: |
| Allocate initial seed | 64 | 0 | 0 | 0 |
| Lookup evolving output | 76 | 0 | 0 | 0 |
| Public coin | 1 | 0 | 0 | 0 |
| Public hash | 0 | 1 | 0 | 0 |
| Labeled opening | 0 | 1 | 0 | 1 |
| Labeled sealing | 0 | 1 | 1 | 0 |
| Caller-known receive | 0 | 1 | 0 | 0 |
| Caller-known send | 0 | 1 | 0 | 0 |
| Charge effect | 0 | 0 | 0 | 0 |
| Publish pending frames | 0 | 0 | 0 | 0 |

These are upper bounds for separate ledgers, not a claim that every column is charged simultaneously. For example, a selected opening forwards its raw attempt, whereas a known opening performs real local AEAD work and forwards its shared hash. `service_total` also bounds the total endpoint requests by 64 for allocation, 76 for lookup, zero for charge/publication, and one for each other service. Every seed or output table hit retains its cached answer and can cost less than its miss bound. The allocation and output misses specifically sample 64 and 76 bytes. A public coin can request an arbitrary finite uniform value and contributes one query of its actual type. The output miss draws one full 76-byte value; its projections are not independently resampled.

## Source work and reduction work

`known_receive_hash` and `known_send_hash` derive the one-hash bound from the literal source receive/send adapters, including cached and future receive paths, failed opening, and writer failure. `knownRom_total` and `knownProgram_total` retain the entire native program and carry that bound through the shared-ROM presentation. Public functional KDF/AEAD calls still execute with their actual arguments. They do not become selected-key oracle calls merely because the reduction evaluates them locally.

The source's native KDF ledger is a separate quantity: the already checked `PqxdhRecordLiftMixedRecords.known_send_bound` and `known_receive_bound` give one and 51 logical KDF requests for the respective caller-known operations. The companion global source laws preserve native counters before the explicit `Bare` projection removes those unobservable counters. The present theorem does not turn a source counter into an ordinary endpoint request or discharge a global source ledger cap. Likewise, the uniform column counts explicit forwarded uniform requests; random-oracle cache filling remains charged by the existing CTX component's own hash/ROM accounting.

`uniform_other`, `public_other`, and `lookup_other` prove that these actual interpreters make no requests in the unrelated categories. `opening_categories`, `sealing_categories`, and `known_categories` preserve the full optional replies and private state. They retain the distinction between an explicit selected-nonce refusal and a successful endpoint call followed by writer `None`. The latter attempt remains charged and logged. No equality or inequality assumption is made about caller-known key bytes and selected key bytes.

## Adaptive continuation and ordinary endpoint

`CostBound` is a weighted syntactic bound on the actual `Protocol.ServiceSpec` client: at every possible query it subtracts that service's stated cost, and the remaining bound must hold for every typed reply. `schedule_total` and `schedule_categories` prove the resulting endpoint bounds through the complete `ExceptT` computation. On an error reply the suffix stops; on an ordinary optional reply it continues with the complete poststate. No successful-run premise is used, and no ambient continuation is treated as free.

`reduction_budgets` applies those bounds to the exact `CtxProtocol.reduction`. Given four service-client budgets, the constructed reduction makes at most `qUniform` explicit uniform requests, `qHash` shared hash requests, `qSeal` selected sealing requests, and `qRaw` selected raw verification requests. It has no selected-key parameter. The existing dynamic known-key compiler preserves these four ledgers while evaluating each actual known key locally and forwarding its shared hash requests. This covers arbitrary adaptive optional replies and every possible verification attempt, not just one chosen successful attempt.

The weighted client bounds remain explicit premises here. The later source-syntax transport must derive their numerical values from the frozen protocol request budget, including all initialization, environment and administrative requests. Actual-support bounds under the real source interpreter cannot substitute for these all-reply bounds in changed CTX games. This package also leaves selected-key uniformity, selected-nonce stop elimination, record selection, alias-event bounds, and the final secrecy/authentication event comparison to their respective joins. It does not claim those conclusions from query accounting alone.

## Validation status

Independent semantic review approved all sixteen statements after clarifying that the shared ledger counts explicit uniform queries; seed/output misses specifically use 64/76 byte queries. The final exact guarded module check, companion protocol52 check, root import, inventory (1,622 handwritten Lean modules), and transcript fidelity checks (20 Python checks and 30 Rust tests) pass on central `2f69a484`. Final publication metadata review is pending. No Rust or primitive implementation changed.
