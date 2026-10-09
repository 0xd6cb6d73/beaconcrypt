# Record binding resource audit

Read-only audit by `/root/facts_later`, 2026-10-09. No proof or source file was modified. The exact BindingGlobal7 statistical theorem is sound independently of a total finite-coin budget because it bounds digest collisions using actual private and ordinary request caps. This audit distinguishes the source execution, the constructed primitive reductions, and the additional memoizing compiler used to prove that statistical bound.

## Already proved for the actual source record world

`PqxdhRecordLiftWorldBudget.run_native` bounds each final native call counter in the original `PqxdhRecordLiftWorld.run` by `sendCost(kind)*S + receiveCost(kind)*R`. Thus ordinary-record KDF callbacks are at most `S+51*R`, seals and writers at most `S`, opens at most `R`, and native commitment-hash callbacks at most `S+R`. `run_kdf` states the KDF specialization explicitly. These bounds require the outer command budget and include unsuccessful record calls; no selected honest key or successful-record premise is used.

`run_effects` bounds every charged environment-effect category by the explicit startup, direct outer-command and `Caps.envTotal` allowances. `run_hash` combines native and effect hash counters as `H = budget.hash + S + R + envTotal.hash`. `run_uniform_counts`, `run_seed_draws` and `run_uniform` count the actual original execution's finite queries, including cache misses and slot-seed allocations. Its final bound is `startup + budget.coin + budget.test + bounds.max*budget.fresh + envTotal.coin + 64*H + 64*n`. In particular seed work and opaque restricted environment callbacks are not free. Registration and root primitive costs belong to the environment/CE accounting interface; these record-world theorems do not independently prove internal registration query counts.

`PqxdhRecordLiftMixedWorld.run_kdf` already covers every evolving-chain replacement policy with the same `S+51*R` KDF cap. `PqxdhRecordLiftCtxAvailability.program_lookups` bounds the exact compiled source program's hidden lookup requests by `S+51*R`, and `lookup_kdf` charges each such request exactly once, including a table hit. The latter two are reusable pieces, not a published final arbitrary-mode `ctxRun` native-counter bound.

## Already proved for the actual constructed reductions

Let `U = PqxdhRecordLiftCtxBills.programBill .uniform input`, and let `D` denote an actual supported decision-query bound. `CtxBills.program_categories` proves the source service categories and `program_target_seal` proves at most one seal of each selected coordinate. The integrity reduction's concrete `ctxBills` has uniform cap `U+D+64*H`, hash cap `H`, selected seal cap one, and raw cap `R`; `stepBilled` proves those caps for the actual reduction. The privacy reduction's concrete `privBills` has uniform cap `U+D+66*H`, with the same hash/seal/raw caps, again discharged by its actual `stepBilled`.

The privacy reduction uses the proved same-law `bytesSample` implementation: its body sample is one finite query of the appropriate cardinality, and its tag another. Its `66` charge includes the 64-byte private digest sample. That is a correct query bill for the constructed reduction, not a claim that the literal original random-seal sampler executes one byte query for its entire body.

`PqxdhRecordLiftChainBills` separately proves the actual full76 observer finite-query caps. The explicit program cost is `Ecoin+64*Ehash+64*Eadmin+140*S+3940*R`; `observerBill` is twice that cost plus 44 and the supported decision allowance. The chain primitive calls remain the existing explicit full-Extract/Expand reductions, including their two HMAC block queries. No new binding proof changes these bills or their selection factors.

## Additional compiler accounting

`HashPrivateBills.source_private` and `HashOrdinaryBills.source_ordinary` prove `S` and `H` caps for the exact same source compiler, including adaptive continuations. Cache hits reuse their old output; every newly sampled digest is a uniform 64-byte value, with its private/ordinary class fixed before the reply. These caps give `S*(S+H)/2^512`, then the frozen binding term by arithmetic.

`HashFiniteBills.source_interpreted_total` proves the compiler's finite-query bill `U + qBody + 16*S + 64*(S+H)`. `source_decision_total` adds the actual `D`. `qBody` bounds the weighted sum of the actual substituted random-mode body lengths. The command budget alone cannot bound arbitrary caller-supplied plaintext lengths. If a total finite-byte-query bound for this compiler is advertised, the explicit `qBody` premise or an independently established message-length budget must remain visible.

The compiler's native callbacks are deterministic relative to this finite-query interface and produce zero explicit finite queries, while their real KDF/AEAD/writer invocations, charges, source control, cache updates and logs remain in the compiled state. This is not a zero-runtime or zero-primitive-call claim.

## What is not already established by those theorems

I found no final theorem bounding `ctxRun modes replace`'s original native or uniform instrumentation directly for arbitrary replay/random mode assignments. The original `World.run` theorems cannot simply be retyped as such a theorem. `CtxHybrid.allReal_bare` explicitly erases both native and uniform counters; our later counter projection erases uniform counters; the private-cache projection additionally erases selected private cache work. None transports an equality of original work totals.

A direct original-`ctxRun` uniform theorem would require another supported-step accounting induction over literal key interpreters and base services, paying original private opening cache fills as well as original hidden sealing, body/tag draws, known native hashing, lookup sampling and environment work. Existing weighted category/lookup/source bounds make this local rather than a new security reduction, but this endpoint is not currently supplied by `HashFiniteBills`. Similarly a direct arbitrary-mode native-counter endpoint would require joining retained native charges and known-record calls to the weighted source caps. It should not be inferred from counter erasure.

This missing internal-world instrumentation endpoint does not invalidate the exact BindingStatement, the already-proved original production-world resource bounds, or the constructed reduction bills. It is a genuine additional obligation only if documentation or a later theorem advertises that particular internal world's full counters. The final audit should cite the source-world bounds, reduction bills and compiler bill separately and avoid asserting a common total or numerical equality among them.

## Principal source locations inspected

- `PqxdhRecordLiftWorldBudget.lean`: run_native 349, run_kdf 366, run_effects 473, run_hash 490, run_uniform_counts 781, run_seed_draws 982, run_uniform 996.
- `PqxdhRecordLiftMixedWorld.lean`: run_kdf 252.
- `PqxdhRecordLiftCtxAvailability.lean`: lookup_kdf 94, program_lookups 1142.
- `PqxdhRecordLiftCtxBills.lean`: program_categories 279, program_target_seal 342, ctxBills 595, stepBilled 613.
- `PqxdhRecordLiftCtxPrivBills.lean`: seal_uniform 56, privBills 498, stepBilled 513.
- `PqxdhRecordLiftChainBills.lean`: programCoins_closed 578, observerBill 728.
- `PqxdhRecordFactsHashFiniteBills.lean`: source_coins 209, source_interpreted_total 282, source_decision_total 307.

The unchanged Lift files were read from the frozen source available in the KnownLedger worktree; new HashFiniteBills was read from the owned Draw worktree without modification. Line numbers are navigation aids, not content pins.
