# Concurrent persistence results

Row persistence substantially improved the concurrent PostgreSQL workloads. Keeping decoded rows in memory removed a database fetch, but its additional timing benefit depended on the workload: cached rows helped the large bursts, while ordinary rows were slightly faster in several high-frequency cases. The existing snapshot and row APIs remain available alongside `CachedRowServer`.

The completed comparison contains PostgreSQL at 1, 100 and 1,000 registered peers and SQLite at 1 and 100 peers. SQLite at 1,000 peers was stopped at the user's request; its interrupted attempts are excluded from all results below. There are 65 workload/population/backend groups, three trials per group, 585 arm/trial records and 1,270,800 measured callbacks. The [evidence directory](concurrent-row-persistence-results/2026-10-25/README.md) contains all retained and discarded attempts, raw observations, analysis inputs and validation records.

## High-frequency traffic

This case offers one 1,024-byte callback every 5 ms per active peer for two seconds. With 32 active peers, that is 12,800 callbacks per arm, or 6,400 offered callbacks per second. Values below are the median of the three trials. Duration includes draining all offered work. Deadline success uses a one-second response deadline measured from the planned arrival.

| Database | Registered / active peers | Snapshot duration | Row duration | Cached-row duration | Deadline success: snapshot / row / cached |
|---|---:|---:|---:|---:|---:|
| SQLite | 1 / 1 | 2.432 s | 2.566 s | 2.350 s | 100% / 100% / 100% |
| SQLite | 100 / 32 | 88.258 s | 83.099 s | 81.801 s | 1.18% / 1.64% / 1.45% |
| PostgreSQL | 1 / 1 | 1.997 s | 2.003 s | 1.998 s | 100% / 100% / 100% |
| PostgreSQL | 100 / 32 | 55.782 s | 5.516 s | 5.713 s | 1.84% / 29.70% / 31.02% |
| PostgreSQL | 1,000 / 32 | 333.191 s | 12.569 s | 12.867 s | 0.30% / 9.88% / 9.29% |

For PostgreSQL at 100 peers, the paired snapshot/row duration ratio was 9.22, with a trial range of 7.54–10.61. At 1,000 peers it was 26.05, ranging from 25.55–29.33. These are substantial improvements, but all three APIs were overloaded at the 32-peer 5 ms offered rate. At 1,000 peers, median trial response p99 was 328.15 seconds for snapshots, 10.30 seconds for rows and 10.77 seconds for cached rows. Native service time alone would hide most of this waiting.

The cached API did not improve this PostgreSQL case consistently. Its paired row/cached duration ratio at 100 peers was 0.965, ranging from 0.872–1.446. At 1,000 peers it was 0.983, ranging from 0.951–0.994: cached rows took slightly longer in all three trials. A ratio above one means the denominator completed sooner. Ratios are calculated within each trial before summarizing; they need not equal a ratio of the displayed median durations.

SQLite's 100-peer result remained around 145–157 completed callbacks per second across the arms. Independent owners did not remove its writer contention. The original five-second SQLite busy timeout also caused a storage failure under load; the follow-up used a 600-second wait budget for every arm so that waiting appeared in latency rather than ending the case early. This is a benchmark setting, not a suggested production request timeout.

## Large bursts and mixed traffic

Each largest burst contains 512 callbacks of exactly 512,000 bytes: 262.144 decimal MB. The smaller 32.768 MB and 131.072 MB bursts are included in the complete tables.

| Database | Registered / active peers | Snapshot duration | Row duration | Cached-row duration | Paired row/cached ratio, median [range] |
|---|---:|---:|---:|---:|---:|
| SQLite | 1 / 1 | 3.424 s | 3.407 s | 3.603 s | 0.953 [0.936–1.004] |
| SQLite | 100 / 32 | 4.028 s | 3.783 s | 3.496 s | 1.082 [0.979–1.139] |
| PostgreSQL | 1 / 1 | 1.326 s | 1.284 s | 1.213 s | 1.045 [1.038–1.285] |
| PostgreSQL | 100 / 32 | 2.839 s | 0.283 s | 0.279 s | 1.023 [1.014–1.042] |
| PostgreSQL | 1,000 / 32 | 13.222 s | 0.499 s | 0.447 s | 1.115 [1.104–1.131] |

At 1,000 PostgreSQL peers, the paired snapshot/row ratio for this burst was 26.96 and snapshot/cached was 30.08. Both row arms met the one-second deadline for every burst callback in all three trials. Cached rows improved throughput relative to ordinary rows by a paired median 11.5% here, compared with 2.3% at 100 peers. That benefit should not be generalized to the small-message cases above.

The heterogeneous case assigns simultaneous peers periods of 1,000, 100, 10 and 5 ms, with larger messages mixed into the faster streams. At 100 PostgreSQL peers, both row arms met every one-second deadline in all trials; snapshot deadline success had a median of 5.69%. At 1,000 peers, median deadline success was 0.80% for snapshots, 29.70% for rows and 35.13% for cached rows. Median response p99 was 125.64, 3.08 and 2.54 seconds respectively. Even the cached-row one-second cohort had a median per-trial p99 of 2.414 seconds. The per-cadence breakdowns expose delays that an aggregate throughput number would hide.

The separate regular-large case sends 65,536-byte messages at a one-second period. Every arm met all deadlines in every completed population/backend group. At 1,000 PostgreSQL peers, median trial response p99 was 32.24 ms for snapshots, 12.64 ms for rows and 12.35 ms for cached rows. Batch throughput in this case is limited by the offered schedule, so near-equal batch durations are not evidence of equal service latency.

## What the comparison measures

The experiment compares the existing full-state API, the ordinary row API, and `CachedRowServer` using durable SQLite WAL/FULL and PostgreSQL over localhost TCP. Snapshot state already stays resident in memory: its measured cost includes serializing and committing the aggregate state, without an artificial reload before each operation. Row handles use eight independent owners at the larger populations; snapshot uses one owner. Each peer remains serial. Row-versus-snapshot gains therefore include the concurrency enabled by independent peer persistence. Row-versus-cache comparisons use the same ownership topology.

The completed populations are listed above, with up to 32 active ratchets. Each case has three balanced trials. Fixed arrivals cover 1,024-byte messages every 1,000, 100, 10 and 5 ms per peer, mixed traffic with periodic 65,536-byte messages, a separate regular-large case, and simultaneous peers with heterogeneous cadences. Each periodic case offers traffic for two seconds, then drains. Bursts contain 64, 256 or 512 messages of exactly 512,000 bytes: 32.768, 131.072 and 262.144 decimal MB. These are finite load experiments, not long-running capacity or soak tests.

Response latency starts at the planned arrival, so it includes delayed production, bounded admission, owner queueing, cryptographic processing and durable database completion. A one-second deadline classifies latency; it does not cancel or retry a mutation. All offered callbacks in a successful case must drain within the finite budget, and their outputs must authenticate and match the expected plaintext and sequence. Setup, registration, client-side generation and verification are outside measured service. Payload bytes are traffic processed by the crypto API; logical state bytes and client-call counts are not physical disk/network traffic or the cost of persisting an application's entire outbox payload.

The cache avoids loading and decoding a warm peer, while still validating its exact committed state and durably committing the mutation. It installs tentative state only after confirmed commit and clears on transaction errors, including uncertain outcomes. No callback is automatically retried. The benchmark represents warm, stable peer ownership; it does not measure cache churn or competing owners of the same ratchet.

Collection excludes other coordinated VM jobs and records unavoidable physical-host noise. Three trials expose variability but do not establish statistical significance. Separate backend/population windows are not a randomized cross-backend comparison. Database-call overlap demonstrates outstanding concurrent calls, including lock waits; it does not establish simultaneous physical writes. The limited Mythic HTTP/AMQP/provider/PostgreSQL acceptance uses the existing full-state provider contract and fresh campaigns. It verifies integration behavior, not a deployed row migration or an end-to-end Mythic speedup.

The measured warm cached-row path used zero peer loads and one PostgreSQL exchange per callback; the ordinary row path used one peer load and two exchanges. Both still committed every mutation durably. The fetch reduction requires an adapter that validates `expect` at commit; the default expectation implementation can still read storage. This confirms the intended fetch reduction, while the timing results show why halving the exchange count does not imply halving latency. Cache benefits over a remote network, under eviction or with competing owners were not measured.

## Validation and collection limits

The native protocol/persistence audit completed its 1,672-candidate catalog: 1,206 caught mutations and 466 verified source compilation failures, with no misses or timeouts. The WASI audit completed 159 selected candidates: 147 caught and 12 source compilation failures, with three separately documented equivalent candidates in the full 162-entry catalog. The benchmark extension leaves the library implementation at `ad3382627df2f3fbebe1954393ad80cf7e60027c` unchanged. Existing property-based, replay, malformed-input, rollback, stale-cache, uncertain-commit and restart coverage remains applicable.

The focused benchmark validation passed 87 checks, including real PostgreSQL crash/restart and native output verification. After the SQLite-only timeout adjustment, all 70 non-PostgreSQL checks passed again, along with formatting and example Clippy checks; the 17 PostgreSQL checks retained their earlier success on unchanged PostgreSQL/common code. The additional exhaustive benchmark-harness mutation run was stopped after scope clarification. Its 60 completed outcomes out of 633 are preserved as incomplete supplementary evidence, not a passed audit. No further harness mutation work was performed.

The retained PostgreSQL 1/100-peer reports use `e26909af1d1aeb1ee48bf197b8be6c6b35ef643e`; the retained SQLite reports and final PostgreSQL report use `77d5633d6a180b9c9ca37b1ceddbaaab303c2f3b`. That change adjusts only SQLite's wait setting, its metadata test and documentation. Each paired comparison uses one binary. The initial PostgreSQL startup-marker omission, SQLite lock failure and all interference decisions remain recorded separately.

The original CPU gate rejected routine tool-service startup during both attempted 1,000-peer SQLite collections. The user then stopped that remaining SQLite configuration. Before collecting the final PostgreSQL axis, the outside-CPU limits were raised from 0.25 core per process / 0.5 aggregate to 1 / 2 cores over the monitoring interval. Lease, known-heavy-job, swap and monitor-gap checks remained. CPU and host noise are recorded, not assumed absent. The final PostgreSQL axis therefore has a different noise-admission policy from the earlier axes; all three policies and all trials are retained. Treat the within-axis paired results as the comparison, not separate collection windows as a controlled causal experiment.

The [evidence index](concurrent-row-persistence-results/2026-10-25/README.md) includes reproducible analysis and the complete per-trial tables. The [benchmark guide](row-persistence-benchmark.md) and [concurrency design](concurrent-row-persistence.md) describe the API ownership and measurement contracts. The earlier sequential results remain separate historical measurements.
