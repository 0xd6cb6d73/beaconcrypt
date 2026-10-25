# Cached row persistence: SQLite and PostgreSQL results

All six configurations completed on 2026-10-25. The warm cached API eliminated the peer-fetch query as intended: the PostgreSQL adapter used one query/acknowledgement exchange per successful message instead of two. This collection does **not** demonstrate a consistent timing advantage over uncached rows on localhost. Both row APIs avoid the growing cost of full snapshots; that difference is clear at 1,000 peers.

The implementation is on `codex/row-persistence`: cached API commit `3d0da31f5edd79ddea82729a70e4bb134e1bd6d9`, benchmark commit `6a89a4c7624453c471c3f148a7a8b4e24a7ee6dd`, and clean collection revision `9f9c51d7911dae8c7b6ea4020cac38c8ad0c78bb`. The existing `RowServer` and `PersistentServer` remain available. The library contains no database driver; SQLite and PostgreSQL adapters are example/development code.

## What was measured

The experiment compared resident full snapshots, uncached rows, and fully warmed cached rows. The snapshot arm keeps the server in memory, so the comparison does not impose a full reload on every snapshot operation. Each successful message commits durably before its output can be released. The cached arm still supplies the exact predecessor bytes for atomic database validation; it does not replace the database with an in-memory authority.

Each backend ran with 1, 100, and 1,000 eligible peers, both send and receive directions, and three balanced trials. The order rotates so each API occupies each position once per case. The workloads are 1,024 messages of 1 KiB, 128 messages of 64 KiB, 1,024 mixed messages with every sixteenth message at 64 KiB, and bursts of 64, 256, and 512 identical-sized 512,000-byte messages. Those bursts total 32.768, 131.072, and 262.144 decimal MB. Every eligible peer is warmed before timing, although a shorter workload touches only a subset of a larger peer set.

The validated matrix contains 72 workload/direction/peer/backend groups, 216 paired trials, 648 arm batches, and 324,864 measured server operations carrying 47,584,641,024 plaintext bytes (approximately 44.32 GiB). Fixture creation, registration, cache filling, client cryptography, and exact-output verification are outside the measured batches. Raw per-operation timings and cold-open/cache-fill counters are retained. There is one worker and a durable commit per operation; no batching or relaxed durability is used.

## Timing results

The following tables show the 1,000-peer cases. S, R, and C mean full snapshot, uncached row, and cached row. Batch durations are medians of three batches. Ratios are **medians of matched-trial duration ratios**, followed by the observed minimum and maximum; they are not ratios of the displayed medians. A ratio above one means its denominator finished sooner. These three-trial ranges are observations, not confidence intervals.

### Rapid small messages: 1,024 × 1 KiB

| Backend | Direction | Median batch seconds S / R / C | S/C ratio [min, max] | R/C ratio [min, max] |
| --- | --- | ---: | ---: | ---: |
| sqlite | send | 14.201 / 6.673 / 6.595 | 2.154 [1.689, 2.303] | 0.962 [0.923, 1.064] |
| sqlite | receive | 14.816 / 6.373 / 6.204 | 2.461 [2.120, 2.565] | 1.059 [0.937, 1.076] |
| postgres | send | 22.922 / 1.906 / 1.898 | 11.721 [7.708, 13.000] | 1.020 [0.942, 1.040] |
| postgres | receive | 23.052 / 1.942 / 2.446 | 9.498 [7.230, 12.504] | 0.999 [0.794, 1.028] |

### Largest burst: 512 × 512,000 bytes, totaling 262.144 MB

| Backend | Direction | Median batch seconds S / R / C | S/C ratio [min, max] | R/C ratio [min, max] |
| --- | --- | ---: | ---: | ---: |
| sqlite | send | 7.915 / 3.834 / 3.498 | 2.235 [1.869, 2.264] | 1.049 [1.031, 1.096] |
| sqlite | receive | 7.342 / 3.543 / 3.960 | 1.975 [1.854, 2.091] | 1.024 [0.856, 1.092] |
| postgres | send | 11.714 / 1.471 / 1.517 | 7.809 [7.710, 9.153] | 1.044 [0.933, 1.049] |
| postgres | receive | 12.049 / 1.317 / 1.380 | 8.569 [6.242, 9.461] | 1.034 [0.873, 1.075] |

At 1,000 peers, median paired snapshot/uncached-row ratios across all workloads and directions ranged from 1.850–2.325 on SQLite and 7.243–12.437 on PostgreSQL. Snapshot/cached-row ratios in the small-message cases were 2.154–2.461 on SQLite and 9.498–11.721 on PostgreSQL. The largest bursts still benefited substantially from rows versus snapshots at that peer count.

### Cached versus uncached rows across every workload

This table shows the range of the six group medians for each workload: three peer counts times two directions. It is a descriptive range across different cases, not a pooled estimate. All individual trial ratios and latency percentiles are available in the linked full tables.

| Workload | SQLite R/C group-median range | PostgreSQL R/C group-median range |
| --- | ---: | ---: |
| 1 KiB stream | 0.956–1.063 | 0.999–1.047 |
| 64 KiB stream | 0.969–1.043 | 0.950–1.092 |
| Mixed 1/64 KiB stream | 0.938–1.067 | 1.013–1.071 |
| 32.768 MB burst | 0.954–1.049 | 0.977–1.169 |
| 131.072 MB burst | 0.897–1.193 | 0.920–1.198 |
| 262.144 MB burst | 0.977–1.049 | 0.951–1.165 |

Of the 72 groups, 52 had uncached-row/cached-row paired duration ranges spanning one; 16 had all three trials favoring caching, and four had all three favoring uncached rows. This does not support a general cache-speedup claim. The saved exchange is real, but its benefit was often smaller than the observed timing variation. All arms still serialize their changed durable state and synchronously commit. Commit latency and other work could mask a small localhost fetch saving; this is an interpretation, not a measured decomposition of the operation.

At one peer, full snapshots also sometimes finished sooner than rows. Avoiding whole-state persistence becomes more valuable as the peer set grows. The experiment establishes neither a universal API ranking nor the benefit under remote-network latency.

## Database work and correctness

Every measured uncached row operation performed one peer load and one peer store. Every warm cached operation performed zero peer loads, one exact expectation, and one peer store. Both validated one peer row and committed once. On PostgreSQL that changed two client query exchanges to one; on SQLite it changed five SQL calls to four. SQLite cached operations still read the authoritative row during commit validation. PostgreSQL performs that validation inside its database function. Neither path skips conflict detection.

For the 1,000-peer small-message batches, logical writes averaged roughly 936 KB per snapshot operation versus 818 bytes per row operation. These counters describe serialized values, not physical disk I/O, WAL traffic, or network packet bytes. Cached rows still transmit the expected old row and replacement row to PostgreSQL; eliminating the fetch response does not eliminate database validation or halve the entire transaction’s bytes.

The correctness evidence includes 435 native runtime tests, separate 128-case runs of each new property, 18 SQLite/PostgreSQL example tests, 97 Python tests, the Go race suite, two additional C bridge tests, and 28 WASI tests. Coverage includes stale and competing caches, exact receipt recovery after uncertain commit, authentication/replay rejection, rollback, registration failures, and an actual immediate PostgreSQL crash/restart. The native mutation audit accounted for 1,672 cases as 1,206 caught and 466 verified unviable; the WASI audit accounted for 159 selected cases as 147 caught and 12 unviable. There were no missed or timed-out cases. The [implementation record](cached-row-persistence.md) explains the tests and the explicitly waived proof work; archived receipts retain the initially failing PostgreSQL address-format check and its successful corrected rerun.

## Machine conditions and interpretation limits

The guest exposed 16 QEMU vCPUs and about 31.3 GiB RAM, with an ext4 virtual disk at `/dev/sda2`. CPU governor and physical-host hardware policy were not exposed. The release binary used Rust 1.96.0; SQLite was 3.53.2 and PostgreSQL was 16.15. SQLite used WAL with `synchronous=FULL`. PostgreSQL ran over loopback TCP with `fsync`, `synchronous_commit`, and `full_page_writes` enabled, 128 MiB shared buffers, and TLS disabled. Affinity allowed all 16 guest CPUs. This is a component benchmark on local durable storage, not a remote, replicated, or TLS production deployment.

The owner confirmed that the VM had no other active worker, while the physical host also ran an active Kubernetes cluster. Collection required no competing coordination leases, Lean slots, or detected heavy jobs, then reserved the full coordination budget. Five-second monitoring recorded VM activity, swap and host steal. Only the exact Codex controller identity was treated as instrumentation, with its CPU recorded separately; its children were not exempted. Host steal was recorded without rejecting ordinary physical-host noise.

The revised collection ran from 12:25:57 to 13:45:24 UTC. Its first SQLite/one-peer attempt encountered 29,458 swap-in pages over one sampling window and was discarded under the declared rule. The fresh retry and every other configuration passed. The original stricter collection was superseded before timing inspection after the owner clarified the host arrangement; all of its attempts are preserved and none contributed to these comparisons. No attempt or trial was selected for favorable timing.

Across retained invocations, the largest sampled steal rate was 0.092 CPU core, the largest outside-process aggregate rate was 0.143 core, and the exact controller reached 0.790 core in one PostgreSQL/100-peer window. One core means one CPU-second per wall second. Retained runs had small nonzero swap-in activity, with a maximum sampled rate of 23.46 pages/s, below the fixed 256-page/s veto; they were not swap-free. Samples include fixture setup and output verification. Host storage contention and short disturbances can remain invisible to these counters, and the sample distributions are not per-arm measurements.

Latency tails varied: for example, cached PostgreSQL small sends at 1,000 peers had per-trial p99 values of 4.20, 8.53, and 4.76 ms. Per-trial percentiles are kept separate rather than pooled. Three balanced trials and a quiet guest do not establish physical-host isolation or statistical significance.

The [Mythic integration review](cached-row-persistence.md#mythic-provider-compatibility) remains relevant: the provider still needs an atomic row-batch service operation and transaction-level orchestration for authorization, request receipts, native mutation, and response persistence. This benchmark omits HTTP/AMQP, CGO, provider metadata, and the application inbox/outbox or result journal. In particular, burst payloads are processed and verified, not durably journaled as application results. Additional provider reads can remain even when the peer fetch disappears. No end-to-end Mythic speedup follows from these measurements.

## Reproduction and evidence

The [benchmark guide](row-persistence-benchmark.md) documents commands and adapter contracts. The [artifact index](cached-row-persistence-results/2026-10-25/README.md) links the exact release build, source hashes, test/mutation evidence, immutable collection plans, every retained and discarded attempt, database settings, raw operation timings, and noise journals. The binary was built from implementation bytes before they were committed; those bytes were subsequently verified against the committed implementation and clean collection revision. The build receipt distinguishes the 50 committed source/manifests from two ignored Python bytecode artifacts.

Use the [preselected tables for all peer counts](cached-row-persistence-results/2026-10-25/analysis/concise-tables.md), [all 72 groups with each trial](cached-row-persistence-results/2026-10-25/analysis/full-tables.md), [wide CSV](cached-row-persistence-results/2026-10-25/analysis/all-72-groups.csv), and [noise distributions](cached-row-persistence-results/2026-10-25/analysis/noise-distributions.csv). Every paired result remains available, including cases where cached rows lost. The earlier two-arm SQLite study is preserved separately and is not combined with this three-arm experiment.
