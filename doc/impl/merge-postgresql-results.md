# PostgreSQL persistence results on the merge branch

The concurrent PostgreSQL comparison completed on `codex/core-row-merge` at `40f66d60d268a7153043b90f483899ba00515641`. Row persistence retains its substantial advantage over full-state persistence at larger peer populations. Cached rows remove a database fetch, but did not consistently improve elapsed time over ordinary rows in this collection.

All 1, 100 and 1,000 registered-peer configurations completed on their first attempt. The collection contains 39 workload/population groups, three balanced trials of each of the three APIs, 351 arm/trial records, 840,960 completed callbacks and 14,108,239,872 plaintext bytes. The [evidence directory](merge-postgresql-results/2026-10-26/README.md) includes raw observations, monitoring journals, validation and reproducible analysis. SQLite benchmarks were not rerun.

## High-frequency traffic

This case offers one 1,024-byte callback every 5 ms per active peer for two seconds, then drains all queued work. The larger populations have 32 active ratchets, offering 12,800 callbacks per arm at 6,400 callbacks per second. Each value below is the median of three trial statistics. Deadline success uses a one-second response deadline from the planned arrival.

| Registered / active peers | Snapshot duration | Row duration | Cached-row duration | Deadline success: snapshot / row / cached |
|---|---:|---:|---:|---:|
| 1 / 1 | 1.998 s | 1.998 s | 2.000 s | 100% / 100% / 100% |
| 100 / 32 | 56.238 s | 6.043 s | 6.196 s | 1.77% / 31.66% / 24.16% |
| 1,000 / 32 | 323.302 s | 12.365 s | 12.070 s | 0.32% / 8.38% / 9.33% |

The median paired snapshot/row duration ratio was 9.31 at 100 peers, with a trial range of 8.24–9.61, and 25.79 at 1,000 peers, ranging from 23.15–26.15. All three APIs were overloaded at this offered rate with 32 active peers. At 1,000 registered peers, median trial response p99 was 318.40 seconds for snapshots, 10.24 seconds for rows and 9.97 seconds for cached rows.

The median paired row/cached duration ratio was 1.086 at 100 peers, ranging from 0.870–1.109, and 1.015 at 1,000 peers, ranging from 0.812–1.166. A ratio above one means cached rows completed sooner. These ratios are calculated within trials before taking their median, so they need not equal the ratio of the displayed median durations. The single-peer batch durations are limited by the arrival schedule; their similarity does not establish equal latency or capacity.

## Large bursts and mixed traffic

The largest burst contains 512 callbacks of exactly 512,000 bytes, totaling 262.144 decimal MB. The table reports median trial duration and plaintext throughput over the complete drain.

| Registered / active peers | Snapshot duration | Row duration | Cached-row duration | Throughput MB/s: snapshot / row / cached |
|---|---:|---:|---:|---:|
| 1 / 1 | 1.515 s | 1.313 s | 1.739 s | 173.07 / 199.67 / 150.72 |
| 100 / 32 | 2.504 s | 0.249 s | 0.234 s | 104.68 / 1,054.35 / 1,122.14 |
| 1,000 / 32 | 13.263 s | 0.470 s | 0.587 s | 19.77 / 557.55 / 446.63 |

At 1,000 peers, the median paired row/cached duration ratio was 0.801, ranging from 0.624–0.984: cached rows took longer in all three trials of this burst. Ordinary rows met every one-second deadline in all three trials; cached rows missed 47 of 512 deadlines in one trial and met all deadlines in the other two. A median deadline-success figure of 100% would hide that failure to meet the latency target. All callbacks nevertheless completed successfully.

The heterogeneous case runs peers with simultaneous periods of 1,000, 100, 10 and 5 ms, mixing larger payloads into the faster streams. At 100 registered peers, ordinary rows met every deadline in all three trials. Cached rows met all deadlines in two trials, but only 68.47% in the third. At 1,000 peers, median deadline success was 0.84% for snapshots, 32.11% for rows and 27.43% for cached rows; median trial response p99 was 121.90, 3.31 and 3.31 seconds respectively.

The separate regular-large case sends 65,536-byte messages every second. All arms met every deadline at every population. At 1,000 peers, median trial response p99 was 33.73 ms for snapshots, 16.36 ms for rows and 16.89 ms for cached rows. These periodic workloads are arrival-limited at light load. The single-peer regular-large and heterogeneous cases contain only two callbacks per trial, so their tail statistics have little descriptive power.

## Method and interpretation

The existing benchmark was built in release mode with Rust 1.96.0 and run against a dedicated PostgreSQL 16.15 instance over localhost TCP. `fsync`, `synchronous_commit` and `full_page_writes` were enabled. The measured binary SHA256 is `774b1a86945b4a865d842659faf0f046d3cce3a011a005a3397eaadd4d76f20e`. The source receipt covers the merged adapter, core, parser and crypto sources. This run changes neither the library nor the benchmark implementation.

Snapshot state already remains resident in memory; its measured work includes serializing and durably committing the aggregate state. It uses one serial owner and database connection. Row and cached-row use up to eight independent owners/connections, with stable peer assignment and serial mutation of each ratchet. All arms have the same total queue limits of 256 jobs and 16 MiB. Snapshot/row comparisons therefore include the concurrency enabled by independent peer persistence. Row/cached-row comparisons share the same owner topology.

The 13 workloads per population cover 1,024-byte messages at 1,000, 100, 10 and 5 ms periods; corresponding mixed cases with periodic 65,536-byte messages; regular large messages; heterogeneous cadences; and bursts of 64, 256 and 512 messages of exactly 512,000 bytes. Periodic cases offer traffic for two seconds before draining. The bursts total 32.768, 131.072 and 262.144 decimal MB. These are finite load experiments rather than sustained capacity or soak tests.

Response latency begins at the planned arrival and includes scheduler delay, blocked admission, owner queueing, cryptographic processing and durable database completion. Deadlines classify latency without cancelling callbacks. Every offered callback must drain and its output must authenticate and match the expected plaintext and sequence; there are no automatic mutation retries. Setup, registration, client-side message generation and output verification are outside measured service. Payload throughput measures traffic processed by the crypto API, not durable storage of an application's entire outbox payload.

Observed database client calls overlapped up to eight at the larger populations for both row arms. This demonstrates outstanding concurrent calls, including time waiting on database locks; it does not establish simultaneous physical writes. Warm cached rows used zero peer loads and one PostgreSQL exchange per callback, versus one peer load and two exchanges for ordinary rows. Durable commit and exact-state validation remain necessary. The experiment does not measure cache churn, competing owners of the same ratchet or a remote network's latency.

Each population waited for 180 seconds with no other active resource leases, then reserved the full benchmark budget and settled for 60 seconds. The predeclared CPU limits were one core per outside process and two aggregate outside cores, matching the final previous PostgreSQL collection; lease, known-heavy-job, swap and monitor-gap gates remained active. All three first attempts were retained without a quiet-window rejection. Measurement ran from 08:05 to 09:41 UTC on 2026-10-26. The physical host's Kubernetes activity remains a source of noise, and host steal was recorded rather than assumed absent.

Three trials expose variability but do not establish statistical significance. The earlier pre-merge collection occurred in a separate window; differences from it cannot be attributed to the crypto backend or merge alone. This collection supports a strong row-versus-snapshot advantage under concurrent load and confirms the cached API's fetch reduction, but provides no consistent additional timing advantage for caching. It is not a Mythic end-to-end throughput measurement.

## Validation

Before collection, `cargo test -p beaconcrypt --example persistence_bench --locked -- --include-ignored --test-threads=1` passed all 87 tests against the owned PostgreSQL instance, including commit conflicts, lost acknowledgements, concurrent operations and crash/restart. Each retained report then passed the existing summarizer and collection validation. An independent review reproduced all 1,053 paired-ratio summaries and checked the counts and source/binary pins. All 64 files in the compressed evidence were verified byte-for-byte against their archive manifest.

The [merge validation record](core-row-merge.md) covers the broader implementation checks. No additional implementation, proof changes or harness mutation work was needed for this benchmark run. The temporary PostgreSQL service was stopped after collection and its synthetic database was removed after the evidence was archived.

The subsequent [row versus cached-row burst profile](row-burst-profile.md) localizes the large-burst waiting to PostgreSQL WAL flushes and measures the cache's CPU savings. Its diagnostic collections remain separate from the results above.
