# Row versus cached-row burst profiling

The large concurrent burst is limited primarily by PostgreSQL's durable WAL flushes. Cached rows save a database fetch and some CPU work, but both APIs still wait for the same durable commit mechanism. The focused runs did not reproduce a consistent cached-row slowdown, including a follow-up that retained the preceding workloads.

This profiles the merged implementation at `40f66d60`, published with its benchmark results at `f3491c00`: 1,000 registered peers, 32 active ratchets, eight independent owners/connections, and 512 callbacks of exactly 512,000 bytes, totaling 262.144 decimal MB. Protocol code, persistence code, PostgreSQL SQL and durability settings were unchanged. Diagnostic instrumentation lives separately on `codex/row-burst-profile`; [evidence and replay instructions](row-burst-profile/2026-10-26/README.md) accompany this report.

## What explained the earlier difference

The retained benchmark already recorded each database-call interval. Across its three burst trials, mean native service rose from 7.803 ms per callback for rows to 10.465 ms for cached rows. The extra time was inside the commit call:

| Mean time per callback across the original three trials | Row | Cached row |
|---|---:|---:|
| Database load | 0.129 ms | 0 |
| Database commit | 6.784 ms | 9.606 ms |
| Native work outside database calls | 0.890 ms | 0.859 ms |

The worst cached trial averaged 15.339 ms inside commit, versus 9.026 ms for ordinary rows. Both send and receive slowed down; both APIs still reached eight simultaneous database calls. Each arm performed 512 durable mutations and sent approximately 421 KB of state values. The cache halved exchanges from 1,024 to 512. Additional cache or cryptographic computation does not explain the recorded extra service time.

## CPU and database profiles

The new experiment ran six paired bursts without sampling, four paired bursts with sampling, and two sampled pairs after the original 12 preceding workloads. Arm order alternated. All 24 target burst executions completed and verified their 512 outputs, with no conflicts, retries, failures or missed one-second deadlines. Every preceding workload also completed and verified its outputs; the overloaded periodic cases retained their normal deadline accounting.

| Collection | Median row duration | Median cached duration | Median paired row/cached duration ratio |
|---|---:|---:|---:|
| Original retained benchmark, three trials | 470.18 ms | 586.94 ms | 0.801 |
| Fresh burst, six pairs without sampling | 281.04 ms | 292.20 ms | 1.027 |
| Fresh burst, four sampled pairs | 232.02 ms | 228.22 ms | 0.993 |
| Burst after preceding workloads, two sampled pairs | 263.08 ms | 227.63 ms | 1.153 |

A paired ratio above one means caching completed sooner. Ratios are computed within trials before taking the median, so they need not equal ratios of the displayed median durations. The six unsampled pairs split wins three each, with paired ratios ranging from 0.803 to 1.224. The four fresh sampled pairs split two each. Cached rows completed sooner in both follow-up pairs, with ratios 1.221 and 1.086. These separate collections are diagnostics, not evidence of an overall speedup relative to the earlier benchmark.

Caching reduced worker CPU use. In the unsampled series, median summed worker CPU was 454 ms for rows and 427 ms for cached rows; the median paired reduction was 4.7%. The two sampled series each showed approximately 6.3% paired CPU savings. Summed CPU can exceed elapsed time because eight owners run concurrently. In the fresh captures, the last-finishing worker used approximately 52–68 ms of CPU during a 223–341 ms burst; most of its remaining time lay inside database calls.

CPU samples showed the same main work for both APIs: ChaCha20 accounted for approximately 48–49% of benchmark-process user-CPU samples, Poly1305 for 22–27%, CBOR array serialization for 11–13%, and memory copying for 5–7%. No substantial cache-specific CPU hotspot emerged. Cache hits move the cached peer into the tentative operation and avoid loading, decoding and canonicalizing its stored representation; the large-message cryptographic and framing work remains common to both paths.

PostgreSQL wait observations and syscall traces identify the dominant wait:

| Capture | Row active-backend observations waiting on WAL | Cached active-backend observations waiting on WAL | Wall interval covered by backend sync syscalls, row / cached |
|---|---:|---:|---:|
| Fresh bursts | 93.5% | 95.5% | 96.8% / 97.0% |
| After preceding workloads | 96.2% | 96.5% | 96.7% / 96.6% |

Most observations were `LWLock/WALWrite`, followed by `IO/WALSync`. PostgreSQL defines these as waiting for WAL buffers to be written and waiting for WAL to become durable, respectively. These are WAL-related waits shared across independent transactions; the traces did not identify application peer-lock contention as the bottleneck. See the [PostgreSQL 16 wait-event definitions](https://www.postgresql.org/docs/16/monitoring-stats.html#WAIT-EVENT-TABLE).

Captured stacks place the sync calls on `CommitTransaction → XLogFlush → XLogWrite → issue_xlog_fsync → fdatasync`. In the fresh captures, rows performed 559 such backend syncs for 2,048 commits, versus 537 for cached rows. Group commit was already combining transactions. Mean sync duration was 1.65 ms and 1.77 ms respectively, with occasional durations near 8 ms. The union of these syscall intervals covered approximately 97% of each burst's elapsed interval; their intervals did not overlap. That measures time inside the syscalls, including scheduling and I/O waits, rather than physical device utilization.

The ordinary row fetch cost only about 0.11 ms per callback in the new runs. The commit call cost about 2.6–3.5 ms in typical new trials, and much more in the original slow trial. Removing the fetch therefore saves useful work without reliably overcoming variation in commit latency. The original cached slowdown is best localized to commit waiting; these captures do not establish whether the earlier spike arose from host storage activity, scheduling, group-commit timing or another transient database condition.

## Method and limits

The diagnostic build retained release optimization and LTO, enabled limited debug information, and disabled symbol stripping. Small example-only changes selected the two arms, named worker threads, recorded per-thread scheduled CPU around the existing measured loop, and controlled `perf` at the measurement barriers. No probes were added inside individual cryptographic operations. CPU sampling used `cpu-clock:u` at 999 Hz with DWARF stacks because this VM did not expose hardware cycle counters. PostgreSQL wait sampling queried `pg_stat_activity` with a two-millisecond pause between queries; each query took approximately 0.2 ms on average.

Sampling excluded registration, warmup, client message generation and output verification. Analysis removes the benchmark's existing 50 ms arrival lead from each recorded window. Window bounds differ from reported batch duration by less than 0.1 ms in the fresh captures. Wait percentages count sampled active-backend observations, not elapsed time. CPU percentages count benchmark-process user-CPU samples, not whole-system CPU. Sync coverage uses interval unions, not sums of overlapping waits.

Runs used a dedicated PostgreSQL 16.15 database over localhost TCP with `fsync`, `synchronous_commit` and `full_page_writes` enabled, 128 MB shared buffers and the original queue bounds. Each collection held the full `/tmp/bc-coord` resource lease after other leases had ended and settled for 60 seconds. Physical-host Kubernetes activity remained possible; host CPU counters were recorded. Sampled runs include observer overhead and should not replace the existing uninstrumented benchmark results.

The follow-up retained the original small, mixed, regular-large, heterogeneous and smaller-burst traffic before the final burst. It omitted the snapshot arm and used two alternating row arms, so it does not reproduce every database-background timing condition of the original three-arm collection. Two follow-up pairs are evidence against a persistent cache slowdown in that context, not proof that the earlier slowdown is resolved.

The first profiler smoke run rejected a capture because the installed `perf` acknowledgement includes a terminating NUL. The control reader was corrected, a new binary was built, and the repeated smoke run verified both arms before collection. Both the rejected setup attempt and successful check are retained. No protocol or persistence fix was made in response to these profiles, and no proof changes were needed.

The next useful performance experiment would target transaction grouping or storage commit latency in the database adapter. Any batching of independent ratchets must preserve exact-state validation, atomic persistence and release of results only after confirmed durable commit. The measured CPU savings provide little reason to complicate the generic cache implementation at this point.
