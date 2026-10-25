# Durable row persistence results, 2026-10-25

The generic row API reduced native persistence batch times as stored state grew in this file-backed SQLite experiment. At 1,000 registered peers, case-level median paired snapshot-time/row-time ratios were **1.806–2.345**, and rows finished sooner in all 36 individual pairs. One peer was near parity; gains at 100 peers were modest and variable. This measures the native persistence component on one VM, with one worker and durable SQL commits. It does not establish a Mythic end-to-end speedup or concurrent throughput.

The [design and reproduction instructions](row-persistence-benchmark.md) define the baseline, workload, timing boundary, and predeclared collection rules. Both arms use resident server handles: the snapshot arm does not incur an artificial full restore per operation. The row arm loads and replaces only the selected peer. Both use SQLite WAL with `synchronous=FULL`, 4,096-byte pages, a 20,000 KiB cache target, a 1,000-page automatic checkpoint threshold, and `BEGIN IMMEDIATE`.

## Paired results

Each cell is the median of three **paired snapshot batch duration / row batch duration** ratios, followed by the observed minimum and maximum. Values above one favor rows. Bounds are rounded to three decimals; these are observed trial ranges, not confidence intervals. Ratios are computed within each trial before taking the median; dividing independently summarized throughputs can give a different result.

| Workload | Direction | 1 peer | 100 peers | 1,000 peers |
| --- | --- | ---: | ---: | ---: |
| 1 KiB stream | send | 0.978 [0.962–1.020] | 1.117 [1.072–1.175] | 2.134 [1.947–2.238] |
| 1 KiB stream | receive | 0.957 [0.892–1.108] | 1.051 [0.909–1.157] | 2.142 [2.063–2.370] |
| 64 KiB stream | send | 1.061 [0.905–1.080] | 1.055 [0.952–1.303] | 2.345 [2.258–2.556] |
| 64 KiB stream | receive | 0.960 [0.923–1.028] | 1.079 [1.000–1.150] | 2.276 [1.941–2.298] |
| Mixed stream | send | 0.949 [0.949–1.055] | 1.079 [1.028–1.158] | 2.282 [2.271–2.308] |
| Mixed stream | receive | 0.967 [0.925–1.219] | 1.051 [1.048–1.144] | 2.284 [2.132–2.446] |
| 32.768 MB burst | send | 1.010 [0.962–1.039] | 1.077 [0.898–1.125] | 2.138 [2.076–2.285] |
| 32.768 MB burst | receive | 0.968 [0.952–0.987] | 1.057 [1.038–1.189] | 2.131 [2.079–2.246] |
| 131.072 MB burst | send | 1.000 [0.939–1.055] | 0.983 [0.933–1.117] | 2.113 [1.876–2.297] |
| 131.072 MB burst | receive | 0.978 [0.963–1.018] | 1.014 [0.909–1.051] | 2.180 [1.311–2.348] |
| 262.144 MB burst | send | 1.005 [0.978–1.091] | 0.980 [0.938–1.176] | 2.005 [1.868–2.215] |
| 262.144 MB burst | receive | 1.026 [0.973–1.064] | 1.118 [1.112–1.193] | 1.806 [1.790–2.302] |

At one peer, 11 of 12 case ranges cross one; the exception is the 64-message receive burst, where rows were slightly slower in all three trials. At 100 peers, seven of 12 ranges cross one. These results support a state-size benefit without implying a universal improvement for small stores. At 1,000 peers, the 256-message receive burst still shows substantial trial variation, from 1.311 to 2.348.

Per-trial batch durations, throughput, p95/p99 latency, and logical storage counters remain available in the [1-peer](row-persistence-results/2026-10-25/persistence-peers-1-summary.md), [100-peer](row-persistence-results/2026-10-25/persistence-peers-100-summary.md), and [1,000-peer](row-persistence-results/2026-10-25/persistence-peers-1000-summary.md) summaries. Raw operation samples are archived alongside them. Latency samples are not pooled across trials.

The workload includes 1,024 consecutive 1 KiB messages, 128 consecutive 64 KiB messages, and 1,024 mixed messages with every 16th message at 64 KiB. Bursts repeat identical **512,000-byte** plaintext payloads 64, 256, and 512 times: 32.768, 131.072, and 262.144 decimal MB, respectively, or 31.25, 125, and 250 MiB. The decimal chunk size follows the reference integration. All eligible peers are used round-robin; actual peers touched per batch are `min(stored peers, message count)`. Thus, at 1,000 stored peers, the six workloads touch 1,000, 128, 1,000, 64, 256, and 512 peers respectively.

Across both arms, both directions, three trials, and all three peer counts, the retained matrix covers **108,288 measured operations and 15,861,547,008 plaintext bytes (14.772 GiB)**. Each peer-count report contains 36 paired cases and 36,096 measured operations. All outputs were verified against their exact payload, peer ID, and sequence. The 18 arm/trial fixtures have distinct lineages.

## Persistence work

These are operation-weighted average logical SQL value bytes, rounded to whole bytes across each complete peer-count report:

| Stored peers | Snapshot value bytes written/op | Row value bytes written/op | Row value bytes read/op |
| ---: | ---: | ---: | ---: |
| 1 | 1,350 | 825 | 825 |
| 100 | 94,034 | 820 | 820 |
| 1,000 | 935,828 | 818 | 818 |

The snapshot arm additionally reads a 72-byte compare-and-swap head per operation, with no full-value SQL read during the resident message path. Every measured operation in both arms uses one read, one write, and one transaction. Snapshot serialization includes the complete peer set and consumed-registration history, while row value size stays approximately constant in these ordered-message workloads. Skipped-key caches and other workloads can change row size.

These counters measure values crossing the SQL boundary. They exclude SQL keys and indexes, head writes, WAL/page amplification, fsync behavior, and filesystem effects, so they do not quantify physical I/O savings. The much larger logical-byte reduction than wall-time reduction also reflects costs common to both arms, including crypto, SQL, and durable commits; this experiment does not isolate each component's contribution.

## Provenance and quiet intervals

All retained reports measured clean commit `f0b53c634c48cb77db636b1cd01060cae075375b`, on `codex/row-persistence` based on the requested `codex/mldsa65-transcript`. The release binary was built at `31e729f22bacf438773e67c984dc81aa67029282`; intervening commits changed documentation only, and compiled source hashes matched before collection. Its SHA-256 is `750c85fa44e7015ce33fb149e24062476cf06b8a965315cf43044ffd5cb32aef`. The final results commit likewise changes documentation and evidence only.

The build used Rust 1.96.0, `cargo build --locked --release -p beaconcrypt --features gobinds --example persistence_bench`, `CARGO_BUILD_JOBS=1`, and `RUSTFLAGS='-C linker-features=-lld'`. Runtime SQLite was 3.53.2. The host exposes 16 QEMU virtual CPUs and a nonrotating QEMU virtual disk; fixture files were on ext4 `/dev/sda2`, mounted `rw,relatime`. CPU affinity included all 16 virtual CPUs. CPU governor and thermal readings were unavailable, and the underlying physical storage and hypervisor scheduling were not controlled.

The peer-count axes were independent full invocations with `--peers 1`, `--peers 100`, and `--peers 1000`, preserving every default workload and all three trials. The [artifact manifest](row-persistence-results/2026-10-25/artifacts.json), [build receipt](row-persistence-results/2026-10-25/benchmark-build.json), and [environment validation](row-persistence-results/2026-10-25/benchmark-environment-validation.json) preserve hashes, exact commands, and intervals. Original machine paths in raw receipts are provenance; the archive contains portable copies.

| Stored peers | Start UTC, 2026-10-25 | Finish UTC | Invocation seconds | Coordinator lease |
| ---: | --- | --- | ---: | --- |
| 1 | 02:54:17.009 | 02:58:27.312 | 250.302 | `00002699` |
| 100 | 05:30:13.903 | 05:34:54.753 | 280.849 | `00002741` |
| 1,000 | 05:34:54.853 | 05:43:30.512 | 515.660 | `00002741` |

After competing work ended, the coordinator reserved the full memory budget for the benchmark and required a quiet settling minute. The guard monitored the entire invocation, including fixture setup, at approximately five-second intervals. Every retained start/sample/finish record showed only the benchmark memory lease, no occupied Lean slots, no new Lean ticket, no busy ProVerif or integration lock, and no detected competing heavy process. Sampling gaps remained below 5.123 seconds. This documents coordinated quiet intervals, not perfect host isolation: the 1-, 100-, and 1,000-peer intervals recorded 12, 2,130, and 67 system-wide swapped-in pages respectively, with no swapped-out pages. Aggregate virtual CPU steal counters advanced by 29, 20, and 63 accounting ticks. These counters are not attributable specifically to the benchmark, and background activity between samples cannot be ruled out. Exact definitions and counters are in the environment validation.

The retry rule was fixed before inspecting valid timings: retain every complete uncontaminated peer-count report and discard an interrupted or contaminated report in its entirety. The first reduced attempt was discarded when Lean began. A second reservation expired without starting measurements. The third reservation completed a reduced functional check and the 1-peer report, then discarded a partial 100-peer report after a new Lean job appeared. A fourth reservation encountered interference while settling and took no measurements. The fifth completed the 100- and 1,000-peer reports. The reduced functional report is archived separately and contributes no timings to the table. Full receipts for reservations three and five preserve this history, including the later contamination after the valid 1-peer interval. No report or trial was selected for its timing.

## Interpretation limits and integration consequence

Three trials expose variation but do not support narrow confidence intervals. Alternating arm order gives a 2:1 imbalance for each case; order was not randomized. Independent invocations reset the peer-axis index and can differ in allocator, filesystem-cache, and thermal state, so paired within-report comparisons are stronger evidence than absolute cross-window scaling claims.

An explicit WAL truncation checkpoint precedes each batch outside timing. Automatic checkpoints triggered within a batch are timed, but a short row burst can defer checkpoint work beyond the timed region. These are bounded warm-batch results, not an estimate of indefinite sustained performance including every eventual checkpoint. The 64-message burst's nearest-rank p99 is its maximum, making that tail particularly noisy. Client crypto, registration, payload generation, and output verification are outside timing. Warm native open measurements include a snapshot activation commit but only identity reads for rows; they are not cold-start measurements. Retained validation buffers make process memory unsuitable for comparing server memory usage.

The reference Mythic provider already caches a native owner, which is why both arms use resident handles. Its request receipts, authorization, metadata serialization, JSON RPC, AMQP transport, and remote database are absent from this experiment. The generic composition API lets a host commit its own exact response or delivery record with a peer transition, without defining an inbox/outbox schema inside Beaconcrypt. Actual provider migration still needs an atomic row-batch storage capability and a coordinated protocol/snapshot upgrade, as described in the [integration design](row-delivery-design.md). The provider change delivered with this work fixes stored-response request-identity validation; it does not claim to enable row mode on the existing snapshot-only storage RPC.

Runtime and mutation validation are recorded in the [implementation completion guide](row-persistence.md) and the [archived validation summary](row-persistence-results/2026-10-25/row-validation-summary.json). Proof work was explicitly excluded; five existing source-fidelity checks remain failing, so an unfiltered workspace test run is not reported as passing.
