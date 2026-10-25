# Durable persistence component benchmark

The `persistence_bench` Rust example compares a resident `PersistentServer` backed by a full SQLite snapshot with a resident `RowServer` backed by SQLite rows. Both arms run the same Beaconcrypt revision and cryptography, preserve ratchet state durably before releasing output, and use the same database settings. The experiment measures the cost of the native persistence boundary. It does not measure the Mythic provider, its transport, or its application result journal.

The [2026-10-25 results](row-persistence-results.md) archive the completed shared-host collection, raw reports, and measurement limits. No performance result follows from this design alone. Keep the generated JSON and the exact build and run commands with any reported measurements. Do not start this benchmark, including a reduced smoke measurement, on the shared development machine until the orchestrator confirms that all other `/tmp/bc-coord` leases have ended and a quiet measurement window is available. Compilation and correctness testing must finish before that window.

## Reference integration and choice of baseline

The workload reference is [mythic-beaconcrypt at `200af54bd8500d6d619b98d952fd4851e540ce10`](https://github.com/0xd6cb6d73/mythic-beaconcrypt/tree/200af54bd8500d6d619b98d952fd4851e540ce10). That revision is evidence about the integration's work and workload shape, not a claim that its pinned native library has the same wire protocol as this branch.

The provider caches its native owner after activation: [`owner.go`](https://github.com/0xd6cb6d73/mythic-beaconcrypt/blob/200af54bd8500d6d619b98d952fd4851e540ce10/Payload_Type/mythic_beaconcrypt/internal/engine/owner.go#L147) returns when the native handle already exists. Its normal request path still loads the current stored owner record, checks prior immutable results, exports a complete native checkpoint after a native mutation, serializes provider metadata including request history, and commits the checkpoint, metadata, and result together. See [`engine.go`](https://github.com/0xd6cb6d73/mythic-beaconcrypt/blob/200af54bd8500d6d619b98d952fd4851e540ce10/Payload_Type/mythic_beaconcrypt/internal/engine/engine.go#L37) and its [commit path](https://github.com/0xd6cb6d73/mythic-beaconcrypt/blob/200af54bd8500d6d619b98d952fd4851e540ce10/Payload_Type/mythic_beaconcrypt/internal/engine/engine.go#L427). The engine's campaign mutex serializes that path. Storage travels through [JSON RPC over AMQP](https://github.com/0xd6cb6d73/mythic-beaconcrypt/blob/200af54bd8500d6d619b98d952fd4851e540ce10/Payload_Type/mythic_beaconcrypt/internal/storage/client.go), including binary values represented in JSON.

The appropriate primary native baseline is therefore a resident `PersistentServer`, not an artificial full restore before every message. The benchmark's snapshot adapter selects only the current 72-byte lineage/generation/digest head during its atomic compare-and-swap. It validates the replacement envelope and replaces the complete snapshot. The resident API still serializes all peers and consumed registrations, sorts those collections, and hashes the resulting full snapshot on every successful message operation. The benchmark does not add an avoidable full-value database read to that path.

The row arm loads, validates, mutates, serializes, and replaces the selected peer row in a serializable transaction. Immutable identity is loaded at open. Registration replay markers and the key allocator remain separate rows. The two arms use equal peer counts, equal consumed-registration counts, equal identity seed inputs, equal messages, and independent freshly registered beacons. Every fixture receives a fresh random 32-byte lineage outside message timing, recorded with its fixture metadata and reused only to reopen that fixture's authoritative database. Random lineages, peer keys, and handshake randomness are independently generated; their byte values are not deterministic fixtures.

Neither measured arm stores an application request/result journal. The comparison consequently establishes neither retry-result recovery equivalence with the reference provider nor a provider-wide speedup. A provider migration must also preserve immutable request results, request-body identity checks, campaign/session metadata, owner fencing, and atomic result/state commitment. Those costs require a separate application-level experiment once the integration implements them. A reload-per-operation deployment, if relevant, is a separate baseline and must be labeled as such.

## Workload matrix

Defaults use 1, 100, and 1,000 registered peers, three independent paired trials, and every registered peer active in round-robin order. Each trial warms both directions with 16 messages and then measures the following cases independently for server send and server receive:

| Case | Messages | Plaintext size per message | Plaintext volume per arm and direction |
| --- | ---: | ---: | ---: |
| Small stream | 1,024 | 1,024 bytes | 1 MiB |
| Larger stream | 128 | 65,536 bytes | 8 MiB |
| Mixed stream | 1,024 | 1,024 bytes, with every 16th message 65,536 bytes | 4.9375 MiB |
| Burst 64 | 64 | 512,000 bytes | 32.768 MB / 31.25 MiB |
| Burst 256 | 256 | 512,000 bytes | 131.072 MB / 125 MiB |
| Burst 512 | 512 | 512,000 bytes | 262.144 MB / 250 MiB |

The reference's [installed Poseidon tests](https://github.com/0xd6cb6d73/mythic-beaconcrypt/blob/200af54bd8500d6d619b98d952fd4851e540ce10/integration/poseidon/installed/README.md#L214) exercise 1 KiB, 64 KiB, 1 MiB, and 10 MiB values. Its [chunking description](https://github.com/0xd6cb6d73/mythic-beaconcrypt/blob/200af54bd8500d6d619b98d952fd4851e540ce10/integration/poseidon/installed/README.md#L270) gives **512,000 decimal bytes**, rather than 512 KiB, as the usual output chunk size. Actual JSON, base64, delegation, and batching can produce larger wire messages; this benchmark deliberately measures exact native plaintext sizes and records actual encoded wire byte counts separately.

The burst repeats the exact same immutable payload bytes for every message and both arms. Small and large payloads also repeat within their classes. All payloads are generated once before timing using the documented SplitMix64 byte generator with seeds 1, 2, and 3 for the small, large, and burst classes. This is reproducible test data, not cryptographic randomness; the protocol uses its normal randomness and sequence-dependent ciphertext. No compression or deduplication layer is present.

`--extra-registrations N` adds N accepted registrations whose response fails because the explicitly supplied response plaintext is empty. Their consumed replay markers persist without creating peers, allowing registration-history growth to be varied independently of peer count. `--active-peers N` restricts the eligible round-robin working set to `min(N, registered_peers)` while retaining the other peer records. The result's `active_peers` records that eligible limit; `touched_peers` records `min(active_peers, messages)`, because a short batch may not reach every eligible peer. These are useful separate axes: for example, one active peer among 1,000 total peers, or 100 peers with 5,000 additional replay markers. The benchmark's registration history is not the provider's application request journal.

Cases run without intentional sleeps or rate limiting. The small and larger streams are saturated single-worker workloads, with the latter using regularly sized larger messages. The bursts are consecutive native operations, not transport batching. This measures service capacity under continuous demand; it does not measure latency at a chosen arrival rate, queueing, or many-worker throughput. A paced or concurrent experiment should be reported separately. SQLite's writer serialization does not demonstrate parallel throughput across independent peers even though the row API allows a different database to provide it.

The default matrix moves approximately 14.8 GiB of plaintext across the measured API calls, before client verification and wire overhead; full-snapshot persistence can write substantially more. Use a reduced matrix to check the harness during an approved quiet window, then run the intended matrix with sufficient time and disk space. Do not combine reduced and default runs into one summary.

For the shared-host collection, the peer-count axes are run as three independent complete reports with `--peers 1`, `--peers 100`, and `--peers 1000`, retaining three trials and every default workload in each report. This preserves the total workload while allowing completed clean reports to survive an interruption during a later axis. The retry rule is fixed before collecting valid timings: monitor the entire invocation, retain every completed uncontaminated report, and discard and rerun any interrupted or contaminated axis from fresh fixtures. Do not select reports or trials by their timings. Record each axis's window separately and compare paired arms within that report. Independent invocations reset the peer-axis index, so all three axes use the same alternating first-arm schedule, with a 2:1 imbalance over three trials rather than exact balance or randomization. Differences in allocator state, temperature, and filesystem cache between windows further limit absolute cross-axis scaling comparisons.

## Persistence and timing boundaries

Both SQLite adapters use file-backed databases with `journal_mode=WAL`, `synchronous=FULL`, 4,096-byte pages, a 20,000 KiB page-cache target, a 1,000-page automatic WAL checkpoint threshold, and a five-second busy timeout. Both begin writes with `BEGIN IMMEDIATE`, use one connection per resident server, and commit once per ordinary message operation. The row table uses its binary key as its primary key with `WITHOUT ROWID`; the snapshot table has a single integer primary key plus separate trusted head columns. Database errors abort the experiment instead of being counted as successful operations or silently retried.

Before each batch, an explicit WAL `TRUNCATE` checkpoint completes outside the timer, and storage footprints are sampled. Automatic checkpoints caused by the subsequent batch remain inside the timer. The initial checkpoint makes the WAL starting condition comparable; it does not make the filesystem cache cold. Snapshot and row database contents are warm after setup and preceding cases. The measured workloads retain state across cases in the same trial, with equivalent operation sequences in both arms; a new pair of databases is created for the next trial.

Fixture creation, registration, additional replay-history creation, native reopen, warmup, and deterministic payload generation are outside message timing. For receives, all beacon ciphertext is generated before the server batch. For sends, beacons decrypt and check all returned ciphertext after the batch. Every output is checked against its exact payload, peer key ID, and expected sequence number. A failed operation or verification fails the run.

Each operation latency includes the native method, its SQL transaction, commit acknowledgement, and construction of its returned result. The batch timer additionally includes loop bookkeeping, two clock reads per operation, and insertion into preallocated measurement/result vectors. It excludes client crypto, registration, payload construction, verification, SQL footprint scans, reporting, and preparation checkpoints. Throughput is computed from the entire server batch duration; it is not the reciprocal of a latency percentile. Individual latency percentiles use the nearest-rank definition and are reported separately.

The two arms execute consecutively for each case. Initial fixture order alternates by trial and peer-count axis; case/direction order also alternates the first arm, preserving trial-to-trial alternation. Reports record the actual `pair_order`. The same fixed case order is used for both arms. Raw results are written after the complete paired trial, avoiding report-file writes between the paired measurements. No concurrent workload generator runs during the timed region.

The harness retains frames and results so validation can occur outside timing. A receive burst can retain both ciphertext and plaintext buffers, and both initialized arm fixtures coexist. Its process memory is therefore not a server-memory comparison. The report's environment memory readings are context only, not peak-resident-memory measurements attributable to an arm.

Native open time is reported separately after closing and reopening the initialized server. Connection establishment and PRAGMA setup are excluded. The database and OS cache are warm. Snapshot restoration performs its activation write; row open reads identity without an activation write. Label this field `warm_database_open_ns`, not cold-start latency.

## Running and interpreting the report

Build the example from a clean, recorded revision before the measurement window:

```bash
cargo build --release -p beaconcrypt --example persistence_bench
```

After the shared-machine coordinator has confirmed that no other leases or background builds remain, run the release binary directly. Choose a persistent database filesystem representative of the deployment, not a memory-backed temporary directory:

```bash
target/release/examples/persistence_bench --run \
  --output persistence-default.json \
  --database-directory /path/to/persistent/benchmark-space
```

The default database parent is the invocation's current working directory. Temporary fixture databases are removed when the process exits normally; the JSON report remains. The program refuses an existing output file and refuses detected Linux `tmpfs` or `ramfs` database locations. Filesystem detection is best-effort on other platforms. These benchmark identity seeds are fixed, publicly visible fixtures and must never be used as a deployed identity; each fixture owns a fresh independent database lineage.

For a reduced functional measurement, still subject to the same quiet-window requirement:

```bash
target/release/examples/persistence_bench --run \
  --output persistence-reduced.json --peers 1,10 --trials 2 \
  --small-messages 32 --large-messages 8 --mixed-messages 32 \
  --burst-chunks 4 --warmup-messages 4 \
  --database-directory /path/to/persistent/benchmark-space
```

For the history/working-set axis, retain the ordinary default payload sizes and change only the specified variables:

```bash
target/release/examples/persistence_bench --run \
  --output persistence-history.json --peers 100 --trials 3 \
  --active-peers 1 --extra-registrations 5000 \
  --database-directory /path/to/persistent/benchmark-space
```

The JSON records configuration, source revision and dirty state, executable and command line, Rust version found on `PATH`, runtime Rust flags, SQLite version, OS/CPU/memory information where available, CPU governor where available, filesystem type, raw per-operation nanoseconds, batch durations, observed wire/plaintext byte counts, SQL operation counts, logical value bytes, and database footprints. Source status is captured before creating the report and temporary databases, so those generated artifacts do not make a previously clean checkout appear dirty. The Rust version and flags reflect the run environment and do not prove which toolchain or flags built the binary; archive the build command and build log as well. Debug builds are rejected.

The adapter's `value_bytes_read` and `value_bytes_written` count opaque persisted values crossing its SQL boundary. Snapshot compare-and-swap head reads are separate `head_bytes_read` counters. Those counters omit index entries, SQL keys, head writes, WAL/page amplification, fsync calls, and filesystem behavior. Main-database and WAL lengths are instantaneous allocated footprints, not cumulative disk bytes written. Do not describe either metric as physical I/O savings. Row counts include identity, allocator, replay markers, and peer rows; the snapshot arm stores one row containing the aggregate state.

Compare pairs with the same peer count, trial, scenario, direction, active-peer count, and history count. Report per-trial batch durations and throughput, then summarize the distribution of paired ratios or differences. Keep tail latencies per case and trial visible; pooling every message across trials hides run-level variation and is not a substitute for repeatability. Three trials are a practical default, not sufficient evidence for a narrow confidence interval. A difference near the observed run-to-run spread is inconclusive.

The standard-library-only `summarize.py` validates the complete configured matrix, rejects missing or duplicate arms and mismatched workload axes, checks latency summaries against raw samples, and recomputes throughput from positive batch durations. It emits each trial's durations, throughput, p95/p99 latencies, logical storage bytes, and the median/range of the paired snapshot-time/row-time ratios. Ratios above one mean the row batch finished sooner in that pair; they are not an end-to-end provider performance claim. Configuration axes must be unique, and reports with `running` or `failed` status are rejected. JSON output additionally preserves all per-trial latency summary fields and SQL counters.

```bash
python3 beaconcrypt/examples/persistence_bench/summarize.py persistence-default.json \
  --output persistence-default-summary.md
python3 beaconcrypt/examples/persistence_bench/summarize.py persistence-default.json \
  --format json --output persistence-default-summary.json
```

The summarizer refuses to overwrite an output file. Its schema and failure-path tests use synthetic in-memory values only and do not execute or publish any benchmark measurement:

```bash
python3 -m unittest discover -s beaconcrypt/examples/persistence_bench -p test_summarize.py
```

Before publishing results, record storage hardware and mount options, power/CPU policy, CPU affinity if used, free space, thermal state, and whether swapping or competing processes were observed. Keep those choices identical between arms. Do not change host cache policy, drop OS caches, disable durability, or tune one arm after inspecting its timings without defining a new experiment. A file-backed SQLite `FULL` commit measures the guarantees exposed by the local filesystem and hardware; it does not represent network database latency, replicated durability, AMQP latency, or the reference provider's complete recovery contract.
