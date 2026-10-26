# Durable PostgreSQL row commit batching

The large-burst profile identified durable WAL commit waiting as the dominant cost. This change adds opt-in batching to the PostgreSQL adapter example, using the existing database-independent `RowStore` contract. The library, protocol, extracted core and `no_std` support remain unchanged. Mythic and mythic-beaconcrypt are outside this implementation; their existing snapshot provider contract does not gain a production speedup from this example alone.

Each resident owner invokes its callback once and submits owned predecessor expectations and successor writes. A bounded coordinator groups independent requests, executes one PostgreSQL statement in one durable transaction, and releases results only after PostgreSQL acknowledges that transaction. Requests whose writes intersect another request's reads or writes are separated; shared reads are allowed. A stale expectation rejects only its request without writing it. A SQL error rolls back the entire batch. An ambiguous acknowledgement returns a storage error, invalidating the cached successor as required by the existing API; applications still need durable operation receipts to recover ambiguous results.

The default remains unbatched. `--backend postgres --pg-batch-size 8 --pg-batch-wait-us 2000` enables a maximum of eight requests with a 2 ms collection window. The window ends immediately when the batch is full; a lone request can incur the full delay. The default collection window is 100 microseconds, which proved too short for the large-burst measurements below; choose it explicitly for the application’s latency and concurrency requirements. The coordinator also bounds queued request count and encoded read/write bytes, flushes singleton requests without waiting indefinitely, and drains accepted work on shutdown. Its dedicated commit connection preserves `fsync=on`, `synchronous_commit=on` and `full_page_writes=on`. The SQL wrapper acquires the sorted union of advisory locks before validating any request; all writers must follow this locking protocol.

Physical transaction and network counters charge each shared commit once. Per-request read, expected-value, validation and write counters retain their logical meaning. A `row_batch_commit` span includes queueing, batch collection and the shared durable acknowledgement; overlapping spans represent outstanding callbacks, not simultaneous queries on the single coordinator connection. Payload sizes describe cryptographic traffic, not persistence of entire application outbox payloads.

Validation covers generated read/write independence, byte/count bounds, completion gating, shutdown, conflict isolation, SQL rollback, native cached-ratchet recovery and lost acknowledgements. Live tests use an isolated loopback PostgreSQL fixture with full durability; deferred commit triggers verify that cryptographic results cannot escape before the outer transaction commits. Performance validation compares the unchanged unbatched adapter with batching under the same concurrent burst workload, while keeping other repository work idle. The first full live example run passed 103 tests, excluding the existing cluster-restart test. The final focused run passed all 25 selected tests with 256 property cases and seed 130363. Existing row/cached integration suites passed all 25 tests, the nine Python summarizer tests passed, both no_std feature checks passed, and workspace all-target/all-feature Clippy passed with existing warnings. The complete mutation catalog for the changed storage code contains 81 cases: 67 caught and 14 genuine compiler-invalid mutations, with no unresolved misses or timeouts. This is not a full-library mutation rerun. No proof artifacts were changed.


## Large-burst comparison

Measurements used source `df7280ab`, Rust 1.96.0 release mode, and PostgreSQL 16.15 over localhost TCP with full durability. Each burst offered 512 callbacks of exactly 512,000 bytes, totaling 262.144 MB, across 32 active ratchets among 1,000 registered peers and eight owner workers. Every offered callback drained and its output verified. This is state persistence, not persistence of the complete application outbox payload or a Mythic end-to-end measurement.

The initial collection alternated the unbatched and eight-request configurations in order A/B/B/A/A/B, with a 100 microsecond collection window. Each entry is the median of three independent runs; the ranges show all runs.

| API | Unbatched duration | Batched duration | Commits per burst, unbatched / batched |
|---|---:|---:|---:|
| Row | 233 ms (228–251) | 332 ms (280–442) | 512 / 128 |
| Cached row | 221 ms (215–239) | 334 ms (270–413) | 512 / 128 |

Batching was slower in every paired comparison. The traces show a leading owner forming singleton commits, followed by the other seven owners; an average batch size of four consequently hid the alternating singleton/seven-request pattern. PostgreSQL already supports group commit across connections, so fewer transactions alone do not imply fewer flush waits or higher throughput. These runs did not measure physical fsync counts.

A follow-up used a 2 ms window and order A/B/B/A. It collected full eight-request batches. Each duration below is the median of two runs; the speedup ranges compare adjacent unbatched/batched runs within this follow-up, not across the two collection windows.

| API | Unbatched duration | Batched duration | Paired speedup | Commits per burst |
|---|---:|---:|---:|---:|
| Row | 328 ms (306–351) | 240 ms (232–247) | 1.24–1.51× | 512 → 64 |
| Cached row | 323 ms (306–341) | 220 ms (214–226) | 1.35–1.59× | 512 → 64 |

Row network exchanges fell from 1,024 to 576: 512 loads plus 64 shared commits. Cached-row exchanges fell from 512 to 64. Both row APIs met every one-second deadline in every retained burst. Snapshot persistence remained an unbatched control, with median burst durations of roughly 11–12 seconds.

This supports opt-in batching with an appropriate collection window for this workload. It does not establish a universal default or statistically significant speedup: the follow-up has only two pairs, and the unbatched median shifted upward by 41% for rows and 46% for cached rows between windows. The 2 ms batched durations are close to the earlier unbatched durations; comparisons must stay within each collection window. A longer window also adds latency to sparse traffic. The existing full traffic matrix was not repeated: other schedules in these focused invocations had a 1 ms offered horizon and one callback per arm, so they provide smoke coverage only.

Both collections started with no other active coordination leases, reserved the full available benchmark budget, and settled for 60 seconds. The initial collection ran from 12:14:52 to 12:22:36 UTC, and the follow-up from 12:27:42 to 12:33:26 UTC on 2026-10-26, including settlement, setup and verification. Physical-host Kubernetes activity remains an unavoidable source of noise. All ten completed invocations were retained; no timings were discarded.

The [evidence directory](postgresql-commit-batching/2026-10-26/README.md) contains raw reports, summaries, monitoring, commands, binary/source hashes and validation receipts. The PostgreSQL service and its synthetic database were removed after collection.
