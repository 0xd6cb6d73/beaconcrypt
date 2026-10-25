Five explicit primary axes are used: PostgreSQL 1/100/1000 and SQLite 1/100. The first four are individually retained complete reports from two incomplete/stopped campaigns; only the final PostgreSQL campaign has a complete collection index. SQLite 1000 was stopped at the user's direction and is excluded. No campaign completion is fabricated and no timing-based attempt selection is performed.

Snapshot uses one serial owner and one database connection. Row and cached-row use stable peer lanes with independent owners/connections and equal total queue bounds. Snapshot/row ratios include this ownership difference; row/cached-row comparisons share the owner topology.

All offered requests drain successfully. Planned-arrival response time includes scheduler backlog, blocked admission, owner-queue wait, dispatch, native API service, and completion overhead. No automatic retries or discarded overload are accepted.

Periodic work is paced. Its full-batch completion rate can be arrival-limited; use deadlines, response latency and backlog to assess it rather than calling a near-equal batch duration equal capacity. Burst MB/s uses all offered plaintext bytes and full drain time.

All percentiles are computed within one trial. A response-p95 ratio divides the two arms' per-trial p95 values; it is not a p95 of per-callback ratios. Across-trial aggregates summarize trial statistics or within-trial paired ratios; they never pool request latencies across trials. Ratios whose denominator is zero are null with explicit counts, not silently replaced.

source_backlog_ns is computed per callback as scheduler_lag_ns + enqueue_backpressure_ns before taking percentiles. Percentiles of stages cannot be added to obtain a response percentile.

queue_wait_ns includes waiting for the serial owner. owner_wait_ns is dequeue-to-native dispatch overhead, not a separate contended owner mutex. Native API service includes database work; database client spans and overlap are not pure crypto or physical database CPU/write concurrency.

Overlapping interval durations are reported as unions by the validated summarizer, never added as wall time. Logical SQL counters and plaintext bytes are not physical I/O. No significance, cross-window causal comparison, or Mythic end-to-end speedup is inferred.

Old PostgreSQL 1/100 use source e26909a; SQLite 1/100 and PostgreSQL 1000 use 77d5633d. The change raises only SQLite busy waiting from 5 to 600 seconds, with its settings test/documentation. PostgreSQL and common/library implementation are unchanged. Preserve both builds and separate collection windows.

The final PostgreSQL 1000 window permits outside VM CPU below 1 core per process and 2 cores aggregate; earlier retained windows used 0.25 and 0.5. Host steal remains recorded only. These policy differences preclude claiming a controlled cross-window scaling experiment or an isolated physical host.

analysis.json contains min/median/max summaries of matched trial ratios and trial statistics. arm-trials.csv contains each arm/trial's stages, deadlines, workload, drain, counters and overlap. paired-trial-ratios.csv preserves every ratio operand and paired-ratio-summary.csv summarizes those matched ratios; cohort-trials.csv includes marginal and joint period/flow/payload groups, which overlap and must not be summed across cohort kinds. tables.md shows per-trial values without pooling. input-receipt.json binds all retained inputs, the plan, summarizer and this exporter.
