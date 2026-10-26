# Deferred v2 analysis exporter

Prepared before inspecting any v2 timing data. Do not run until the parent authorizes analysis after all six axes finish. The script is pinned to collection plan `9bc49b4c0ac309368998e71f58c13c4e9520bf0c72c96991f5404403abe2c997` and analysis plan `4450b721243b36bd544b8da3f6c9dc0139a34706aa514e5e0c2a4a58ba42f325`. It refuses the superseded campaign and requires six retained receipts with matching report, summary, and plan hashes.

After authorization:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/bc-arc-scratch/row-persistence-20261025/hybrid/export-completed-v2.py --authorized-after-completion --collection /tmp/bc-arc-scratch/row-persistence-20261025/hybrid/collection-20261025-v2 --output /tmp/bc-arc-scratch/row-persistence-20261025/hybrid/analysis-v2
```

The output directory must be new and outside the immutable collection. The script runs no benchmarks, compilation, retries, or tests. It revalidates each report with the hash-checked committed summarizer, compares its result with the saved summary, checks the full matrix and cross-axis fixture independence, and requires exactly 72 groups, 216 paired trial rows, 648 arm batches, 324,864 operations, and 47,584,641,024 plaintext bytes. It validates warmed fixture probes and measured counters against the adapter implementation, including PostgreSQL row/cached exchanges of two/one per message and SQLite SQL call counts of five/four.

Exports include a wide CSV with all 72 groups and every trial's rates, latency percentiles, counters and paired ratios; 216-row paired-trial and 648-row arm-batch CSVs; full Markdown tables; and preselected small-stream and 512-message burst tables covering both directions, every peer count, and both backends. The concise tables use median batch durations and median paired ratios with their observed minima/maxima; the two are calculated independently. Per-trial operation percentiles are never pooled, and no significance claims are made.

Noise output records per-axis distributions and maxima of host-steal, exact-controller instrumentation CPU, unknown VM CPU, swapping rates, and CPU window duration. Overlapping CPU windows are counted but never summed. Separate cumulative steal/swap differences use the invocation's start/finish endpoints once. Those intervals include setup and verification and do not establish physical-host isolation. All guard checks must have passed. The receipt preserves exact inputs and hashes; the parent remains responsible for publication copies and narrative.

Only static AST parsing was performed when preparing this script; it has not been executed on measurement reports or synthetic timing fixtures. A counter or schema discrepancy must be investigated without timing-based selection or rerunning the experiment merely to obtain favorable results.
