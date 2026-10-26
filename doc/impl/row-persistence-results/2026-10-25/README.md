# Archived row persistence evidence

The [results report](../../row-persistence-results.md) interprets this collection. All three full peer-count reports measured clean revision `f0b53c634c48cb77db636b1cd01060cae075375b` with the same release binary. This archive contains no fixture database or deployed identity. Raw reports preserve original absolute paths as provenance; use the files here after moving the worktree.

## Benchmark data

| Registered peers | Compressed raw report | Per-trial summary |
| ---: | --- | --- |
| 1 | [JSON](persistence-peers-1.json.gz) | [Markdown](persistence-peers-1-summary.md), [JSON](persistence-peers-1-summary.json.gz) |
| 100 | [JSON](persistence-peers-100.json.gz) | [Markdown](persistence-peers-100-summary.md), [JSON](persistence-peers-100-summary.json.gz) |
| 1,000 | [JSON](persistence-peers-1000.json.gz) | [Markdown](persistence-peers-1000-summary.md), [JSON](persistence-peers-1000-summary.json.gz) |

The [reduced functional report](persistence-reduced.json.gz) and its [summary](persistence-reduced-summary.md) validate a smaller workload; their timings are excluded from the full comparison. Raw reports include every operation latency, configuration, actual command line, fixture lineage, batch duration, SQL counter, and verification result. The per-axis logs record process progress.

[artifacts.json](artifacts.json) records exact compressed-file and uncompressed-content hashes. [benchmark-build.json](benchmark-build.json) records source hashes, binary hash, build toolchain and flags, affinity, filesystem, and device information. [benchmark-final-build.log](benchmark-final-build.log) records compilation and harness checks, including existing Clippy warnings.

## Quiet-window records

[benchmark-retained.json](benchmark-retained.json) identifies each retained invocation's exact interval and raw-report hash. [benchmark-environment-validation.json](benchmark-environment-validation.json) reconciles the three full reports with the monitor records, including observation counts, maximum gaps, sole-lease checks, Lean ticket checks, system-wide swap counters, and CPU accounting deltas. It states the limits of those checks.

[Window 3](quiet-window-3.jsonl.gz) contains a valid reduced run and valid 1-peer run followed by a contaminated, discarded 100-peer attempt. Only the manifest's retained intervals are used. [Window 5](quiet-window-5.jsonl.gz) contains the valid 100- and 1,000-peer runs. The [window 3 log](quiet-window-3.log) and [window 5 log](quiet-window-5.log) preserve the sequence. The [archived window 5 guard](quiet-window-5-guard.py.txt) is historical monitoring code tied to the shared machine's coordinator; it is evidence, not a portable benchmark runner.

The failed attempts described in the results report contribute no measurements. Complete receipts retain the later interference rather than trimming it away. The watcher can detect recognized processes, resource occupancy, and new Lean tickets; it cannot prove complete absence of activity between samples or outside the guest VM.

## Runtime and mutation validation

[row-validation-summary.json](row-validation-summary.json) records native, binding, WASI, and harness validation. [native-catalog-reconciliation.json](native-catalog-reconciliation.json) gives the corrected current mutation accounting: 1,640 distinct cases, 1,188 caught and 452 unviable, with none missed, timed out, or uncovered. The [current catalog](native-complete-catalog.json.gz) and [merged final outcomes](native-current-outcomes.json.gz) allow comparison by exact mutant name. The earlier 1,726 figure counted 86 obsolete historical entries; the corrected union combines two fresh final runs with eight identical overlapping caught cases. Proof source-fidelity checks were explicitly excluded, as detailed in the [completion guide](../../row-persistence.md).

## Recompute without rerunning measurements

From the repository root, decompress a report into a new temporary directory and run the standard-library-only validator and summarizer:

```bash
report_dir=$(mktemp -d)
gzip -dc doc/impl/row-persistence-results/2026-10-25/persistence-peers-1000.json.gz > "$report_dir/persistence-peers-1000.json"
python3 beaconcrypt/examples/persistence_bench/summarize.py "$report_dir/persistence-peers-1000.json"
```

The regenerated summary's input path will differ from the archived machine path; its input hash and numerical results should match. Fresh measurements require their own quiet reservation and provenance, following the [benchmark design](../../row-persistence-benchmark.md).
