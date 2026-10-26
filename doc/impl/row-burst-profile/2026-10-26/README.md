# Row burst profiling evidence

The [profile report](../../row-burst-profile.md) explains the result. Library and SQL behavior match merge source `40f66d60`; the diagnostic branch starts from `f3491c00`. Fresh baseline and sampled runs used diagnostic commit `b2c2845a30c3411aa9e060593c94db9db9b2bdb4`, binary SHA256 `c4dbf6515b30bd1d52d3b4177aab97e7b50d143d38f9b556f3ffa2cfe3de7c73`. The workload-history follow-up used `a98489c67a300922ed00e59279a9b21dfa0c70a1`, binary SHA256 `afedf83031414f7655a9f7c0b92528ab3777936878316c163bce75ae767306be`.

`diagnostic.patch` and `diagnostic-history.patch` show the complete changes relative to `f3491c00`. They affect only the example and its libc development dependency. Build receipts pin the sources, compiler, options and binaries. The instrumentation is kept on `codex/row-burst-profile`; it is not part of the merge branch's library or benchmark implementation.

Read [per-trial values](analysis/trials.csv), [fresh capture analysis](analysis/profile-sampled.json) and [history capture analysis](analysis/profile-history.json). The analysis contains the original three pairs, six new pairs without sampling, four fresh sampled pairs and two sampled pairs with preceding workloads. CPU time is summed across workers. Per-arm medians and medians of paired ratios are distinct statistics.

`captures.tar.gz` contains the original selected burst records plus each new collection's raw report, command, completion receipt, marker log and observer data. Sampled collections also include symbolized CPU/syscall traces and PostgreSQL stacks. `capture-manifest.json` records each archived input's length and SHA256. Raw system-wide `perf.data` files and unstripped binaries remain in `/tmp/bc-arc-scratch/row-burst-profile-20261026`; stack-memory records, database files and build output are not included in this publication.

`validation.tar.gz` contains the run/build/analysis helpers, build logs, source pins, PostgreSQL logs, resource-lease logs, settling observations and smoke-check records. The first smoke capture failed on the profiler acknowledgement format; the corrected capture passed before the main runs. All 24 target burst executions verified all outputs. The two full-history trials also verified every preceding callback, for 192,960 completed callbacks across the new collections in total.

To verify publication files, run `sha256sum -c SHA256SUMS` in this directory. To replay the numerical analysis with Python 3.11 or newer:

```bash
mkdir replay
tar -xzf captures.tar.gz -C replay
cp analyze-profile.py replay/
python3 replay/analyze-profile.py sampled
python3 replay/analyze-profile.py history
```

Outputs appear in `replay/analysis/`. Replay uses the extracted burst-only subset of the history report, so it does not need to load the full 231 MB history report. The helper pairs syscall entry/exit events by thread and classifies samples by marker windows and owned backend PIDs. It subtracts the existing 50 ms scheduling lead; no samples are selected on favorable timing. The published symbolized traces suffice to reproduce the tables without rerunning PostgreSQL or invoking `perf`.

For a new capture, use the pinned diagnostic commit, release options in the build receipt, the exact arguments in each collection's `command.json`, and the runner in `validation.tar.gz`. `BC_PROFILE_HISTORY=1` restores the preceding workload sequence. The runner's scratch and worktree paths describe this collection and should be adjusted for another workspace. The original standalone benchmark remains unchanged on the merge branch.
