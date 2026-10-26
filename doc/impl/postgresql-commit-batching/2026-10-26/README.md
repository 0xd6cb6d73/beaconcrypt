# PostgreSQL batching evidence

The source is `df7280ab` on `codex/pg-batching`. The measured release binary SHA256 is `6b34b4aeb6d1ee6e6428ff5eb36d7b0d6c51ed1b8f4075a036cd09c85dc829de`.

`bench/` contains the three-pair 100 microsecond collection; `bench-2ms/` contains the two-pair 2 ms follow-up. Each directory preserves compressed raw reports, validated summaries, the comparison, invocation logs and `vmstat` observations. The compressed runner and analysis scripts in `validation/` reproduce the commands and calculations. The existing repository summarizer validates every report before the comparison is calculated. All reports are retained, including the slower 100 microsecond results.

`validation.json` records scope, commands, source hashes and unchanged library/core trees. The complete 81-case changed-storage mutation campaign initially had one survivor; its added shutdown test and focused rerun caught it without modifying production code. Reconciled results are 67 caught and 14 genuine compiler-invalid cases, with no unresolved misses or timeouts. The original catalog and outcomes plus the focused rerun remain separate to preserve that history. This is not a full-workspace mutation run. Mutation discovery appends `mutation-alias.toml` to the adapter manifest in a scratch source copy; all executions test the original `persistence_bench` example target, and published manifests remain unchanged.

`artifacts.json` records compressed and decompressed SHA256 values and original sizes for every compressed artifact. The readable interpretation and limitations are in [the main report](../../postgresql-commit-batching.md).
