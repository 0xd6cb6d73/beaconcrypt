# Merge PostgreSQL benchmark evidence

The [results report](../../merge-postgresql-results.md) covers PostgreSQL at 1, 100 and 1,000 registered peers on `codex/core-row-merge`, source commit `40f66d60d268a7153043b90f483899ba00515641`. The measured release binary SHA256 is `774b1a86945b4a865d842659faf0f046d3cce3a011a005a3397eaadd4d76f20e`. All three configurations completed on their first attempt under the same collection policy. The analysis contains 39 groups, 351 arm/trial records, 840,960 callbacks and 14,108,239,872 plaintext bytes.

Read the [per-trial tables](analysis/tables.md), [arm/trial CSV](analysis/arm-trials.csv), [paired-ratio summaries](analysis/paired-ratio-summary.csv), [cohort CSV](analysis/cohort-trials.csv) and [input receipt](analysis/input-receipt.json). Percentiles are calculated within trials and never pooled across them. The [analysis notes](analysis/README.md) explain ownership, latency accounting and interpretation limits.

## Archived inputs

`collections/metadata.tar.gz` contains the original frozen plan, retained manifest, collection events, scripts, build/validation receipts and resource reservation records. The three axis archives contain their raw reports, summaries, settings, monitoring journals and logs. Extracting these archives together restores a `collection/` directory. No attempts were discarded in this collection.

`validation.tar.gz` contains the build and source-hashing scripts, build receipt and log, focused validation and PostgreSQL restart logs, cluster manifest, instrumentation policy and collection driver/analysis logs. The source-hashing helper includes `beaconcrypt-crypto/src/` so the merged crypto backend is covered. The validation command passed all 87 checks, including the otherwise ignored live PostgreSQL tests.

The archives exclude generated database fixtures, the live database cluster, Cargo build output and executables. These are not analysis inputs. [archived-files.json](archived-files.json) records the size and SHA256 of every archived file; all 64 entries were verified against the compressed contents. The top-level `SHA256SUMS` covers every published file here except itself. Original absolute paths in receipts describe provenance and are retained unchanged.

The frozen plan SHA256 is `bbffe7afcaa7814d95f24cfeb31789aa50ad03572476d5cb9a1e3a10e48c5687`. The included `analyze-results.py` is reused unchanged from the earlier concurrent collection. It checks the authoritative retained attempt/report hashes and recomputes the stored summaries before exporting statistics; it does not choose attempts based on timings.

## Verify and replay analysis

Run `sha256sum -c SHA256SUMS` from this directory to verify the published files. Python 3.11 or newer can reproduce the numerical analysis after extracting the collection archives:

```bash
mkdir replay
for archive in collections/*.tar.gz; do
    tar -xzf "$archive" -C replay
done
python3 analyze-results.py \
    --plan replay/collection/collection-plan.json \
    --report replay/collection/axis-01-postgres-peers-1-attempt-01/report.json \
    --report replay/collection/axis-02-postgres-peers-100-attempt-01/report.json \
    --report replay/collection/axis-03-postgres-peers-1000-attempt-01/report.json \
    --output replay/recomputed-analysis
```

Allow several GiB of memory for loading the raw JSON reports. Numerical outputs are reproducible; relocated absolute paths in the newly generated input receipt will differ. The collection plan also records the original execution arguments, database settings, tool versions and quiet-window policy for a future measurement run. Replaying analysis does not start PostgreSQL or rerun benchmarks.
