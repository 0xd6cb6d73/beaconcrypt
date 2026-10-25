# Concurrent persistence evidence

The [results report](../../concurrent-row-persistence-results.md) explains the five completed comparisons: PostgreSQL at 1/100/1,000 registered peers and SQLite at 1/100. The analysis accounts for 65 groups, 585 arm/trial records, 1,270,800 callbacks and 23,096,070,144 plaintext bytes. SQLite at 1,000 peers was stopped at the user's request; neither interrupted attempt supplies primary measurements.

Read the [per-trial tables](analysis/tables.md), [arm/trial CSV](analysis/arm-trials.csv), [paired-ratio summaries](analysis/paired-ratio-summary.csv), [cohort CSV](analysis/cohort-trials.csv), and [input receipt](analysis/input-receipt.json). Percentiles are not pooled across trials. The [analysis notes](analysis/README.md) explain latency accounting, ownership and interpretation limits.

## Raw collections

Each file under `collections/` is an independently compressed tar archive. Metadata archives contain the original plans, scripts, build/validation receipts, event logs and stop/recovery records. Each attempt archive contains its raw report when present, stored summary, settings, monitor journal and logs. Extracting them together restores all three original collection directory names. Generated database fixtures, live data directories and executables are excluded; [archive-exclusions.json](archive-exclusions.json) records the scope.

`collection-20261025` contains retained PostgreSQL 1/100, a historical SQLite1 result, the initial setup/interference failures and the five-second SQLite lock-timeout failure. `collection-sqlite-wait-v2` contains retained SQLite1/100 at the 600-second wait setting and both discarded SQLite1000 attempts, followed by the explicit user stop. These two campaigns are incomplete; only their individually retained reports are used. `collection-postgres-final` is a completed one-axis PostgreSQL1000 collection. Its CPU-noise threshold was revised before measurement, as documented in its plan and the results report.

The old PostgreSQL reports use source `e26909af1d1aeb1ee48bf197b8be6c6b35ef643e`, binary SHA256 `5dcd5f30b005b1652bd2980963186190952d3d9fda68bdee33b0824553c51e80`. The later reports use `77d5633d6a180b9c9ca37b1ceddbaaab303c2f3b`, binary SHA256 `097a0d6dd53666fad470597ce0ccd8db06fe1de84161b2bf376751b6076b553d`. Only the SQLite setting, its metadata test and documentation changed between these revisions; library, PostgreSQL and common workload code are unchanged.

## Validation

`correctness/native-complete-audit.tar.gz` and `wasm-complete-audit.tar.gz` preserve the completed native/WASI audit logs, catalogs, source bindings and reviewed outcomes; their adjacent JSON files contain file manifests. `validation.tar.gz` contains the focused benchmark validation, real PostgreSQL restart evidence, release receipts, source comparison and SQLite-wait follow-up. The earlier [cached-row implementation evidence](../../cached-row-persistence-results/2026-10-25/README.md) also documents bindings and persistence testing.

`benchmark-mutation-diagnostic-and-stopped-run.tar.gz` preserves an initial harness diagnostic and the later user-interrupted run. The latter completed 60 of 633 candidates: 57 caught and three compiler-unviable, with 573 uncompleted. It is incomplete supplementary evidence, not a passed mutation audit. No further exhaustive harness testing was performed after the scope correction.

The limited Mythic HTTP/AMQP/provider/PostgreSQL acceptance and its evidence were pushed to [mythic-beaconcrypt](https://git.mschn.fr/amn/mythic-beaconcrypt/src/branch/codex%2Fmythic-local-e2e) at `5452c936ed7a3d72509be1138b45e8d4fc311882` and the [Mythic custom-provider feature](https://git.mschn.fr/amn/mythic/src/branch/codex%2Fcrypto-shim-local-e2e) at `ccbacbb71aa25e37156b8001f87a53a042805bea`. That acceptance uses the existing full-state provider contract, not a production row migration. The fork's changes stay inside the custom-provider feature.

## Verification and replay

Run `sha256sum -c SHA256SUMS` from this directory to verify the published files. To replay the numerical analysis with Python 3.11 or newer, extract the collection archives into a new directory and use the included scripts:

```bash
mkdir replay
cp analyze-final.py analyze-results.py replay/
for archive in collections/*.tar.gz; do
    tar -xzf "$archive" -C replay
done
python3 replay/analyze-final.py --root replay --output replay/recomputed-analysis
```

The wrapper checks the retained attempt/report hashes and recomputes stored summaries. It uses the completed final campaign's normal validator, directly checks the four retained reports from the two incomplete campaigns, and reuses the same statistical calculations for all five. It does not invent completed campaigns or select attempts by timing. Absolute paths in original receipts record provenance; replay output records its relocated paths. `archive-final-evidence.py` records the publication copy/compression procedure.
