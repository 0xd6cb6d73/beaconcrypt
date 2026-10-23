<!-- SPDX-License-Identifier: 0BSD -->

# Full ML-DSA branch Lean build

## Status

The owner authorized a full Lean build on 2026-10-23, based on `ac2338710975bd5468fd4f456ca43ce813a7b9ed` plus the reviewed metadata-only model-baseline repair below. The canonical build passed with exit zero: 5,639 jobs in 28 minutes 20.08 seconds, including all 2,035 project modules. Independent review confirms every project module has a fresh local compiled artifact and all source bytes remain unchanged. `verify-in-shell`, ProVerif and extraction were not run.

## Reviewed baseline repair

The panic-freedom preflight still pinned the eleven-file model digest from `6d6ec443`, immediately before `42a41516` added `Model/Pqxdh/TranscriptAuth.lean`. The later `a9254229` change to that added file affects only its introductory comment. Independent comparison confirms all eleven original model files remain byte-identical to the Lean 4.35 merge `248953c9`; excluding the additive file reproduces the complete previous `92278ec9` digest exactly.

The twelve-file digest is now `dbbe6453280d7d670e07bb883016743ec03b4dbc3693fc046818258f608a5b06`. The added module's bytes match its existing reviewed-inventory entry. Its public byte constructors, width predicates and 19 guarded facts add no cryptographic axiom or replacement state-machine definition. Only the expected digest and its explanatory documentation change; whole-tree sorted path/content hashing and rejection of unreviewed additions or edits remain enforced. No Lean declaration, theorem statement, extraction, aggregate API, certificate or regression is changed. Inventory refreshes cover only the checker, Lean README and trusted-boundary prose; the 33 historical mismatches retain their previous expected digests.

## Environment and execution

The scratch flake's `flake.nix` and `flake.lock` are byte-identical to the repository files. The pinned environment runs Lean 4.35.0 at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and its Lake 5.0.0 build. A fresh private `.lake` holds all package checkouts and build outputs. Dependency preparation verifies exact revisions and applies the already reviewed Aeneas/Hax-Lean compatibility patches. The pinned Mathlib cache preparation completed successfully in about 95 seconds, decompressing 9,030 already-cached files without additional downloads.

The build holds one coordination Lean slot and a 16,384 MiB memory lease, with `LEAN_NUM_THREADS=6`. The runner clears inherited `LEAN_PATH` and `LEAN_SRC_PATH`; the independent process audit confirms Lake's generated import paths resolve only into this worktree's private `.lake`. No shared or frozen dependency tree is rebuilt.

Inside the pinned shell, the runner executes:

```bash
make -j1 -C beaconcrypt-core SHELL=bash check-lean
```

This target prepares dependencies, checks policy and root coverage, validates panic-freedom contracts, then runs `lake --rehash build`. The library glob covers the maintained root and every project submodule. All 2,035 project Lean source inputs were fingerprinted before the run. Neither `verify-lean` nor `check-generated-lean` is used, so no Hax extraction or generated-artifact rewrite occurs.

## Validation receipt

Preflight passed all nine checker regressions and the unchanged 279-operation contract inventory before entering Lake. The final log reports `Build completed successfully (5639 jobs).` and no errors. It contains 423 warning rows from the checked-in proof and dependency sources, including deprecation, module-system and linter warnings; no new warning suppression was introduced and this record does not claim warning-free compilation. No Lean source or deprecated API use was added by the baseline repair.

The independent final audit matches all 2,035 source fingerprints to the starting snapshot and all 2,035 fresh, regular, private compiled artifacts to their actual build traces. Every trace identifies the Lean 4.35 compiler, corresponding source and output hashes; none is synthetic. All 14 dependency revisions match the manifest, and their only source changes are the exact approved Aeneas/Hax compatibility patches. The six authentication extraction input pins, six generated output hashes and provenance remain unchanged. No output path escapes into a shared build tree. The copied flake and lock still match the repository byte for byte. Exactly the same 33 historical inventory mismatches retain their expected pins.

GNU Time reports 28:20.08 elapsed and maximum child resident memory of 6,510,248 KiB. The five-second cgroup sampler observed a peak of 8,379,584,512 bytes, about 7.8 GiB, across the build scope. These are different measurements: the latter includes the scope's charged file cache. The memory lease and Lean slot were released after completion. Rust sources, Lean sources, generated artifacts, certificates and the panic-freedom manifest are unchanged. Python formatting and Git whitespace checks pass; the existing checker regressions remain unchanged.

Evidence is under `/tmp/bc-arc-scratch/mldsa-full-lean-20261023`: `build-command.json` and `build.sh` preserve the exact invocation; `build.log`, `build.time`, `build.exit` and `final-build-summary.json` record completion and measurements; `prepare-receipt.json` records preparation success; `model-pin-review.json` records the model comparison; `lean-source-hashes-before.json` and `lean-source-hashes-after.json` record the matching source fingerprints. `independent-build-audit.json` and its text sibling record the independent artifact, dependency and extraction audit.

This build checks the committed Lean artifacts and reviewed dependency sources. It does not migrate the historical AD153/CTX229 extraction or approximately 115 handwritten modules to current production types, discharge ML-DSA security assumptions, resolve the 33 historical inventory mismatches or establish a global verification result. The [verification analysis](../formal-verification-analysis.md#full-lean-build-and-model-baseline-review-2026-10-23) records the repair's scope.
