# Rebase core lifecycle onto current VCVio

On 2026-10-26, fetched `codex/core-lifecycle` from `me` at `eda5a18424d816d9e1f5ba86eafbdae5da788411` and `vcvio` from `origin` at `b766ffe0eac816293c1b5706daa97b589430bdd1`. Rebased the seven lifecycle and portable-backend commits from common base `278204b921ae31a3e900cf21f690184173e531f5` with `--rebase-merges`, retaining the no_std integration merge and all existing Codex footers.

Preserved the original no_std merge resolutions, including its adapter, CI, documentation and validation-receipt changes. Apart from this record, the resulting tree differs from the original lifecycle tip only in the fifteen paths changed upstream: Python checker portability fixes, their inventory hashes and the ML-DSA audit record. Rust sources, Lean sources, generated proof outputs, symbolic models, dependency locks and existing validation receipts remain byte-identical to the original lifecycle tip.

The combined Python files retain lifecycle source guards and upstream deferred POSIX imports. Verdict enumeration retains the upstream temporary AWK source-file fix for Windows command-line limits. Resolved inventory conflicts by updating exactly thirteen validation hashes for these reviewed checker changes. Preserved the original eighteen stale inventory entries associated with the existing no_std migration boundary; this rebase does not migrate their source pins or weaken proof assertions. The existing [merge record](no-std-core-lifecycle-merge.md) and [deferral receipt](no-std-core-lifecycle-deferred.json) remain applicable.

Validation:

- `cargo fmt --all -- --check` passes.
- `cargo clippy --workspace --all-targets --all-features` passes with existing warnings after initializing the pinned vector submodules.
- Executed all twenty-two `beaconcrypt-core/proofs/pro-verif/test-*.py` scripts individually, since unittest discovery skips their hyphenated filenames. The rebased tree and a pristine archive of the original lifecycle tip have identical outcomes and final diagnostics: 404 tests run, three assertion failures, eleven test errors and one class-setup error across twelve failing scripts. These existing failures pin pre-migration backend source hashes or exact source text; the rebase introduces no new failures.
- Independently compared all thirteen changed checker files and their manifest hashes with the expected combination of original lifecycle changes and upstream fixes. All match; the eighteen unrelated original inventory mismatches are unchanged.
- `make -C beaconcrypt-core check-inventory` fails on the original stale `beaconcrypt/src/beacon.rs` hash. The inventory gate remains unsatisfied.
- `make -C beaconcrypt-core verify` enters the locked Nix environment and passes its toolchain checks, then stops at `check-generated-authentication-lean` with authentication extraction drift in `provenance.json`. The generated Lean files still match. The sole provenance mismatch is its existing `Cargo.lock` source hash; both the lock file and checked-in provenance are unchanged from the original lifecycle tip. No generated artifacts were updated. After confirming that no Nix build or shell remained active, ran `nix-collect-garbage` and released 8.8 GiB of temporary store paths.
- `git diff --check` passes, the fetched `origin/vcvio` is an ancestor, and the seven rebased commits retain their Codex footers.
