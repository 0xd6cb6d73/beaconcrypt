<!-- SPDX-License-Identifier: 0BSD -->

# PR #17 proof-source migration

This change repairs the source guards and metadata at PR head `dc267a46f0f11b187ae59d2f58bc8a048b8a3bbc`. It changes no production Rust, wire format, bindings, executable symbolic model, query, expected verdict class or generated Lean code. The full proof toolchain was not run.

## Reviewed source changes

The RustCrypto/no_std port moved hosted registration methods into caller-RNG implementations and made the hosted methods delegate through `OsRng`. Core lifecycle extraction also changed exact controller bodies and private token layouts. The retained guards still expected libsodium calls, the old hosted bodies, `std::mem`, standard-library map entries and the old identity layout. The migrated guards inspect the current implementations and continue to check exact operands, order, one-use continuations, failed-operation behavior and publication boundaries.

The existing Rust mutation matrices retain their original controls and counts. An additional test exercises 27 omission, duplication, entropy-substitution and retained-key substitution controls. It protects the exact hosted delegates, fresh X25519 and ML-KEM entropy handoffs and the Beacon's entropy-free completion path. The inventory independently checks both new guard tables, their actual validator calls and the mutation loop's positive baseline, changed-input assertion and exact count. Four deliberate in-memory changes to those inventory inputs were rejected.

Python admission checks now follow the portable helper while separately checking the exact hosted wrapper and forwarded buffer/RNG. Beacon completion retains its exact key handles and `NoEntropy` implementation, whose methods must return errors. The persisted registration identifier must originate from the consumed request. Existing negative controls now mutate the actual current operands; new controls reject wrapper bypass, substituted input/entropy, synthesized entropy success, deterministic collection hashing and backend rewiring.

All nine specialized source-hash maps retain every previously pinned path. They additionally pin all eight `beaconcrypt-crypto/src/*.rs` files, the backend manifest, `Cargo.lock`, the adapter module/feature wiring and `collections.rs`. This covers the now-local primitive and map implementations that the old adapter reached through external dependencies. Hashes are still checked exactly, and mutation tests exercise the new boundaries.

The 227 free-schedule source-citation checks remain enabled with current method names and line ranges. Only comments changed in the twelve free-schedule libraries. The canonical commitment-comparison fact now names the portable constant-time wrapper instead of libsodium; the implementation delegates to `subtle::ConstantTimeEq`. Removing comments from all thirteen changed ProVerif libraries gives byte-identical executable inputs. Classical-projection limitation markers, model hashes, formulas and all 3,236 verdict classifications remain unchanged.

## Inventory and provenance review

The inventory retains all 2,530 prior entries, refreshes 58 reviewed hashes and adds fifteen entries, for a total of 2,545. The original adapter has nineteen Rust files after adding the collection adapter and four row-persistence/binding modules. The new `crypto-rust` category covers all eight primitive-backend Rust files. Its manifest and the active nextest configuration are new control entries. Exact category counts, complete file sets and symlink rejection remain enforced, including the new backend tree.

The prior inventory predated the RustCrypto/no_std and row-persistence merges. Existing adapter, manifest, lockfile and integration-test changes explain its original twenty stale hashes; this repair additionally changes guard tests, source-checker scripts, source-citation comments, the boundary explanation and the inventory audit itself. No prior path or hash check was removed.

Authentication provenance changes only the workspace lockfile SHA-256, from `d968f0a4ad72cf125fcddb86f4554b94d7d80dc1c227b6c2c4a15395025eb958` to `fa0bcc041f43039e1f186aa7b596260a5c49180d8bf7010eb2e09d6d4be7d17d`. All five other recorded source hashes, all six generated Lean hashes and all tool pins match their previous values. The direct `beaconcrypt-core`, hax and zeroize package records are unchanged; the workspace lock also includes later backend/database and target-specific dependency changes. CI run `40379604750` regenerated matching authentication Lean files and reported only provenance drift. The updated hash records the current reviewed lockfile; no extraction was run locally and no generated Lean file was regenerated or edited.

Rust and release CI now run the complete workspace test command. The active `.config/nextest.toml` includes every source guard in mutation runs. Historical deferral receipts and profiles under `doc/impl/` remain historical records rather than active test exclusions.

## Validation

- `cargo test --workspace --locked`: 544 tests passed, including all 43 source-fidelity tests with zero source-test skips. This includes the existing exhaustive source/model mutation matrices and 27 new entropy controls.
- All twenty-two `proofs/pro-verif/test-*.py` checker suites and `proofs/source/test-getter-profile.py`: 447 tests passed. These tests use mocked or fixture executables rather than real provers.
- `make -C beaconcrypt-core check-proverif-transcript-fidelity` passed on the final source state, including all 43 Rust fidelity tests without skips. This target runs source checks rather than extraction or ProVerif.
- Direct verdict-classification, symbolic-name-order and getter checks passed: 3,236 classified expectations, two complete symbolic continuations and twenty-one getter rows.
- `cargo clippy --workspace --all-targets --all-features --locked` and `cargo fmt --all -- --check` passed. Clippy reports two existing warnings in the parser test and Wasm allocation code.
- `make -C beaconcrypt-core check-inventory`, shell syntax validation and `git diff --check` passed. Extra inventory mutation probes reject new backend files, backend source drift and backend symlinks.

Validation used Rust 1.99.1. On this NixOS host, the existing GNU Make binary was placed on `PATH` and `SHELL` was set to the installed Bash path because `/bin/bash` is absent; no Nix shell or build was started. Focused source and inventory checks do not replace Lean extraction/typechecking, ProVerif security runs, primitive implementation proofs or end-to-end composition. No full native/WASI implementation mutation campaign was rerun for this guard-only change; production code and configured implementation-mutant exclusions are unchanged.
