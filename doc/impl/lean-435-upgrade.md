# Lean and VCVio 4.35 upgrade

The upgrade was prepared from `e6871ab0` (`Adapt proofs to CBOR transport`) on branch `codex/lean-vcvio-4.35` in `/home/user/worktrees/beaconcrypt-435`. The existing proof and CBOR work is part of that committed baseline.

## Target dependencies

| Dependency | Target |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `v4.35.0`, `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| VCVio | `v4.35.0`, `88efe9715a9fa9e7d89635c38cf70259836766c2` |
| PolyFun | `ef4c157b3c6775fb55864303d96f9b400428d5f0` |
| cslib | `v4.35.0`, `5b56df99362532c46e1175381fbbdd755bd56030` |

The extraction stack retains cargo-hax 0.4.2, Aeneas `6852e6474ec508930acba4df79977b3483a10d10`, Hax-Lean `174840bf2f633ae3bae955e08f781b3737ffc0b8`, and Charon `nightly-2026.09.02`. The Aeneas and Hax-Lean source overlays are re-ported to Lean 4.35 with their original regression propositions preserved. The immutable VCVio release manifest supplies the remaining transitive package versions.

## Work and acceptance

1. Resolve the coordinated dependency manifest, update the strict preparation checks, and validate dependency libraries and original regressions.
2. Replace upstream-named forward backports with imports and port foundational event, cache, advantage, coupling, and expectation interfaces.
3. Port consumers in import order, then remove every dependency on the transitional legacy bridge. Preserve complete state and continuations, sampling order, freshness premises, challenge restrictions, loss coefficients, and query accounting.
4. Review changed statements and definitions against the baseline; preserve all axiom guards, proof-root imports, and all-module build coverage. Update protected-source digests and the reviewed inventory only after reviewing the corresponding changes.
5. Run focused checks during development. Reserve the approximately two-hour full project Lean build for integration and final validation.
6. Run generated-artifact drift checks, the complete locked verification, the separate inventory check, required formatting and Clippy checks, and the complete mutation suite after substantial code additions.
7. Document substantial proof changes in `doc/formal-verification-analysis.md` and record actual validation results here. Run Nix garbage collection only after the final Nix-backed command and once no repository Nix process remains active.

The existing `vcvio-upgrade-residual.md` is a starting backlog against the earlier upstream `afa6593f`; the exact 4.35 release must be checked independently. VCVio's release removes the discrete API, changes oracle answer classes and caches, and replaces expectations and total variation with measure-based interfaces. A successful compilation alone does not establish preservation of the original security statement.

## Validation record

The upgrade passes the complete locked Make verification and the separate inventory check. Regenerated Lean, LLBC and ProVerif extraction artifacts are byte-identical to the committed baseline, with no untracked generated outputs.

Completed checks: the exact VCVio release aggregate (3,880 jobs), all dependency regressions (1,811 jobs), and the complete project aggregate including every production endpoint (5,627 jobs). All 86 panic-freedom, refinement, assumption and verification modules pass without source changes, including the generated extraction boundary. The compiled-environment axiom sweep checks 54,572 declarations across all 2,024 project modules and reports zero admissions and zero nonstandard-axiom dependencies against an empty exception baseline. It imports the maintained root and both generated external-template modules, so module provenance also covers project declarations outside the project namespace. Formatting and workspace/all-target/all-feature Clippy pass; warnings remain. The policy, root-coverage and 279-operation panic-freedom inventory checks pass.

The Rust checks use the installed Rust 1.96.0 toolchain explicitly, with its bundled LLD disabled because that installation's wrapper references a removed Nix store path. The stable system linker builds the unchanged production Rust sources. Final `cargo fmt --all` and `cargo clippy --workspace --all-targets --all-features` pass with existing warnings.

The original complete native mutation run exercised 1,437 identities and exposed 29 misses and two timeouts in the existing WASM test boundary. Additional tests cover constructor operands independently, Beacon identity, status counters, call forwarding and close effects, context zeroization before deallocation, actual packed guest replies, host restore/CAS failure/destruction, exact copy lengths and size bounds. Production Rust code is unchanged. The new wazero test runner uses the existing pinned Go dependency, the pinned guest Rust/Zig toolchain and the production 256 MiB memory cap. Its 16 regular guest tests and isolated allocation-bound probe pass; all 12 native guest tests also pass. The isolated probe requires both the exact allocation-failure message and the unreachable trap, so a normally returned rejection, unrelated panic or timeout cannot satisfy the test.

The final mutation suite partitions source identities across native workspace execution and actual wasm32-wasip1 execution. Native execution passes all 1,299 identities: 908 caught and 391 compile-unviable. Guest execution passes all 135 identities: 123 caught and 12 compile-unviable. Their actual catalogs and outcome identities are disjoint and total 1,434: 1,031 caught and 403 unviable, zero misses or timeouts. All 403 unviable identities match the original complete run and have compiler diagnostics rather than linker, runner or tool failures. All 28 originally viable failures are now caught. The original 1,437-case catalog is accounted for exactly by those 1,434 executed identities and three exact-name equivalent exclusions documented in `.cargo/mutants.toml`: packing disjoint 32-bit halves with XOR versus OR, and two allocation-guard changes that cannot alter the zero return under the actual guest pointer width and memory cap. There is no blanket guest exclusion. Guest mutation workers have private Cargo target directories, and the final authoritative run was repeated after discovering and removing an absolute shared-target path in an earlier discarded partial run.

For Nix commands, a scratch flake copies `flake.nix` and `flake.lock` byte-for-byte, verified by SHA-256, so entering the same locked environment does not repeatedly import the ignored Lake build cache into the Nix store. This changes no dependency input or repository flake file.

The reviewed inventory is refreshed from the committed baseline after freezing and reviewing the proof sources. Its preflight check, the inventory gate inside locked verification, and the separate post-verification inventory check all pass with the new file membership and native endpoint spellings, covering 2,449 monitored files. The locked verification passes every configured extraction, ProVerif, Lean and inventory gate, including the 53-case registration sweep with 2,444 exact results, the isolated free-schedule profiles and every extension profile. The final Lean build passes all 5,627 jobs after regenerating extraction. Explicit comparisons against `HEAD`, including staged changes and untracked generated outputs, confirm zero generated-artifact drift. The final verification uses the existing `/tmp/bc-coord` exclusive matrix lease and memory scope to coordinate shared-machine resources.

The final commands are `make -j1 -C beaconcrypt-core SHELL=/run/current-system/sw/bin/bash PROOF_SHELL=path:/tmp/beaconcrypt-435-proof-flake#proofs verify`, followed by a separate `make -j1 -C beaconcrypt-core SHELL=/run/current-system/sw/bin/bash check-inventory` and the generated-artifact comparisons. The combined driver exits zero. Extraction emits two Miri sysroot setup warnings for the unsupported `json-target-spec` flag and uses its reported rustc default-sysroot fallback; extraction and all resulting proof checks pass, and its generated artifacts remain unchanged.

Nix garbage collection was deferred at validation completion because an existing repository Nix shell remained active in `/home/user/beaconcrypt` (PID 2303988). The verification lease was released and no verification job remained active. At validation completion, the original checkout was clean and the upgrade was prepared in the new branch and worktree.
