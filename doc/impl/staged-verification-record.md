# Resumed staged verification: completed checkpoints

The work began by reading the repository instructions, remediation plan, maintained verification analysis, retained Phase-1 module and transcript-fidelity test. Both remotes were fetched, and all twelve existing worktrees were inspected before editing; every worktree was clean. The private remote had advanced to `e5a361289191dbb7bab3675d42d688396044d91a`. Registration M3 and security-kdf were already durably integrated and reviewed there, so the post-registration lane could reconcile without editing the registration worktree. Existing unrelated worktrees and the original retained-tail WIP checkpoint remain preserved.

## Published protocol checkpoints

| Branch | Verified commit | Status |
| --- | --- | --- |
| `codex/vcvio-proverif-post-registration-ratchet` | `729967eb8e1c2ab8a55ac60582fd39d2300dc26c` | Independently reviewed and integrated into `vcvio` by fast-forward. |
| `codex/stateful-phase1-writer-reduction` | `3d771abd61f12b881e32c0047e75ae0b5db3c074` | Independently reviewed and durably pushed; intentionally WIP for broader composition and not merged into `vcvio`. |

For each topic, publication verified exact equality of local HEAD, fetched `origin/<branch>` and direct `git ls-remote` against `ssh://git@git.mschn.fr/amn/beaconcrypt`. The same three-way equality was verified when `vcvio` advanced to the ProVerif commit. This closing record is a documentation-only follow-up; its final `vcvio` object is reported separately after publication. No branch was force-pushed.

## ProVerif result and validation

The finite continuation consumes the actual successful sequence-three registration poststate, opens the cached sequence-one frame, consumes only that cached key, rejects its replay before KDF or open, and then accepts a genuine sequence-four frame while retaining sequence two and the original send state. A control changing only cached-key consumption demonstrates replay acceptance. The model and runtime witness preserve the full carried state and context. The isolated original-assignment trace remains separate from M3's replicated completion and accepted outer-ID relabel case.

Semantic reconciliation preserves all 47 post-registration facts, all 27 query hashes and the complete checker-branch hash, the independent 297-case continuation matrix, the earlier independent 409-case matrix, and M3's agreement distinctions. The manifest now has 512 facts and the complete fidelity suite has 3,164 deliberate source/model mutations. CI now includes every one of the 30 Make scenarios, including the previously omitted three registration scenarios.

- `cargo test --locked -p beaconcrypt-core --test proverif_transcript_fidelity`: 16/16 tests.
- Focused post-registration and legacy later-registration ProVerif targets: 27/27 and 18/18 exact classifications.
- `make -C beaconcrypt-core check-generated SHELL=/run/current-system/sw/bin/bash PROVERIF_TIMEOUT=900`: required locked `verify`, all 30 listed scenarios plus two auxiliary result groups, SSProve compilation/assumption/kernel checks, regenerated Lean/ProVerif artifacts, nine panic-coverage regressions, 269 operation certificates and a full 3,168-job Lean build; all pass, no generated drift.
- Separate final `make -C beaconcrypt-core check-inventory SHELL=/run/current-system/sw/bin/bash`: passes after explicit fingerprint and structural review.
- `cargo test --workspace --all-features --locked`: 285 tests pass. `cargo fmt --all -- --check`, `cargo clippy --workspace --all-targets --all-features --locked`, and both no-default-feature role-specific library checks pass; existing unrelated lint warnings remain.
- Complete configured `cargo mutants --workspace --jobs 6`: 1,173 cases in 36 minutes, 816 caught, 357 unviable, zero missed and zero timed out. Configuration and exclusions are unchanged.

Exact changed files relative to the inspected current source baseline:

- `.github/workflows/formal-verification.yml`
- `beaconcrypt-core/Makefile`
- `beaconcrypt-core/proofs/check-inventory.sh`
- `beaconcrypt-core/proofs/pro-verif/check-results.awk`
- `beaconcrypt-core/proofs/pro-verif/later-sequence-registration-control.pvl`
- `beaconcrypt-core/proofs/pro-verif/post-registration-ratchet-control.pvl`
- `beaconcrypt-core/proofs/pro-verif/post-registration-ratchet-queries.pvl`
- `beaconcrypt-core/proofs/pro-verif/post-registration-ratchet.pv`
- `beaconcrypt-core/proofs/pro-verif/production-transcript-interface.pvl`
- `beaconcrypt-core/proofs/reviewed-inventory.txt`
- `beaconcrypt-core/proofs/trusted-boundary.md`
- `beaconcrypt-core/tests/proverif_transcript_fidelity.rs`
- `doc/formal-verification-analysis.md`
- `doc/impl/post-registration-reconciliation-record.md`
- `doc/impl/security-gap-remediation-plan.md`

## Lean result and validation

The full tail, client and outer identity/signing-writer `OracleComp` equalities preserve private prekey and one-time results, identity and target, actual signatures, adaptive candidate and continuation. The exact ordered log retains all three message/signature pairs. The stopped accepted same-target changed-field event yields one fresh valid weak-EUF-CMA forgery, and the constructed standard VCVio adversary gives a coefficient-one advantage bound with no field guess or collision term.

The query module proves signing upper bound three for the retained tail, its local KEM interpretation, the complete client and the actual forgery reduction. The full tail inherits the selector's explicit logical decapsulation cap `qD`; setup and signing add no logical decapsulation. Successful results have exactly three log entries; aborted computations need not complete all three calls. Underlying ambient/uniform primitive workloads remain in the computation and are not declared free.

- Both directly changed modules pass direct Lean 4.31.0 checks without diagnostics.
- Final serial `lake build`: 3,169 jobs pass.
- Locked `make -C beaconcrypt-core check-generated SHELL=/run/current-system/sw/bin/bash PROVERIF_TIMEOUT=900`: all 29 scenarios plus two auxiliary groups on this separate baseline, SSProve checks, both regenerated extractions, nine panic-coverage regressions, 269 operation certificates and 3,169 Lean jobs pass; no generated drift.
- Separate final inventory check passes with 121 handwritten Lean files. Thirteen guarded axiom reports across the two modules allow only `propext`, `Classical.choice` and `Quot.sound`; forbidden-placeholder and diff checks pass.
- The complete mutation evidence above applies to the exact shared production sources and unchanged mutation configuration, verified by Git comparison on both checkpoints. The ProVerif worktree additionally runs its enlarged fidelity suite; this Lean branch's own aggregate passes its 14 fidelity tests.

Exact changed files relative to the inspected current source baseline:

- `beaconcrypt-core/proofs/check-inventory.sh`
- `beaconcrypt-core/proofs/lean/BeaconcryptCore.lean`
- `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhStatefulPhase1EufCma.lean`
- `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhStatefulPhase1QueryBounds.lean`
- `beaconcrypt-core/proofs/reviewed-inventory.txt`
- `beaconcrypt-core/proofs/trusted-boundary.md`
- `doc/formal-verification-analysis.md`
- `doc/impl/query-bound-note.md`
- `doc/impl/stateful-phase1-writer-reduction.md`

## Assumptions and remaining gaps

The structural Lean equalities and fresh-valid extraction assume no cryptographic security conclusion. The algebraic advantage bound uses deterministic verification and a universally quantified runtime map-preservation law; query accounting uses only the selector's explicit resource cap. A small right-hand side depends on the separately stated Ed25519 weak-EUF-CMA contract. The symbolic fixture uses the existing ideal component equations and exact authenticated-prefix equality gate; it adds no primitive-security assumption.

HKDF-SHA-512, ChaCha20-Poly1305, ML-KEM-768, Ed25519, X25519 and BLAKE2b-512 implementations remain outside scope and are treated as perfect implementations satisfying their stated contracts. No primitive internals were proved. Generator-order interchange, related uses and correlations across subsequent phases, source/ideal semantic instantiation, complete oracle/resource simulation, and initialized-chain/KDF secrecy composition remain open. The secret-input KDF work has landed and been reviewed, but this stopped Phase-1 result is not composed into it. The finite ProVerif fixture does not cover arbitrary schedules or all M3 relabel completions; source tripwires and runtime witnesses do not constitute semantic cross-language refinement. Multi-session, reveal, QPT/QROM, asymptotic efficiency, parser/compiler, persistence and physical-erasure boundaries remain explicit.

## Review and environment record

Independent agents reviewed the finite trace, every query hash, the preserved mutation matrices, Make/CI equality, and the complete retained Lean statements and assumptions. A fresh nonauthor reviewed both final Lean modules after earlier reviewers contributed bounded lifting helpers. Shared references and inventory changes stayed with the integration owner.

The locked environment was restored after the previous garbage collection. Final Rust checks used Rust 1.96, Cap'n Proto 1.1.0 and the existing host linker workaround. An initial M3 run timed out under toolchain-rebuild contention; unchanged controls pass in the final aggregate with the explicit 900-second limit. Initial mutation attempts stopped before testing mutants because of host tool selection/build dependencies, and only the complete passing run is counted. A duplicate Lean build caused transient artifact-write errors; the final owner-only serial and locked builds pass. Automatic approval review initially mistook the staged authorized baseline merge for unrelated dirty work; an exact index-versus-`MERGE_HEAD` audit demonstrated that only the nine reviewed Lean files differed from `e5a361289191dbb7bab3675d42d688396044d91a`, and approval then allowed the normal merge commit and push.

All thirteen worktrees were clean after publication, including every unrelated pre-existing worktree. All proof agents completed, and the host process audit found no repository Nix shell, build, Lean, Cargo, ProVerif or Rocq process before cleanup. Logs are retained under `/tmp/beaconcrypt-staged-*`, `/tmp/beaconcrypt-phase1-*` and `/tmp/phase1-writer-*`.

After those checks, `nix-collect-garbage` completed successfully: 5,530 store paths deleted and 18.7 GiB freed. No Nix-backed verification was started after cleanup.
