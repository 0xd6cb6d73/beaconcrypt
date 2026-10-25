# Core lifecycle extraction

This work implements items 1–3 of the 2026-10-25 core-boundary analysis from `codex/mldsa65-transcript` at `278204b921ae31a3e900cf21f690184173e531f5`. The implementation worktree is `/home/user/worktrees/beaconcrypt-core-lifecycle`, on `codex/core-lifecycle`.

## Scope and sequence

1. Put the complete server authentication pin, pending request digest, ordered ML fingerprints, and final associated data into core-owned registration/session values. Production record operations use that committed session binding. Preserve the current transport and persistence formats.
2. Extend registration into first-order primitive request/resume phases. Core selects authentication and key-agreement operands, retains the pending operation, admits the complete initial plaintext, and controls response publication and terminal Beacon completion. Native primitive execution, entropy, allocation, and codec execution remain in the adapter.
3. Add core-owned protected-record sealing and compose the receive lifecycle into an extracted effect machine. Preserve sender/target metadata, raw initial-response framing, admission before advancement, send-key consumption after advancement, and exact receive rejection rollback.

Each item is a separate extraction/proof checkpoint. Do not start the next item's runtime changes before regenerating the complete core extraction for the preceding item and reviewing its generated diff. Update behavioral refinements, unconditional panic-freedom certificates and the exact operation inventory at every checkpoint. New proofs are explained in `doc/formal-verification-analysis.md`; no theorem or assumption is silently weakened to preserve compilation.

## Validation constraints

The owner explicitly excludes the full `verify-in-shell` gate. Run constituent checks as appropriate, including complete core re-extraction after each item, maintained-root Lean compilation, source-fidelity and checker controls, runtime tests, feature checks, formatting, Clippy, complete mutation campaigns, and reviewed inventory checks. Coordinate expensive runs through `/tmp/bc-coord`; hold a Lean slot and memory lease for full Lean builds. Keep all build and extraction evidence under the registered `/tmp/bc-arc-scratch/core-lifecycle-20261025` scratch directory. Existing worktrees and dependency caches are read-only inputs.

Moving a protocol decision into core does not prove primitive correctness or honest execution of its external interpreter. New refinements must state exact request operands, chronological request/result correspondence, and the relation to the existing ideal or computational models. Compiler correspondence, constant-time primitive behavior, physical erasure, and crash durability remain external. Collection and persistence verification are separate from items 1–3.

## Checkpoint receipts

Implementation and validation receipts will be added here as each item completes.

### Item 1

The runtime checkpoint retains complete core server pins and phase-specific request bindings, stores final session AD on both roles, and reconstructs the same binding from the existing snapshot metadata. Independent review found no blocking security or proof-contract issue. A numeric pin-mismatch test was expanded to cover lower values, higher values and exhaustion extremes.

The locked complete core extraction was regenerated after the runtime item completed. It adds 250 lines to `Extraction/Funs.lean` and 29 lines to `Extraction/Types.lean`, removing no prior definitions and adding no external implementation hole. The isolated authentication extraction was also regenerated: its six Lean outputs are unchanged, while provenance records the changed crate root. Eight new behavioral/observer facts and nineteen unconditional panic-freedom certificates compile with exact standard-foundation guards. All 290 earlier certificate mappings are unchanged; the aggregate now covers 309 operations and its canonical dependency build passed all 3,714 jobs.

Validation passed `cargo test --workspace --all-features --locked --offline` (428 tests), formatting, all-target/all-feature Clippy and both role-only checks. The actual WASI guest suite passed 27 ordinary tests and its isolated allocation-failure probe. All 32 transcript-fidelity tests, both joint-fidelity tests and 78 focused Python checker regressions passed. The complete inventory check and Lean policy/root/operation preflights passed. The source-fidelity update retains the ninety ML-DSA controls and adds twelve session controls; 145 source-citation comments across twelve ProVerif files changed without changing any noncomment model/query byte.

The complete native mutation campaign is running against an immutable copy of this checkpoint, with all 1,529 configured mutants and the normal property case counts. Its unmutated baseline passed. The guest mutation campaign and final mutation outcome audit remain pending. These are unfinished validation obligations, not passing receipts. Logs and machine-readable reviews are under `/tmp/bc-arc-scratch/core-lifecycle-20261025`; no full `verify-in-shell` invocation has run.
