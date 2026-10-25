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

The complete native mutation campaign passed against an immutable copy of this checkpoint: 1,529 configured mutants, 1,101 caught, 428 unviable, no missed mutant and no timeout. The audit checked all 428 unviable logs: each fails Rust compilation (including three compile-time arithmetic-overflow errors and two parser errors without numeric diagnostic codes). Normal property case counts were retained. The complete actual-WASI guest mutation campaign also passed: all 159 configured mutants tested, 147 caught and 12 unviable, with no miss or timeout. Every unviable guest log reports an actual Rust compilation error. Both campaigns have complete outcome audits against the frozen checkpoint. Logs and machine-readable reviews are under `/tmp/bc-arc-scratch/core-lifecycle-20261025`; no full `verify-in-shell` invocation has run.


### Item 2

Core now owns authentication, key-agreement request selection, initial-record admission, complete-pin validation at delayed completion, and signature/encoding publication gates. The adapter supplies actual primitive and encoding replies. Two complete-record callback seams remain temporary until item 3; this intermediate checkpoint does not claim extracted orchestration of those callbacks. Shared secrets and root preimages are native zeroizing owners; successful root derivation also clears the extracted preimage before publishing the continuation.

After the runtime changes, locked global and isolated-authentication extraction completed successfully. The generated core retains every earlier operation and contains 391 operations, an increase of 82: 61 registration operations, 20 agreement operations and one root-input clear operation. External templates and forwarders are unchanged and there is no new extraction hole. All 100 new public behavioral/helper facts and all 82 new unconditional panic-freedom certificates have exact standard-foundation guards and pass current-source compilation. The regenerated 391-operation aggregate compiles against the exact extracted signatures.

The complete all-feature workspace suite passed 445 tests. Formatting, all-target/all-feature Clippy, and both role-only library checks passed. Source-fidelity migrations retain the symbolic model/query bytes and replace obsolete adapter-body checks with checks of the actual core continuations and native interpreters. Both full mutation campaigns passed against a frozen copy: native tested all 1,639 mutants (1,116 caught, 523 unviable) and actual WASI tested all 159 mutants (147 caught, 12 unviable). Neither campaign missed or timed out a mutant, and every unviable log was audited as an actual Rust compilation error.

The final extraction replay succeeded after the runtime and packaging edits. It changes only registration source-span annotations for the three-line header and the Cargo publication-exclusion digest in isolated-authentication provenance. Removing generated comments leaves the complete function/type declarations byte-identical to the preliminary extraction. The reviewed artifacts were installed and the fresh proof overlay was refrozen under its exclusive lock; subsequent proof builds use the current annotated extraction.

The final separate locked inventory check passed after relocating the old native implicit-opening anchor to three exact core/native clauses; all other checks and the raw-helper gate remain. The reviewed relocation passes its baseline and nineteen negative controls. Lean policy, maintained-root imports, operation coverage and all twelve checker regressions also pass. The aggregate check found a witness-name capture in its generator for an input named `result`; the generator now selects a fresh witness against every input/operation identifier, with same-type and repeated-collision regression fixtures. The correction changes no operation certificate or premise. A comment-only lexical escape-hatch false positive was reworded while retaining the gate.

This checkpoint's source-fidelity validation passes all 36 transcript tests and both joint tests, with 695 moved core/native controls, 114 reviewed operand/handoff rows and unchanged noncomment symbolic-model/query bytes. The initial complete-record callback remains explicit in this commit and is removed by item 3. No full `verify-in-shell` gate has run. The final whole-project canonical Lean build is reserved for the completed three-item tree; this checkpoint's focused aggregate compiles its current 146-module closure.
