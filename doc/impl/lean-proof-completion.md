# Lean proof completion and F* retirement

## Objective

Complete panic-freedom coverage for the default production `beaconcrypt-core` Lean extraction, then replace every maintained F* guarantee with a checked Lean theorem. Each completed milestone is committed and pushed to the private `origin` remote. The integration branch is `codex/lean-proof-completion`; agent worktrees live under `/home/user/worktrees`.

## Acceptance criteria

The ideal PQXDH and ratchet models are immutable for this work. No file under `beaconcrypt-core/proofs/lean/BeaconcryptCore/Model/` may change from starting commit `27ff282`; improvements belong in extracted-code proofs, refinements, and verification tooling.

Panic freedom means that each covered extracted production API returns `RustM.ok`, including ordinary `Err`, `None`, cancellation, and exhaustion results. Internal generated closure and loop helpers may require the bounds established by their callers. Any representation invariant required by an exported API must have checked constructor and preservation theorems. Merely assuming a helper returns `ok`, assuming a failure-trace witness exists, or assuming correct cryptographic responses does not discharge totality. Successful extraction and a compiling `RustM` definition alone do not establish panic freedom.

F* replacement requires a declaration-level coverage ledger with checked Lean counterparts or documented equivalent composition for every maintained F* guarantee. It includes material-slot correspondence, complete future preparation and publication, complete receive outcome classification, repeated rejection/retry and replay, derivational reachability, conditional restoration, paired-session composition, exact byte layouts, registration transitions, and commitment collision witnesses. Cryptographic implementations, compiler behavior, adapter execution, persistence provenance, and physical erasure remain explicit external assumptions. Existing F* artifacts and gates remain until their proof surface has replacements; no theorem is silently weakened to retire a backend.

## Milestones

1. Establish a reproducible Lean baseline and a complete panic-freedom API inventory. Repair any baseline compilation issues without weakening theorem statements.
2. Prove byte/initialization, control, bounded-loop, restoration, and effect API totality. Add a checked aggregate surface and a drift gate. Run the locked proof verification, policy and trust-boundary checks, relevant mutation suite, and required formatting/lint checks; commit and push the completed panic-freedom milestone.
3. Prove cached material-array publication and exact future staging/publication, then complete receive outcome and derivational preservation. Validate, document, commit, and push completed proof units.
4. Compose arbitrary finite operation traces, replay/retry, restoration, and paired-session preservation; close the remaining declaration-level F* coverage ledger. Validate, document, commit, and push.
5. Retire the F* proof surface and backend-specific build/CI/inventory requirements only after all equivalent Lean guarantees are checked. Run the complete replacement verification and mutation gates, update maintained documentation, commit, and push.

## Coordination and verification

The first parallel tasks own separate new modules: `PanicFreedom/Control.lean` and `Restore.lean`; `PanicFreedom/Bytes.lean` and `Pqxdh.lean`; and `PanicFreedom/RatchetLoops.lean`. The coordinator owns effect composition, the aggregate coverage gate, shared documentation, and integration. Agents check proof changes incrementally with the pinned Lean 4.31.0 toolchain. No agent runs Nix garbage collection; the coordinator collects only after all repository Nix activity ends. Existing build caches are copied, never shared for mutable proof outputs.

## Progress

- Created isolated integration and three agent worktrees from `27ff282`.
- Verified access to `ssh://git@git.mschn.fr/amn/beaconcrypt` and confirmed the baseline `vcvio` head.
- The tracked baseline and integrated foundation build passed; the final panic-freedom build now checks 3,110 jobs.
- Checked foundation modules are imported by the maintained root and included in the trust-boundary inventory. The inventory and formatting checks pass; core unit and transcript-fidelity tests pass.
- Full workspace mutation testing passed all 1,164 mutants: 814 caught, 350 unviable, zero missed and zero timed out.
- Locked aggregate verification currently fails at regenerated F* initial-output arithmetic before Lean; historical artifacts remain intact. Fresh locked Lean extraction reproduced all generated files without changes.
- Panic-freedom milestones 1 and 2 are complete: all 269 unconditional contracts compile, the locked complete Lean build passes (3,110 jobs), all nine checker regressions pass, and the reviewed inventory passes. The full dependency audit found only standard Lean axioms (19 axiom-free contracts; 250 with propext/Classical.choice/Quot.sound).

- Checked semantic units now include complete cached publication and cached-success refinement, fixed KDF interpreter conformance, concrete complementary initial sessions, all non-lifecycle raw PQXDH parity statements, exact future loop behavior, canonical future admission and nonfinal continuation, and execution composition/determinism. Terminal future refinement, complete receive traces, restoration, paired lifecycle preservation, and remaining F* ledger work continue.
- A second full 1,164-case workspace mutation run is in progress for the semantic stage. The current Rust source is unchanged; the new Lean units are independently compiled.
- The first semantic checkpoint passes the complete 3,118-job Lean build, all nine panic-coverage regressions, and the reviewed inventory. The cached publication/success, canonical admission/nonfinal continuation, and execution determinism capstones depend only on the standard Lean axioms. The second full mutation run continues, and the aggregate verification limitation above remains open.
- The complete future trace, publication, synchronous receive, and arbitrary finite mixed-history units pass the 3,129-job Lean root build and reviewed inventory. The new lifetime capstones use only the standard Lean axioms. Both completed full mutation runs report 814 caught, 350 unviable, zero missed and zero timed out out of 1,164 mutants. Raw commitment parity is complete; the conservative ratchet declaration audit continues to distinguish structural validity from canonical provenance.
- The structural/rollback checkpoint passes the complete 3,139-job Lean root build, reviewed inventory, all nine panic-coverage regressions, and the immutable-model check. New unconditional termination/rollback/retry and generic structural publication/send capstones use only the standard Lean axioms. Paired PQXDH lifetime composition and complete canonical restoration are integrated. The third full mutation run is in progress; generic structural restoration and future receive preparation remain assigned work.

The structural receive/restoration checkpoint integrates exact relative future traces and publication from `ValidRefined`, unconditional preparation of valid cached targets, full successful-output classification, generic replay with independent retry callbacks/interpreters, the historical fifty-step/forty-nine-skipped boundary, arbitrary finite mixed-history validity, full raw control restoration, and generic trusted-persistence provenance. The pinned Lean gate passed all 3,152 build jobs; the reviewed inventory now has 104 handwritten Lean files, all nine panic-coverage regressions pass, and the audited capstones use only standard Lean axioms. All ideal model files still match the starting commit. The remaining declaration audit concerns cached/future internal helpers; F* tooling and historical artifacts remain present until that audit closes. Automatic approval review rejected premature retirement before the completed coverage evidence existed, so no retirement mutation was made. The next step is to finish those scoped audit rows and retry the concrete authorized retirement with the completed proof evidence.
