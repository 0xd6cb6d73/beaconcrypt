# Compiled-owner statement-hygiene review (read-only)

Target: `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointCompiledOwner.lean` at `8fd99de181bff6e778ce328d21a0aa188416be6a` on `codex/registration-joint-service-composition` (`/tmp/beaconcrypt-registration-joint-service-composition`, clean worktree, HEAD verified). The analysis paragraph is the one-line addition at the end of `doc/formal-verification-analysis.md`.

Verdict: APPROVE_WITH_NITS. The eight exact statements are correct, faithful to their docstrings and the analysis paragraph, carry no premise beyond the already-approved Finish15 slot/`KemBound` premises, and are guarded 8/8 with standard-only axioms. All findings are documentation or naming nits.

## Integrity

- Module sha256 is `9be837ec…dfd5ac`, which matches `compiled-owner-manifest.json`. All four evidence hashes in that manifest match the committed files. The guarded log is empty with exit 0. The axioms log lists exactly `[propext, Classical.choice, Quot.sound]` for all eight statements.
- `PqxdhRegistrationJointFinishCompiler.lean` is byte-identical to its 871d186 version. Both have git blob `482b14da841d5385ae07c6d207710907723285c4` and sha256 `c09c8eff…a15e` (worktree, 871d186 and HEAD). `git diff 871d186 HEAD` on that file is empty. The commit touches only the new module, the analysis paragraph and five handoff evidence files.
- There are no CR characters and no trailing whitespace in the commit. The analysis paragraph is a single line, so AGENTS.md has no mid-sentence break problem.

## Compilation (shared lock, `-j1 -M8000`, timeout 240, lane LEAN_PATH, no `-o`)

`HygieneReview.lean` is the exact module bytes (prefix `cmp`-identical) plus the appendix below. The run took 4 s. Log: `hygiene-run-1.log`; exit: `hygiene-run-1.exit`.
- All eight copied repository guards matched, producing no error or warning in lines 1–198.
- `pp.fullNames` statements were printed for all eight (see log). Every opened short name resolved to the intended constant:
  - `compiler`, `impl`, `classify`, `cap` and `Kind` resolve to `PqxdhRegistrationJointFinishCompiler.*`.
  - `callbacks`, `annotated` and `State` resolve to `PqxdhRegistrationJointFinish.*`.
  - `encode` resolves to `PqxdhRegistrationJointBundle.encode`.
  - `Setup` and `Codec` resolve to `PqxdhServerAuthExperiment.*`.
  - `NativeState` resolves to `PqxdhServerAuthNative.NativeState`.
  - None of the five opened namespaces (PqxdhRefinement, PqxdhJointIdentity, PqxdhJointGapDh, PqxdhServerAuthExperiment, PqxdhServerAuthNative) defines any of the eight names.
- Cap values by `rfl`: `cap none = 56`, `cap (some .decapsulate) = 1`, `cap (some .staticDh) = 1`, `cap (some .localCall) = 0`.
- Negative guard control 1 dropped `Quot.sound` from the expected list for `owner_queries`. The guard rejected it at line 259, as intended.
- Negative guard control 2 applied the repository-form standard guard to a `sorry` theorem. The guard rejected it, reporting `[sorryAx]` (line 268), as intended.
- Non-vacuity was checked in two steps:
  - `slots_satisfiable` proves that for every native owner, of every phase, and every native shared state there is a product state with `seeds[0]? = some identity` and the InitSent KEM slot at index 0.
  - A second example uses this witness to instantiate `PqxdhRegistrationJointCompiledOwner.finish_source` on the one-owner scheduler state `⟨shared, [owner]⟩`, with `found := rfl`, `identityIndex = kemIndex = ownerAddress = 0`. It elaborated.
  - So `found`, `identityOwned` and `kemOwned` are jointly satisfiable, including for InitSent owners. `KemBound` is the pre-existing resource premise from Finish15/ServerAuthSourceCosts.
- The collision probe opened `PqxdhRegistrationJointFinish` and `PqxdhRegistrationJointCompiledOwner` together. This produced `Ambiguous term @owner_source` and `Ambiguous term @finish_continuation`, as expected.

## Statement versus docstring and analysis

- `owner_queries` quantifies over every encoded owner (all phases), raw input, setup and codec, with no premises. For each kind it gives `IsQueryBoundP (classify q = kind) (cap kind)`, i.e. 56 tail requests, 1 decapsulation, 1 joint static DH and 0 for every other capability. The other capabilities are identity create/sign/reveal, KEM create/reveal and both unifSpec coin channels, per `serviceClass`. VCVio's `IsQueryBoundP` is structural over every reply, so the "every typed reply / failed attempt" wording is accurate. This matches the docstring and the handoff target exactly.
- `owner_interpreted` instantiates `program_interpreted` exactly and takes no premises.
- `owner_source`, `owner_original`, `owner_continuation` and `owner_uniform` are the Finish15 statements with the LHS `simulateQ callbacks` replaced by `simulateQ impl (simulateQ compiler …)`. Their premises are identical to Finish15: the identity slot, the active KEM slot and `KemBound`. Their conclusions are otherwise identical, including the uniform bound `69 * max 64 (decapsUniform + baseUniform * decapsBase)`.
- `finish_source` and `finish_continuation` project the scheduler post-state to the reinstalled owner at `ownerAddress`, mapped by `encode`, together with `shared`. The docstrings and analysis claim exactly this. They do not claim the other owners are preserved; that fact remains available from `PqxdhRegistrationJointFinish.finish_source`.
- There is no honest-origin, partnering, admission or authentication premise. No premise mentions `raw`.
- The module contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe`. Its only option is `autoImplicit false`. It has 8 theorems and 8 guards, matched one-to-one by name, with guard text in repository form.

## Nits

1. Wording. The module docstring (line 4) says "resource equalities" and the analysis paragraph says "These are distribution and query-count equalities". `owner_queries` (`IsQueryBoundP`) and `owner_uniform` (`IsTotalQueryBound`) are upper bounds, not equalities. Suggested wording: "distribution equalities and query-count bounds".
2. The lane handoff is stale. `doc/impl/handover/pause-2026-10-01/joint-services/README.md:32` still says "No whole-owner class theorem was started" and gives the restart point as that theorem. The commit added the compiled-owner evidence to this handoff's `evidence/` directory but left the README unchanged, so the next agent would see the wrong restart point.
3. The commit message says "The five reviewed compiler statements are unchanged". The new analysis paragraph says "unchanged for their pending review", and the earlier paragraph and handoff say review is pending. A Compiler5 APPROVE exists only in scratch (`/tmp/bc-arc-scratch/c-work/review-pause/compiler5-notes.md`) and is not recorded in the repository.
4. Name collisions. Six of the eight names reuse names in `PqxdhRegistrationJointFinish`: `owner_source`, `owner_original`, `owner_continuation`, `owner_uniform`, `finish_source` and `finish_continuation`. Two reuse names in `PqxdhRegistrationSchedule`: `finish_source` and `owner_uniform` (the latter in ScheduleCosts). A later scheduler file that opens both namespaces whole gets ambiguity errors, as the probe demonstrated. This is not a soundness risk, since Lean picks or rejects by type. It follows the existing repo convention and the module's own selective-`open` pattern. Suggestion: later consumers should use selective opens or qualified names.
