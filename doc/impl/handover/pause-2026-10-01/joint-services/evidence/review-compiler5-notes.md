# Compiler5 review notes (read-only)

Target: `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointFinishCompiler.lean` at 871d186 (introduced in fad3306), on `codex/registration-joint-service-composition` in `/tmp/beaconcrypt-registration-joint-service-composition`. Statements reviewed: `compiler_interpreted`, `program_interpreted`, `pool_queries`, `tail_queries`, `prepare_queries`.

Verdict: APPROVE. I found no defect in the five statements.

## Integrity

- `git show 871d186:<file> | sha256sum` gives `c09c8eff96ac180c4cc57323b9983519e02d03ab9289d42bc7ba6487db1ea15e`. This matches `compiler-checkpoint-manifest.json` `source_sha256` and the worktree file. The worktree is clean at 871d186.
- All 32 evidence hashes in `compiler-checkpoint-manifest.json` match the committed files (0 mismatches). The leanpath and check.sh copies match `/tmp/beaconcrypt-registration-joint-service-check`.
- The dependency overlay oleans for JointCreation/Bundle/Preparation/PreparationCosts/Finish were each built after their source mtimes, and those sources are unchanged since their commits.

## Compilation (shared lock, -j1 -M8000, Lean 4.34)

- I compiled the exact 871d186 bytes from a scratch copy (`src/`) with the lane LEAN_PATH. Result: `exit=0` and an empty log (`compiler-guarded.log`/`.exit`). All five `#guard_msgs`/`#print axioms` guards matched, with no sorry and no warnings.
- The probe (`probe/Compiler5Combined.lean`, which is the exact source plus probe lines and writes no olean) also returned exit=0. Its unguarded `#print axioms` output for all five statements is `[propext, Classical.choice, Quot.sound]` and is byte-identical to the committed `beaconcrypt-registration-joint-finish-compiler-axioms.log`.
- The file has no escape hatches (sorry/admit/native_decide/implemented_by/extern). Its only option is `autoImplicit false`. It has 5 theorems and 5 guards, and no private theorems.

## Semantics

- `compiler_interpreted`: `impl ∘ₛ compiler = PqxdhRegistrationJointFinish.callbacks` takes no premises. By rfl, `compiler (.inl q) = simulateQ poolLift (JointPreparation.compiler q)`, `compiler (.inr q) = tailLift q`, `impl (.inl q) = onPool (LiveKemBirth.impl baseImpl joint kem q)` and `impl (.inr q) = onNative (sourceBeaconTail q)`. Because `callbacks (.inl q) = onPool (LiveKemBirth.impl ∘ₛ Prep.compiler) q`, the equality is the real routing identity over the full `Pool × NativeState` product state, including optional replies.
- `program_interpreted` holds for an arbitrary `program : OracleComp (JointFinish.Spec Response) Result` with arbitrary Result. It covers arbitrary adaptive programs and has no premise.
- `pool_queries` is an iff for every kind and budget. With kind=none the RHS predicate is always false, so it yields zero tail requests.
- `tail_queries`: the only premise is the program's own `IsTotalQueryBound budget`, which is a resource hypothesis and not an origin or admission premise. The conclusion is ≤ budget for the tail class and 0 for every `some k` class, so there are zero cross-class requests.
- `prepare_queries` is universal over control/identity/prekey/oneTime/keys/raw and has no slot-ownership premise. By rfl, `preCap` is 0/1/1/0 for none/decap/DH/other. `serviceClass` maps only `.inr (.inr (.decapsulate ..))` to decap and `.inl (.inr (.service _ (.staticDh _)))` to DH. Create, sign, reveal (both pools) and uniform coins all fall into `some .localCall` (checked by rfl examples). The counts are structural, per path, and include failed attempts (VCVio `IsQueryBoundP` definition).
- `cap none = 56` matches `PqxdhBeaconPhase2Bounds.native_tail_bound` (`IsTotalQueryBound 56`). This is only a def here; the next theorem consumes it.

## Scope remarks (not defects)

- The RHS of `compiler_interpreted` is the indexed `JointFinish.callbacks`. Reaching the native source callbacks still requires `owner_source`/`owner_original` (Finish15) with its identity-slot and active-KEM-slot representation premises. The handoff states this correctly.
- `PreparationCosts.Kind.localCall` means "local source callback (cap 13)" under the source-level `classify`, but "other private-service capability (cap 0)" under `serviceClass`. The compiler's `cap`/`preCap` correctly use `serviceCap`, as documented at line 59. This inherited naming could confuse whoever writes the next whole-owner bound.
- None of the five statements is a whole-owner class bound, a global reduction or a security claim. This is consistent with the handoff and the analysis appendix.
