# Milestone B handover: server authentication (route R1)

This directory hands the unfinished Milestone B work to the next agent. Milestones A, C and D of the audit remediation are complete, committed and verified; Milestone B is about half built. Everything needed to continue is either committed in the Lean library, recorded in the documents listed below, or copied into this directory from the scratch area where it was being developed.

## Read first

- `AGENTS.md` at the repository root, with one override from the owner: never run `nix-collect-garbage`, because other agents share this machine's Nix store.
- `doc/impl/audit-0b4039e-remediation-plan.md`, section 6. It records the Milestone B experiment, every owner decision (subsections "Review decision (2026-09-29)", "Design grounded in the Rust implementation (2026-09-29)", "Owner decisions on the staged design (2026-09-30)") and the current status ("Milestone B status (2026-09-30, paused)").
- `doc/impl/server-authentication-design.md`, the staged Lean design: experiment, events, headline statement, negative controls, the hybrid chain (section 5), the assumptions (section 6), the stage plan (section 7), risks (section 8), the critique responses (section 9), the spike results (section 10) and review obligations appended after section 10.
- `doc/formal-verification-analysis.md`, section "Audit remediation B: server authentication (in progress)", for the plain-English account of the committed stages.

## Owner decisions that bind all remaining work

- Route R1: zero-salt HKDF-Extract on 192-byte inputs (the PQXDH root input) is a programmable random oracle; every other HMAC use, HKDF-Expand included, stays real. The hardness assumption is the existing game `PqxdhJointGapDh.game`, described as a twist-inclusive strengthening of Gap-DH on libsodium's X25519 treated as a black box.
- Approved functional contracts, stated as premises in `PqxdhServerAuthAssumptions`: `X25519ClassLaw`, `X25519ScalarSpread` (for the session-collision term), `NonzeroHonestDh` (negative controls only).
- Partnering is by identical root derivation (same 192-byte root input); the Server-assigned key identifier is not part of partnering, it is authenticated inside the sequence-one plaintext and compared by the W2 event.
- No key-compromise impersonation: no Beacon secret is revealed. Reveals of a Server session return only its post-registration state.
- The Server is modelled with two oracles, accept and build, as the public Rust `ProviderServer` trait exposes them (`beaconcrypt/src/server.rs:118-121`). The Server-session budget `Q` is a parameter, evaluated in the documentation at a few tens.
- Out of scope, never modelled or proved: Cap'n Proto and serialization (messages are abstract byte strings each side can decode; decoders and writers are free functions; only abstract message-model premises such as read-back laws are allowed), persistence, attacker access to the running code, and libsodium internals (libsodium is assumed correct).
- Design choices must follow the Rust reference implementation: the proofs cover the protocol and its reference implementation, so cite `beaconcrypt/src` and the extracted functions with file and line.
- Proof rules: axioms only `propext`, `Classical.choice`, `Quot.sound`, with a repository-form `#guard_msgs` / `#print axioms` guard on every theorem; bound terms are advantages of constructed reductions plus explicit numbers, never "for all adversaries, advantage ≤ ε" premises; secrets sampled inside experiments; every adversary restriction justified; new assumptions need owner approval before anything is proved with them; do not weaken or delete existing theorems; plain-English explanations of new proofs go into `doc/formal-verification-analysis.md`; no mid-sentence line breaks in Markdown.
- Commits: short imperative sentence-case subjects, the footer `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`, no history rewrite, push after each milestone.

## Status of Milestone B

All modules below are in `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/`, imported by `BeaconcryptCore.lean`, gated in `proofs/check-inventory.sh` and hashed in `proofs/reviewed-inventory.txt`. Each was reviewed by independent adversarial reviewers before it was committed.

| Stage | Module | Commit | Content |
| --- | --- | --- | --- |
| B1 | `PqxdhExtractRomSeparation` | `12d5214` | the zero-salt, 192-byte HMAC patch and proof that it changes no other HMAC evaluation of the protocol |
| B2 | `PqxdhServerAuthAssumptions` | `12d5214`, `7db487f` | X25519 class law, scalar spread, nonzero honest DH, and the Gap-DH term `serverGapDhAdvantage` |
| B3a | `PqxdhExtractRomFamily` | `884cf49` | the lazily sampled random-oracle table shared by honest derivations and adversary queries |
| B8a | `PqxdhServerAuthKeySchedule` | `25dd43e` | `keySchedule_bound`: the 108-byte first-ratchet output of a uniform entry is indistinguishable from uniform up to five constructed-reduction advantages |
| B9a | `PqxdhPhase2LocalMatching` | `07415ba` | a Beacon acceptance matching a partner's seal accepts the partner's key identifier, payload and associated data |
| B4a | `PqxdhServerAuthExperiment` | `aec2ee2` | the game, the accept/build/finish/hmac/hash/reveal oracles, the events W1-W3, BadB, CollB, EntryEvent, `win_le_games`, the invariant `GameInv` and the erasure lemmas |
| B5a | `PqxdhServerAuthNegativeControl` | `84feb7d` | the gate: `negative_control` (seed revealed, W1 with probability at least one minus the KEM error), `relay_not_win`, `relay_live` |

Work in progress, copied into `stages/` in this directory (not built, not inventoried):

- B6, the Gap-DH reduction (`stages/b6/`). The main result `badB_le_gapDh` (Pr[BadB] at most `serverGapDhAdvantage` of the constructed extractor of `scanClient`, premises `X25519ClassLaw` and the random-oracle query budget) compiles with no `sorry` in `Dev14.lean`. `Dev17.lean` adds the inner query counts (body signs nothing, at most `qH` table queries, at most `Q + 1` derivations), and `Dev18.lean` is the latest file, possibly mid-edit. The files are cumulative; continue from `Dev18.lean` if it compiles, otherwise from `Dev17.lean`. Remaining: the outer counts `scanClient_signing` (0), `scanClient_decisions` and `scanClient_uniform`, then docstrings, guards, cleanup, review and integration. `notes.md` has checkpoints 0-3 and the exact next steps.
- B8b, the per-entry key factoring (`stages/b8b/`), the largest stage (estimated 5000-7500 lines). Checkpoint 1: the generic identical-until-bad and eager-sampling lemmas (`src/B8bScratch/Generic.lean`), the flattened game skeleton (`Skeleton.lean`) and the per-query flat couplings (`Flat.lean`) compile; `dev/` holds the next pieces in progress. The architecture is written out in `notes.md` (checkpoint 0 "Architecture decided"); the next step is to assemble `flat_couple` and the game-level inequality, then the factored game, the coupling to it and `entry_le_uniform`. `build.sh` compiles the scratch modules to a private olean directory; adjust its hard-coded paths.
- B7, the session-collision bound: not started beyond reading. The design (section 5 step B, section 6.4) gives the argument.
- Stage S spike (`stages/spike/`): `SpikeServerSend.lean` proves, with no `sorry`, the Server-send half of `entry_factor`; B8b should port it. `stages/b4a/SpikeLink.lean` checks that B4a's `tail_native` composes with it.
- B5b witness seed (`stages/b5a-witness/WitnessCheck.lean`): a toy instance satisfying all premises of the negative controls with zero KEM error. It is kept out of the library because it imports `PqxdhHypothesisWitness` (77 extra modules); B5b should start from it. The F6 toy crypto fails `NonzeroHonestDh` and cannot be wired, so X25519 and sign/verify must be replaced as this file does.

Not started: B9b (the CTX step for each table entry), B10a (the intermediate headline with explicit game terms), B10 (the headline `server_authentication`), B5b (witness and pre-seal reveal control), B3b/B4b (equality with the extracted code, off the critical path), B11 (documentation, the replacement row in `doc/composition-assumptions.md` "Required hybrids and losses", and one `make verify`). Optional stages B12 (post-acceptance corruption) and B13 (record oracles in Lean) are not planned by default.

## Recommended order

B6 (finish and integrate), B7, B8b, B9b, B10a, B10, B5b, B3b/B4b, B11. Build intermediate theorems with explicit game terms first, as Milestone C did, so that a stalled stage still leaves a correct statement. `stage-notes/` holds the development notes of every committed stage; they explain choices that the modules' docstrings only summarize.

## Working method that was used

- Each stage was written in a scratch directory outside the worktree and compiled with `cd beaconcrypt-core/proofs/lean && flock <lock file> timeout 3600 lake env lean <file>`. One Lean process at a time: the machine has 16 GB shared with other proof agents, and a Lean process takes about 4 GB. `lake build` of the library was run only when integrating.
- Each finished module was reviewed by two or three independent reviewers with distinct lenses (fidelity to the Rust code and the design, meaning of the security notion, statement hygiene), and every critical or major finding was sent to a second reviewer who tried to refute it. `review-templates/review-three-lens.js` is the workflow script used for B4a and can be adapted. Findings were fixed before the commit.
- Integration of a finished module: copy it into `Computational/`, add its import to `BeaconcryptCore.lean`, run `lake build BeaconcryptCore`, run `tools/add-module-gates.py <Module>` (adds the per-module gates to `check-inventory.sh`, raises the handwritten-Lean count and adds the `reviewed-inventory.txt` line), run `tools/refresh-inventory.py` on every changed inventoried file (`BeaconcryptCore.lean`, `check-inventory.sh`, `trusted-boundary.md`, re-edited modules), then `LC_ALL=C bash proofs/check-inventory.sh` from `beaconcrypt-core`. Both scripts hard-code the worktree path `/tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core`; change `core` at their top. To regenerate the gates of a module whose theorem set changed, delete its `require_line_count` and `selected_source_module=` lines from `check-inventory.sh` first.
- Pitfalls: the inventory rejects the standalone words sorry, admit and axiom anywhere in handwritten Lean, docstrings included; the gate counts lines starting with `theorem `, so put any `@[simp]` on its own line; generic names (`Query`, `game`, `Spec`, `Inv`, `initialState`, `step`, `realGame`) collide with other namespaces that later stages open, so use distinctive names or qualify; VCVio's `Pr[= …]` and `probEvent` are deprecated, and modules disable the linter per declaration with `set_option linter.deprecated false in`.
- Full verification: `make -C beaconcrypt-core verify` runs `nix develop path:..#proofs`, which copies the whole worktree including the 20 GB `.lake` into the store. Instead, enter the same locked shell from a directory holding only copies of `flake.nix` and `flake.lock` (check their hashes match), with a GC root: `nix develop --no-update-lock-file --profile <profile path> 'path:<dir>#proofs' -c bash -c 'B=$(command -v bash); make -C beaconcrypt-core SHELL="$B" verify-in-shell && make -C beaconcrypt-core SHELL="$B" check-inventory'`. The `SHELL` override is needed because the Makefile hard-codes `/bin/bash`, which this host does not have. The last full run (commit `1c9aa50`, Milestones C and D) passed in about 50 minutes.

## Contents of this directory

- `README.md`: this handover.
- `stages/b6/`: B6 development files and notes.
- `stages/b8b/`: B8b scratch modules (`src/B8bScratch/`), development files (`dev/`), the build script and notes.
- `stages/spike/`: the stage S spike and its notes.
- `stages/b4a/SpikeLink.lean`: the check that B4a's build tail composes with the spike.
- `stages/b5a-witness/WitnessCheck.lean`: the seed of the B5b witness.
- `stage-notes/`: the development notes of the committed stages B1, B2, B3a, B8a, B9a, B4a and B5a.
- `tools/`: the inventory helper scripts.
- `review-templates/`: the review workflow script.

The Lean files here are not part of the Lake build and are not scanned by the repository's policy checks, which cover only `beaconcrypt-core/proofs/lean/BeaconcryptCore`. Before moving any of them into the library, rename modules and namespaces to their final names and make them pass the rules above.
