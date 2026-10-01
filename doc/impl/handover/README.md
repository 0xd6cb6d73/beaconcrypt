# Handover: remediation of proof audit 0b4039e

## Current pause handoff

Read [the 2026-10-01 pause handoff](pause-2026-10-01/README.md) for the latest integrated validation, topic checkpoints, unfinished proof states, publication holds and exact resume instructions. General proof work is paused at the owner’s request. The remediation report below records the earlier milestone state.

This is the handover for the whole remediation of the proof audit at `0b4039e` (audit report: `/home/user/worktrees/beaconcrypt-proof-audit/doc/impl/proof-audit-0b4039e.md`, a separate worktree that is read-only for this work). It covers Step 0 and Milestones A, B, C and D. Milestones A, C and D are complete and verified. Milestone B (server authentication, finding F1) is about half built and has its own detailed handover in `milestone-b/README.md`.

## Where the work lives

- Worktree: `/tmp/beaconcrypt-authenticated-root-completion`, branch `codex/full-proof-composition`, pushed to `origin` (`ssh://git.mschn.fr/amn/beaconcrypt`). All work described here is committed and pushed; the last commit before this handover is `2c1fe00`.
- The main checkout `/home/user/beaconcrypt` (branch `vcvio`) and every other worktree must not be modified.
- The plan and the running record of every decision is `doc/impl/audit-0b4039e-remediation-plan.md`: section 1 summarizes `0b4039e..2bccc01`, section 2 the Appendix A checks, section 3 the status of F1-F16 at the start, sections 4-8 the milestone plans with status paragraphs appended after each pass.
- Plain-English explanations of every new proof are in `doc/formal-verification-analysis.md`, sections "Audit remediation A", "Audit remediation D" (four sections), "Audit remediation B" and "Audit remediation C" (with the subsection "First-record confidentiality (S7)"). The trust-boundary inventory entries are in `beaconcrypt-core/proofs/trusted-boundary.md` under the same headings, and short summaries are in `doc/formal-verification.md`.

## The assignment

The owner asked for Step 0 (re-baseline: summarize `0b4039e..HEAD`, give the status of F1-F16 with evidence, redo the Appendix A axiom sweep and reachability including HB-126/127, and write a plan in `doc/impl/`) and four milestones: A (F3 query placement, F4 disclosure of the BLAKE2b random oracle at claim sites, F8/F12/F15 wording), B (server authentication, F1), C (record confidentiality and integrity for one preselected session and position, with replay rejection combined with the integrity bound, F7), and D (F5 bridges of hand-written glue to the extracted code, F6 a jointly satisfying instance and `decap_encap`). Rules for every statement: only `propext`, `Classical.choice` and `Quot.sound`, with a repository-form `#guard_msgs` / `#print axioms` guard on every public theorem; bound terms are advantages of constructed reductions, never "for all adversaries" premises; secrets sampled inside experiments; new assumptions generic, with plausibility notes and literature, listed in both assumption lists, and approved by the owner before use; adversary restrictions justified; existing theorems never weakened or deleted; artifacts never silently regenerated; plain-English explanations in `doc/formal-verification-analysis.md`; no mid-sentence line breaks in Markdown. `AGENTS.md` applies, except that `nix-collect-garbage` must never be run because other agents share the Nix store. Commits are focused, with short imperative sentence-case subjects and the footer `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`, without history rewrites, pushed after each milestone.

## Owner decisions and feedback given during the work

- Cap'n Proto and serialization are completely out of scope (2026-09-28): nothing may be proved about them or rely on their behaviour. Messages are arbitrary byte strings that each side knows how to decode; only abstract message-model premises (such as `ReadWritable` and read-back laws) are allowed. An earlier codec-based justification was removed in `f8bae7b`.
- Milestone B route R1 (2026-09-29): zero-salt HKDF-Extract on 192-byte inputs as a programmable random oracle, Gap-DH on X25519 via the existing `PqxdhJointGapDh.game`, and the X25519 class law. Signal's PQXDH specification assumes Gap-DH, and the CTX proofs are already in the random-oracle model.
- No key-compromise-impersonation resistance is wanted. Partnering is by identical root derivation. The Server-session budget is a parameter evaluated at a few tens. Experiment design choices must follow the Rust reference implementation, because both the protocol and its reference implementation are being proved.
- Persistence is out of scope and inaccessible to the attacker; the attacker has no access to the running code, so getters that return secrets need no assumption; libsodium is the canonical library, assumed correct, and nothing is proved about it (2026-09-29).
- Approved on 2026-09-30: the `X25519ScalarSpread` and `NonzeroHonestDh` functional contracts, two Server oracles (accept and build, as the public Rust `ProviderServer` trait), and describing the Gap-DH assumption as a twist-inclusive strengthening of Gap-DH (plausibility: Signal's assumption and Curve25519's twist security).
- Full verification may be run (2026-09-29). The work was paused on 2026-09-30 because of limited credit, with a request for these handover notes.

## Step 0

Commit `e5a5ce1` records the re-baseline in the plan (sections 1-3). The range `0b4039e..2bccc01` added HB-126 and HB-127 (71 Lean modules, 642 guarded statements). The axiom sweep over the full `BeaconcryptCore` import closure (46,208 constants) found only the three standard axioms, and the reachability traversal showed that no headline statement reached the hand-written stand-ins' extracted counterparts (`validate_init_kex`, `server_accept`, `server_prepare_commit` and others), which is finding F5. All sixteen findings still applied at `2bccc01`; the table in section 3 has the evidence.

## Milestone A (complete)

- F3 (`ce0255f`): the exact `BeaconAnyCommitted` query moved to `exact-registration-origin-queries.pvl`, where the alias checker requires it TRUE under the canonical theory and FALSE with a reconstructed trace under the alias theory; `main-registration-controls` now requires the property over the HB-89 eleven-field projection. `check-results.awk`, `check-phase2-x25519-alias.py`, the transcript-fidelity test hashes and the claims in `doc/formal-verification-analysis.md` and `beaconcrypt-core/README.md` were updated.
- F4, F8, F12, F15 (`3e60e96`, `125fc87`): the BLAKE2b random oracle is disclosed at every HB-111/112/126/127 claim site; the correlated Extract family is described as a generic split-key PRF game with a plausibility note, and the consolidated assumption list gained the joint Ed25519/X25519 contract and the other games; the CTX wording and the stale counts and phrases were corrected.
- The Milestone B design request (`a0b31a7`) and the composition-table row (`490242c`) were written during this pass.
- Verified on 2026-09-28 with `verify-in-shell` and `check-inventory` (exit 0, about 58 minutes).

## Milestone D (complete)

- F6 (`6de6bae`): `PqxdhHypothesisWitness` proves every HB-111 and HB-112 premise on one instance, with `rfl` lemmas showing the actual games ignore the ideal model's KEM fields; `decap_encap` is documented as unused by any headline statement.
- F5, first pass (`74b89ec`): `PqxdhHeadlineBridges` proves bridges B1-B11 between the hand-written stand-ins and `server_prepare_commit`, `server_commit`, `beacon_start`, `beacon_commit`, `registration_id`, `build_commitment_transcript`, `SendSeal.finish`, `OpenFrameContext.from_frame`, `validate_init_kex` and `server_accept`, restates HB-111/112 with them as conjuncts, and adds experiments that execute the extracted acceptance with an unchanged output distribution.
- F5, record opening (`c047be9`): `PqxdhOpenBridges` bridge B12 equates the experiments' opening step with `executeOpen`, a hand-written transcription of the unextracted adapter function `execute_open` that calls the extracted `begin_open`, `OpenCommitment` and `OpenAead` phases. The transcription and its `memcmp` comparison are reviewed adapter-level trust (entries OR-10 and PL-11 of the trust-boundary inventory).
- F5, receive path (`76ffee9`, `f18cddd`): `PqxdhOpenContextBridge` proves the extracted `begin_receive` and `ReceiveKdf.resume` are natural in the context type and relates hand-written transcriptions of the post-decoding part of `decrypt_message_with_ratchet` to the experiments' receive driver; `PqxdhReceiveHeadlineBridges` conjoins these bridges with the four headline restatements.
- Remaining F5 gaps, all documented: frame decoding and `finish_frame_read` (out of scope under the message model), the realization of the KDF query by `ratchet_hkdf`, the composition with HB-112's symbolic chain receive driver, and the fact that the experiments still run the hand-written programs with the bridges as proved conjuncts.

## Milestone C (complete for Beacon `b`'s first record)

- Integrity chain: `PqxdhFirstRecordTarget` (`2785b4d`), `PqxdhSelectedFirstRecord` (`0d340a7`), `PqxdhFirstRecordNonceStop` (`f17e14d`), `PqxdhFirstBeaconRecordIntegrity` (`6be8915`), `PqxdhFirstRecordStopBound` (`e3f545a`), `PqxdhFirstBeaconRecordCtx` (`175a364`, `first_beacon_record_integrity` with two game terms), `PqxdhFirstBeaconRecordCanonical` (`58d5eb8`, `f8bae7b`, bounds the gap term by 2^-256 for a canonical forgery event under the message-model premise `ReadWritable`), `PqxdhFirstRecordStopTagged` (`bcf17fd`, bounds the nonce-repeat term by (1 + sends + 51 (raw receives + finishes)) / 2^256; `first_beacon_record_integrity_stop` has no game term).
- Replay, F7 for records (`d6016a3`): `PqxdhFirstRecordReplay.first_beacon_record_integrity_replay` bounds a forgery or any reacceptance at the registered Server peer by the same right side; `no_reacceptance` proves that no reachable run reaccepts a sequence number.
- Confidentiality (`2497992`, `e4bf4f6`, `1c9aa50`): `PqxdhFirstRecordConfidentiality.first_record_confidentiality` is single-challenge adaptive left-or-right confidentiality of the first record, with equal-length plaintexts, a fresh sequence-one challenge, undisclosure of the selected chain and key, and replayable-CCA-style suppression of receive replies equal to a challenge plaintext, each restriction justified and a negative control included. `PqxdhFirstRecordKeyBound` bounds its key-recovery term and `PqxdhFirstRecordFinishBound` its finish-collision term; `PqxdhFirstRecordConfidentialityComplete.first_record_confidentiality_complete` states the result with only constructed-reduction losses and explicit numbers.
- Not covered: Server-owned targets, records after the first, and the registration half of F7 (the consumed-registration set lives only in unextracted adapter code).
- Verified at `1c9aa50` on 2026-09-29 together with Milestone D: `verify-in-shell` and `check-inventory` both exited 0 (about 50 minutes) and the worktree was unchanged afterwards (`7a9190f` records the run). An earlier intermediate run failed only in `check-inventory`, because a generated gate did not escape a `?` in a theorem name; `9f3cf1a` fixed the generator.

## Milestone B (in progress)

See `milestone-b/README.md`. The design is `doc/impl/server-authentication-design.md`. Seven stages are committed and reviewed (`12d5214`, `884cf49`, `25dd43e`, `07415ba`, `7db487f`, `aec2ee2`, `84feb7d`): the Extract random-oracle patch and table, the assumptions and X25519 contracts, the key-schedule bound, local matching, the experiment and the negative-control gate. B6 (Gap-DH reduction, main result already compiling), B7 and B8b are in progress in `milestone-b/stages/`; B9b, B10a, B10, B5b, B3b/B4b and the documentation stage are not started. No server-authentication theorem is stated yet, and the Milestone B stages have been checked only with `lake build` and `check-inventory`, not with a full `verify` run.

## Status of the audit findings now

| Id | Status |
| --- | --- |
| F1 | In progress (Milestone B). |
| F2 | Not addressed (ProVerif guard processes and fixed sequence schedules); outside the assigned milestones. |
| F3 | Fixed (Milestone A). |
| F4 | Fixed (Milestone A). |
| F5 | Addressed (Milestone D) with the documented residual gaps above. |
| F6 | Fixed (Milestone D). |
| F7 | Fixed for records (first record of Beacon `b`); the registration half remains, because the consumed set is adapter code. |
| F8 | Fixed (Milestone A). |
| F9 | Addressed (Milestone C): integrity, replay rejection and confidentiality for one protocol-derived key. |
| F10 | Not addressed (budget and `noSign`/`noCreate` restrictions of the adversary class). |
| F11 | Not addressed. |
| F12 | Fixed (Milestone A). |
| F13 | Not addressed. |
| F14 | Not addressed. |
| F15 | Fixed (Milestone A). |
| F16 | Not addressed (`check-inventory` is still a separate target, and three older modules still lack axiom guards). |

## Working environment and method

- Lean: `beaconcrypt-core/proofs/lean`, Lean 4.34 with VCVio and Aeneas/Hax extraction. Scratch files compile with `lake env lean <file>`; the library with `lake build BeaconcryptCore` (about 4,550 jobs). The machine has 16 GB shared with other proof agents: run one Lean process at a time (the agents used `flock /tmp/bc-arc-scratch/lean.lock`), and stop idle language-server workers if swap fills.
- Full verification: the `verify` target copies the 20 GB worktree into the Nix store, so the same locked shell was entered through a directory holding only copies of `flake.nix` and `flake.lock`, with a GC root, and `SHELL` set to the shell's bash because the Makefile hard-codes `/bin/bash`, which this host lacks. The exact command is in `milestone-b/README.md`.
- Every new module was checked by two or three independent adversarial reviewers with distinct lenses, with a refutation pass on every serious finding, before it was committed; `milestone-b/review-templates/review-three-lens.js` is the workflow used. Integration steps and inventory pitfalls are in `milestone-b/README.md`; the helper scripts are in `milestone-b/tools/`.

## Commits of this work, in order

`e5a5ce1` re-baseline and plan; `ce0255f`, `3e60e96`, `125fc87` Milestone A; `a0b31a7`, `490242c` Milestone B design request and table row; `6de6bae`, `74b89ec` Milestone D first pass; `2785b4d`, `0d340a7`, `f17e14d`, `6be8915`, `e3f545a`, `175a364`, `9f3cf1a`, `58d5eb8`, `f8bae7b`, `bcf17fd`, `d6016a3` Milestone C integrity and replay; `c047be9`, `76ffee9`, `f18cddd` Milestone D record opening and receive path; `1a9c05e`, `39f0e28`, `a18cdcc`, `fbe31f9` Milestone B decisions and grounding; `2497992`, `e4bf4f6`, `1c9aa50` Milestone C confidentiality; `7a9190f` verification record; `12d5214`, `884cf49`, `25dd43e`, `07415ba`, `7db487f`, `aec2ee2`, `84feb7d` Milestone B stages; `12d9308`, `2c1fe00` Milestone B checkpoint and handover.
