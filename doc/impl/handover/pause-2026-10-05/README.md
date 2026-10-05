# beaconcrypt formal verification: handoff of 2026-10-05

Draft written on 2026-10-05 at about 21:30 +02:00 by a read-only subagent of the orchestrating Claude session `8a771e85-7234-5670-9e9c-438d4cb1f12f`. Sources: the three fact files next to this README (`facts-pin-and-lanes.md`, `facts-proverif.md`, `facts-process.md`, collected 19:05-19:15), plus fresh read-only checks made while writing (`git log/show/ls-remote/merge-base`, file reads, the finished AnyPin pass in `/tmp/bc-arc-scratch/pv-work/p3-anypin/final/`). No worktree was edited, nothing was committed or pushed, and no ProVerif, Lean, Nix or `make` command was run for this document. Anything that could not be confirmed from a file or from git is marked **[unverified]**. This file is not committed anywhere; it lives only under `/tmp/bc-arc-scratch/handoff-2026-10-05/`.

## 1. Start here

The effort proves the beaconcrypt PQXDH protocol and its Rust reference implementation. Codex worked on it until 2026-10-01 and left the pause handoff `doc/impl/handover/pause-2026-10-01/README.md` in the central worktree `/tmp/beaconcrypt-authenticated-root-completion` (branch `codex/full-proof-composition`). Claude resumed on 2026-10-02 at `959cdab` and did three things. (1) It aligned the registration models with Rust after the owner ruled on 2026-10-03 that "the code is authoritative": the Lean `parsePin` no longer requires `checks.identityPoint`, and ProVerif `JointCreate` no longer has the matching creation gate. This touched eight branches, all reviewed and published. (2) It continued four paused Lean lanes (joint services, symbolic schedule, R1 restriction, evolving record) far enough to publish reviewed cohorts; none of these lanes is merged into central. (3) Following the owner's 2026-10-02 priority for ProVerif (audit findings F2, then F13, then F11), it built a new bounded "free-schedule" (fs) ProVerif group in stages: P0 (scoping spike, gate G0), P1 `fs-registration`, P2 `fs-records-s2b` and P3 `fs-records-b2s`. P1 and P2 are reviewed, published and fast-forwarded into central (`d937aab`). P3 is local only.

**Published versus local.** Every branch Claude touched is on `origin` (`ssh://git@git.mschn.fr/amn/beaconcrypt`) with local = remote. P3 `codex/proverif-fs-records-b2s` was published at `287be25` on 2026-10-05 after its confirming review, and central `codex/full-proof-composition` was fast-forwarded from `d937aab` to `287be25` (both verified with `git ls-remote`).

**Running or paused.** Nothing is running. The owner asked on 2026-10-05 to pause and prepare this handoff, so do not resume proof work without a new owner instruction. The last job, the full serial fs pass on `974eedf` (P3 AnyPin follow-up), finished at 2026-10-05 20:28:58 with exit status 0 and 49/49 exact results; it was recorded in `00ad609`, confirmed by a two-lens review (both APPROVE_WITH_NITS), the nits were fixed in `287be25`, and P3 was published (section 4.3.6). No Lean job is running; the only Lean processes on the machine are long-lived `lake serve` / `lean --server` language servers of the MCP tools, not proof jobs.

**First actions for a new agent.** Read `AGENTS.md`, the central pause README `doc/impl/handover/pause-2026-10-01/README.md` (its resumption log points here), then this file. Check refs with `git ls-remote` and every worktree's `git status` before doing anything. Then follow section 7 in order; P3 is finished and published, so the first open item is the OD7 budget decision before any P4-P8 target.

## 2. Owner decisions and constraints in force

Sources: the memory files in `/home/user/.claude/projects/-home-user-beaconcrypt/memory/`, the central pause README, the ProVerif plan §7.1 and `p0/s2b/NOTES.md:78`. Later decisions override earlier plans.

| Date | Decision or constraint | Where recorded |
| --- | --- | --- |
| 2026-09-27 | Never run `nix-collect-garbage` (AGENTS.md says to; the owner overrides it; ask first). Use the Lean and Rust MCP servers freely. Prefer subagents for bulk reading; run at most 3-4 subagents at once (even 3 hit the usage limit on 2026-10-02) and have each write a timestamped `NOTES.md` immediately so it can be resumed. | `shared-machine-compute-limits.md`, `prefer-subagents-for-exploration.md`, `subagent-concurrency-limit.md` |
| 2026-09-27 | If auto-mode blocks tool calls mid-session, do not retry; stop and tell the owner the options. | `auto-mode-classifier-blocks-audit.md` (not listed in `MEMORY.md`) |
| 2026-09-28 | Cap'n Proto is out of scope: messages are abstract byte strings each side can decode; never cite capnp internals. Enter the proof shell only through the two-file flake copy, never `nix develop path:<worktree>` or `make verify` (each copies about 20 GB into the store). | `codec-out-of-scope.md`, `proof-shell-minimal-flake.md` |
| 2026-09-29 | "We are proving the protocol AND its reference implementation": experiment design (reveals, partnering) must follow the Rust code with file:line evidence. Out of scope: persistence, attacker access to the running code, libsodium internals (libsodium is a correct black box; assumptions such as Gap-DH are stated on its functions). Milestone B: route R1 (Extract ROM + Gap-DH), no KCI resistance. | `ground-proofs-in-rust-source.md`, `proof-scope-exclusions.md` |
| 2026-10-01 or earlier (Codex era) | Mutation testing is required only for Rust changes. Nothing under `beaconcrypt/src` or `beaconcrypt-core/src` changed since `959cdab` (`git diff --stat 959cdab d937aab` on those paths is empty). Whether the 4,537-line growth of the test file `proverif_transcript_fidelity.rs` counts is **[unverified]**. | central pause README, "Read first" |
| 2026-10-02 | Resume authorised; the two Codex publication holds released (`2f8845e`, `4a9453c` pushed). New commits use the trailer `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. "You can create and publish branches as needed", but publish proof claims only after independent review; fast-forward only, never force-push, verify with `ls-remote`. | pause README resumption log, `branch-publication-permission.md` |
| 2026-10-02 | ProVerif first (F2, then F13, then F11), overall strategy unchanged; Lean lanes continue at lower priority. ProVerif results are symbolic and never presented as computational bounds. | `proverif-priority.md` |
| 2026-10-03 | "The code is authoritative here." When a model and Rust disagree, change the model; never propose Rust changes to fit a model. | `ground-proofs-in-rust-source.md` |
| 2026-10-03 | The proof Server is an idealisation: no backup or restore, perfect key management (keys uniform, independent, never disclosed; secret state never disclosed). Two Server objects built from one seed are one Server identity; replay claims are per live Server state; ProVerif R4 is expected, not a finding. | `proof-scope-exclusions.md`, OD2 |
| 2026-10-03 | ProVerif plan decisions: OD1 bounded (tier B) results are the deliverable, tier U / stage PU dropped (claims U1-U7, C-U-UKS, L7, L8, fallback W never built), closure item 1 stays with Lean. OD2 as above. OD7: 1800 s per target, about 3 h (10800 s) for the serial fs group, 10 GiB address space per run (`ulimit -v 10485760`, raised from the plan's 4 GB). OD11: the serial step-by-step run in the minimal flake shell is the verification record; `make verify` is never run on this machine. | `proverif-priority.md`, `p0/s2b/NOTES.md:78`, plan §7.1 |
| 2026-10-03 | "You're the only one currently working on this machine": use the whole 16 GB machine for one heavy job at a time; Lean and ProVerif may run side by side under their separate locks. Re-check with the owner if other agents reappear. | `shared-machine-compute-limits.md` |
| 2026-10-04 | HB-95: `origin/main` and `vcvio` lack fix `5cbd76e`; the owner said "I'll handle it". Do not port the fix or open branches for `main`/`vcvio` unasked. Keep stating the Rust basis (central branch) in proof claims. | `main-lacks-seq1-fix.md` |
| standing | Lean theorems may depend only on `propext`, `Classical.choice`, `Quot.sound`; each new theorem gets a `#guard_msgs` / `#print axioms` guard copied from actual output; stop and report anything else. No new assumption without owner approval; in ProVerif no `axiom`, and no `restriction` without explicit approval. Never weaken or delete a theorem; fidelity corrections are listed as meaning changes. Explain new or substantially changed proofs in `doc/formal-verification-analysis.md`. Never silently regenerate known-answer or proof artefacts. One paragraph per line in text files. | `c-work/pin-gate/plan.md` lines 70-81 and 612, `proverif-plan.md` line 97, AGENTS.md |
| standing | Never change another agent's worktree or its uncommitted files (dirty submodules, untracked prototypes, WIP) unless that lane was handed over. | pause README, AGENTS.md |

Plan decisions with no owner record found **[unverified]**: OD6 (primitive semantics), OD8 (fate of legacy scenarios), OD9 (whether P7 is in scope), and an owner confirmation of the `959cdab` Rust basis (G0 §10 item 9). OD3 (nx and other features allowlisted), OD4 (far collapse), OD5 (P5 freshness gate) and OD10 (cite fs results as pending until L1-L8 are reviewed) are cited as decisions in the guides. No file records an explicit owner acknowledgement of the pin-width meaning changes M0-M5 (plan §8); the central resumption log only says they are listed in the commit messages **[unverified]**.

## 3. Branch and worktree map

All worktrees share one git directory (`git worktree list` shows 101 worktrees, 224 local branches). Heads re-checked at about 21:25 with `git rev-parse` and `git ls-remote origin`.

| Branch | Head | Published? | Reviewed? | Contents | Worktree |
| --- | --- | --- | --- | --- | --- |
| `codex/full-proof-composition` (central) | `287be25` | yes | each stage reviewed before fast-forward | Codex integration (proof `edc701e`, validation `e410d32`), resumption log `959cdab`, T0a docs `2f4e03e` `a0a67f5` `533901f`, P1 `7518974`..`9e588c6`, P2 `f381479`..`d937aab`, P3 `c122164`..`287be25`. Linear history (fast-forward only). |
| `codex/proverif-fs-records-b2s` (P3) | `287be25` | yes | `c122164`..`b444623`: three lenses + confirming review; `974eedf` + `00ad609`: two-lens confirming review (APPROVE_WITH_NITS), nits fixed in `287be25` | `c122164` scenario, `ddc0a33` pass record, `8323943` review fixes, `b444623` pass record, `974eedf` UKSr and C-UKS pin-free, `00ad609` AnyPin pass record, `287be25` extrapolation and wording fixes. Worktree `/tmp/beaconcrypt-proverif-fs-b2s`. |
| `codex/proverif-fs-records` (P2) | `d937aab` | yes | yes | `f381479`..`d937aab` (s2b scenario, event-meaning reference, L6 review fixes, records, nits) | `/tmp/beaconcrypt-proverif-fs-records` (clean) |
| `codex/proverif-fs-registration` (P1) | `9e588c6` | yes | yes | `7518974`, `1b09dbd`, `f85e7c3`, `487acff`, `9e588c6` | `/tmp/beaconcrypt-proverif-fs` (clean) |
| `codex/pin-fidelity-docs` (T0a) | `533901f` | yes; ancestor of central | RG4 approved with 3 nits, fixed in `a0a67f5` | Server parse-check instance docs and central resumption-log entry | `/tmp/beaconcrypt-pin-fidelity-docs` (clean) |
| `codex/registration-pin-width` (T1) | `8984399` | yes | RG1 reviewed `716c631`; nit fixed in `8984399`; confirming review of `8984399` not recorded **[unverified]** | `716c631` parsePin = width parse + `parsePin_eq_toWord32`; `8984399` "by construction" qualifier | `/tmp/beaconcrypt-registration-pin-width` (clean) |
| `codex/registration-joint-schedule` (base) | `8984399` | yes | as T1 | fast-forward `4f76bbb` -> T1 | `/tmp/beaconcrypt-registration-joint-schedule` (clean) |
| `codex/registration-pin-width-lanes` (T2) | `d2c7b29` | yes | RG2 approved with nits, fixed in `d2c7b29` | `2fd6b56` merge of T1 onto lane base `ae279d7`; `53b8e58` pvl gate removal; `755fa00` ProVerif re-run record; `605420b` key-id doc; `d2c7b29` RG2 nits | `/tmp/beaconcrypt-registration-pin-width-lanes` (clean) |
| `codex/registration-joint-service-composition` | `6ccf4b4` | yes | RG3 (1 minor, 5 nits) fixed in `341c9f7`; confirming nit fixed in `6ccf4b4` | `67b8063` merge of T2, `1b33b5c`, `341c9f7`, `6ccf4b4` on top of Codex milestones | `/tmp/beaconcrypt-registration-joint-service-composition` (clean) |
| `codex/registration-symbolic-schedule` | `5b28f90` | yes | RG3 (2 nits) fixed in `5b28f90`; confirming review of `5b28f90` not found **[unverified]** | `02b7e4e` merge of T2, `c637a52`, `5b28f90` on top of Accept31/CommonReceipt31 | `/tmp/beaconcrypt-registration-symbolic-schedule` (10 untracked Codex prototype files: keep byte for byte) |
| `codex/registration-r1-common-restriction` | `204eff7` | yes | 49-statement cohort reviewed at `fdb3169` (two lenses, no statement defect) and `65362dc` (prose); RG3 (2 minor, 6 nits) fixed in `f870350`; confirming nits fixed in `204eff7`; step-6 reviews outstanding | `b9acda2`, `d5a6ffd` merge of T2, `2708919`, `db60df8`, `f870350`, `204eff7` | `/tmp/beaconcrypt-registration-r1-common-restriction` (clean) |
| `codex/evolving-record-composition` | `6ae17ba` | yes | two reviews of `59a9803`; re-review of `9d9a4d6`; confirming review of `a913a00` APPROVE_WITH_NITS, fixed in `6ae17ba` | `59a9803` five modules, 33 guarded statements; `9d9a4d6`, `a913a00`, `6ae17ba` | `/tmp/beaconcrypt-evolving-record-composition` (clean) |
| `codex/evolving-record-pause-2026-10-01` | `b4fce6d` | yes (2026-10-02 19:43; the pause README still calls it local-only) | Codex archive | Codex pause archive | `/tmp/beaconcrypt-evolving-record-pause-2026-10-01` |
| `codex/server-auth-publication-composition` | `adabe9a` | yes | Codex | Source of the 109 modules for R1 step 4 (do not edit) | not touched by Claude |
| `vcvio` / `main` | `8330cde` / `61df284` | yes | n/a | Product branches; both lack `5cbd76e` (HB-95) | `/home/user/beaconcrypt` (branch `vcvio`, two untracked owner files from 2026-09-06 **[owner's, unverified]**): do not touch |

Not created: the T0b branch `codex/server-check-docstrings` and worktree `/tmp/beaconcrypt-server-check-docstrings` (confirmed absent locally and on origin).

Merge-bases with central `d937aab` (re-checked): every registration branch `bb7b67e`; `codex/evolving-record-composition` `e22e83d`; `codex/pin-fidelity-docs` is an ancestor. No registration or evolving lane is merged into central.

Other worktrees, do not touch: `/home/user/worktrees/beaconcrypt-proof-audit` (detached `0b4039e`, untracked audit report `doc/impl/proof-audit-0b4039e.md`; commit only if asked), `/home/user/worktrees/beaconcrypt-vcvio-lean-4.34` (`7e996e5`), and 85 Codex `/tmp/beaconcrypt-*` worktrees with HEADs dated 2026-09-05..2026-10-01, several heavily dirty. `/tmp/beaconcrypt-server-auth-common-integration` (`e410d32`) is the clean integration worktree named in the pause README.

## 4. Work done

### 4.1 Registration pin-width alignment (2026-10-03 to 2026-10-04)

**Trigger and ruling.** The 2026-10-03 review of the R1 lane (review-fix item 2, recorded at `65362dc` and in the R1 handover README) found that the registration scheduler model refused Beacon creation unless the pinned Server key passed `checks.identityPoint`. Rust does not: `Beacon::try_new` (central `beaconcrypt/src/beacon.rs:65-82`) runs `ensure_init`, calls libsodium-rs 0.2.4 `crypto_sign::PublicKey::from_bytes` (length check only) and draws the identity, prekey and ML-KEM keys. A pin that `ed25519_pk_to_curve25519` rejects is noticed only in `finish_registration`: at the conversion of the response identity (beacon.rs:432) or at the core byte comparison with the pin (`beaconcrypt-core/src/pqxdh.rs:545`, `IdentityMismatch`). A finish before the bundle returns `None` and leaves the Beacon unchanged (beacon.rs:403-406); the first InitSent finish aborts it. The owner ruled "The code is authoritative here"; the models were changed, Rust was not. Scratch plan: `/tmp/bc-arc-scratch/c-work/pin-gate/plan.md` (including §11).

**Lean change.** Old (`4f76bbb`, `PqxdhRegistrationScheduleSurface.lean:14-17`): `parsePin checks bytes := do let pin ← toWord32 bytes; if checks.identityPoint (PqxdhPhase2GapDhSource.peer pin) then some pin else none`. New (`8984399`): `def parsePin (_checks : Checks) (bytes : Pqxdh.Bytes) : Option Word32 := toWord32 bytes`, plus `theorem parsePin_eq_toWord32 (checks) (bytes) : parsePin checks bytes = toWord32 bytes := rfl` with axiom guard `[propext, Classical.choice, Quot.sound]` copied from `t1-logs/print-axioms.out`. `rawCreate` body unchanged (docstrings corrected); Phase 2 and finish unchanged, and they refuse such a Beacon at the same two places as Rust "by construction" (not a separate theorem). Statement counts 80 -> 81, "eight" -> "nine".

**R1 lane change.** `parse_public` now states `parsePin checks identity.toList = some (rootArray identity)` for every `checks` (the only statement-text change, M3); `prefixAudit`/`prefixAuditWith` lost their `identityPoint` branch; `initial_audit`/`initialWith_audit` proofs dropped `split_ifs`/`case neg` and two unused simp arguments.

**ProVerif change.** `JointCreate` in `beaconcrypt-core/proofs/pro-verif/registration-joint-schedule.pvl` lost `let converted_pin = x25519_public_from_ed(pin)` (introduced by shared commit `555af15`). File sha256: `95bf6774…` at `ae279d7`, `48bf5571…` at `53b8e58`, `089453df93203901343b954b88a1e8e63b27a89f3b869ca3113206d65fd66beb` at `d2c7b29` (same on all three lane heads). Re-run: joint operational correspondences 3/3; unread-reply control 2/2 with reconstructed trace; serial-output sensitivity explicitly inconclusive; 18.82 s, 1.09 GB. Logs `pin-gate/pv-t2/` (comment-only re-run `pv-t2-comment/`); 16/16 checker regression tests pass.

**Meaning changes** (no statement deleted or weakened, no assumption added, no Rust change, hence no mutation run):

- M0: every statement about the raw creation surface keeps its text but now also covers a Beacon with a 32-byte non-point pin that is created, publishes bundles and is accepted and built by the Server, and no longer covers the old refusal. Counts (regenerated with `pin-gate/tmp/leandecls.py taint`): 14 at T1, 66 more in the 29 shared modules at `ae279d7`, 27 more in the symbolic lane, 10 more in R1, none in services; lane totals service 80, symbolic 107, R1 90, each plus `parsePin_eq_toWord32`. `route_source`, `route_program` (R1) and `surface_call_source` are in the textual M0 list but their meaning is literally unchanged.
- M1: in `rawCreate_continuation` and `rawCreate_cases` "the pin parsed" now means only "32 bytes"; `rawCreate_cases` no longer yields `checks.identityPoint pin` (no consumer used it; `PendingSurface.surface_step` ignores it).
- M2: `surfaceLabel`, `SurfaceClass`, `surface_relation`, `surface_count` label and count every 32-byte create request; `IsAccept`/`IsBuild` unchanged.
- M3: R1 `parse_public` text (above).
- M4: in R1 `initial_audit`, `initialWith_audit`, `experiment_audit`, `experimentWith_audit`, `experiment_journal`, `PrefixOutcome.rejected` now arises only from initialization failure (Server construction can still refuse on a failed first initialization or a wrong-width supplied seed).
- M5: ProVerif `JointCreate` now creates Beacons for pins that are not `ed_public` terms; verdicts unchanged (3/3). Uncommitted diagnostic `pin-gate/pv-t2/badpin/` checks `not event(JointCreated(i,bad_pin,s))`: true on the old file, "cannot be proved" on the new one (derivation and trace under a hypothesis, no unconditional trace); the default-settings run on the new file timed out at 600 s using 8.8 GB.

**Central Server checks (T0a, Markdown only, `2f4e03e`, `a0a67f5`).** `doc/impl/server-authentication-design.md:122` at `d937aab`: `identityPoint`, `x25519Point`, `beaconIdentity` sit at length-only libsodium-rs `from_bytes` calls (server.rs:342, :362-367, :452-453), so their Rust instance is constantly `true`; `kemKey` is the ML-KEM encapsulation-key admission inside `crypto_kem::mlkem768::encapsulate` (server.rs:373), not `true`. Review rule: no theorem may assume `identityPoint`, `x25519Point` or `beaconIdentity` returns `false`; a `kemKey = false` hypothesis is admissible only for keys ML-KEM encapsulation rejects. The Lean docstring counterpart (T0b) is deferred (section 7).

**Timeline** (commit times, +02:00). 2026-10-03: 15:33 `716c631`, 15:41 `8984399` (both pushed 15:41:55 with the base fast-forward); T2 15:43 `2fd6b56`, 15:46 `53b8e58`, 16:02 `755fa00`, 19:22 `605420b`, 19:32 `d2c7b29` (pushed 19:32:48); 19:36-19:49 lane merges and lane commits. 2026-10-04: 00:26-00:41 RG3 follow-ups (lanes pushed 00:41:41-43); 00:41 retired helpers rewritten; 00:45-00:55 T0a (pushed 00:55:30, central pushed at `533901f` 00:55:31).

**Rechecks after the alignment** (helpers in section 6.2): T1 4/4 modules exit 0 after `8984399`; T2 29/29 (218 existing guards unchanged + 1 new); joint services 32/32 (247 guards, 2026-10-03 19:38-19:46); symbolic 45/45 (281 guards unchanged + 1 new); R1 34/34 (268 guards; R1Surface and R1Journal rechecked after `f870350`, sources equal `204eff7`). I re-counted the `pass` lines in each `status.tsv` (29, 32, 45, 34) against `downstream.txt` today. No commit after these rechecks changed a `.lean` file.

### 4.2 Lean lanes (lower priority since 2026-10-02)

**Joint services** (`codex/registration-joint-service-composition` at `6ccf4b4`; lane handover `doc/impl/handover/pause-2026-10-01/joint-services/README.md` in that worktree). Published milestones: Creation9 `22580c5`, Bundle11 `59fbc69`, Preparation21 `f88498a`, Finish15 `290ee8c`, Compiler5 `fad3306`/`871d186` (approved without findings 2026-10-02), CompiledOwner8 `8fd99de` with nit follow-up `4574a46` (approved with nits by two lenses). No Lean error or placeholder remains. Six CompiledOwner8 names coincide with `PqxdhRegistrationJointFinish` names and two with `PqxdhRegistrationSchedule` names: use qualified names or selective `open`s.

**Symbolic schedule** (`codex/registration-symbolic-schedule` at `5b28f90`; handover `doc/impl/handover/pause-2026-10-01/registration-schedule/README.md` and `review-status.json`). Accept31 approved. CommonReceipt31 plus corollary `prefix_build_field` (32 guarded statements) approved with nits by receipt-a, receipt-b and the correction review. The source surface has nine capabilities; the symbolic process has five. Central wiring would need 8+8 imports and 31+32 guards.

**R1 restriction** (`codex/registration-r1-common-restriction` at `204eff7`; handover `doc/impl/handover/pause-2026-10-01/r1-restriction/README.md` and `manifest.json`). Five modules, 49 guarded statements: Restriction 16, Audit 10, Initial 6, Surface 6, Journal 11. Step 3 done; steps 4-6 not started. The guide `doc/impl/registration-r1-restriction.md` does not exist yet (checked).

**Evolving record** (`codex/evolving-record-composition` at `6ae17ba`; notes `/tmp/beaconcrypt-evolving-record-check/resume-2026-10-02/NOTES.md`; guide `doc/impl/later-challenge-saved-classification.md`). 33 guarded statements: SavedMonitor 12, BuilderContinuation 4, PreparedContinuation 2, GeneratedContinuation 9, SavedClassification 6. Not affected by the pin alignment (no `PqxdhRegistrationSchedule*` module in its tree). Sources equal `logs/review-sources.sha256`; GeneratedContinuation and SavedClassification exited 0 on 2026-10-03 19:24. Refer to every declaration of the five modules by its qualified name.

Next steps for each lane are in section 7.2.

### 4.3 ProVerif free-schedule group (P0-P3)

Every fs result is symbolic (Dolev-Yao attacker, free constructors, ideal hash, KDF and AEAD) for a bounded process. None is a computational bound, and none discharges global closure item 1 (arbitrary reached committed states). The checker demands the exact result line, one trace for FALSE and none for TRUE, and rejects "cannot be proved", unknown, inconclusive and any warning except `Termination warning:`. Only results classed "security" count as evidence.

**Sources.** Plan `/tmp/bc-arc-scratch/pv-work/design/proverif-plan.md` revision 2 (§5 stages, §6 L1-L8, §7.1 OD1-OD11; revision 1 `proverif-plan.rev1.md`). G0 report `/tmp/bc-arc-scratch/pv-work/p0/G0-report.md`. Guides in the repo: `doc/impl/proverif-free-schedule-registration.md` (P1), `doc/impl/proverif-free-schedule-records.md` (P2), `doc/impl/proverif-free-schedule-records-b2s.md` (P3, b2s branch only), `doc/proverif-fs-event-meaning.md`. Analysis sections in `doc/formal-verification-analysis.md` (b2s worktree line numbers): line 3438 fs-registration (with nx, declaration policy, precision and output settings), 3516 s2b, 3562 b2s.

**Change size.** `533901f..974eedf` touches 85 files (+11395/-12). Added: `check-free-schedule.py`, `test-free-schedule-checker.py`, `declaration-allowlist.tsv`, `fs-common.pvl`, eight control libraries `fs-control-{nocheck,uks,retain,stale,failmut,nogate,b2s-retain,b2s-stale}.pvl`, the registration, s2b and b2s libraries with 13, 11 and 14 query files, and the four documents above. Modified: `beaconcrypt-core/{Makefile,README.md}`, `proofs/check-inventory.sh`, `reviewed-inventory.txt`, `trusted-boundary.md`, `tests/proverif_transcript_fidelity.rs`, `doc/formal-verification-analysis.md`. Legacy scenarios, `crypto.pvl`, `environment.pvl` and `production-transcript-interface.pvl` are not edited.

#### 4.3.1 P0 spike and gate G0 (2026-10-03 to 2026-10-04)

193 runs, 56288 s, parts in `pv-work/p0/{s2b,b2s,p0.3,p0.5-6,l6,g0-tools}` (theory files in `p0/p0.3/lib/`). Binding outcomes: theory stays `crypto.pvl` (T0), because T1 and T2 ran out of memory at 10 GiB on every registration cell (168-420 times the T0 cost; A1 failed even at K_reg = 1), and t1enc fits registration only at K_reg = 2 (8 claims, 198.4 s, under 2.3 GB; A2 out of memory at K_reg = 3 after 226.09 s), so F13 stays partly open. Self-contained `fs-common.pvl` loader. The nx heuristic `nounif y: bitstring; attacker(x25519_public(y)).` is needed everywhere (it prevents a legitimate-attacker divergence, not an attack). Accepted model steps: v2 early-fresh coins, reg-v2 process-level lets, na names (b2s Beacon records only), fail-stop (two b2s targets). C-UKS on C2 came out TRUE, so the record-form C-UKS target is the new query UKSr. C5 and R5 witnesses are correspondences expected FALSE (ProVerif 2.05 rejects time inequalities in reachability queries and crashes on a nat inequality in a temporal premise). Larger grid not achieved (each extra receive attempt multiplies process size by about 6-10). No protocol attack in 193 runs; the only real-behaviour trace is HB-95 on `vcvio` (section 5.1).

#### 4.3.2 Model shape

Unbounded Server objects share `SERVER_IDENTITY_SECRET` (private) and `SERVER_KEY_ID` (`fs-common.pvl:36-37`), each keeping state in process variables of a non-replicated step chain. Unbounded honest Beacons make one bundle and at most one finish, aborting for good on any failure. Unbounded attacker identities are built from public constructors and served by the same Server code. No origin tables, guard, `MaliciousServer`, axiom, restriction or lemma; honesty appears only as the `attacker(k)` disjunct in queries; every attacker input is `[precise]`. Vocabulary (`fs-common.pvl`): `fs_kid(nat)` for `server_kid + n` (first peer `fs_kid(1)`), `fs_seq(nat)`; twelve events `FsBeaconStarted`, `FsServerAccepted`, `FsServerReplayRejected`, `FsServerAcceptFailed`, `FsServerCommitted`, `FsBeaconEstablished`, `FsBeaconFinishOpenedLater`, `FsSent` (sequence allocation), `FsReceived`, `FsReceivedFrame`, `FsFarAccepted`, `FsReceiveRejected` (carries the refused frame); nx at line 228.

- fs-registration: K_reg bundles per object in Rust order, nat key-ID counter, two consumed slots; after each accept the attacker chooses build or drop. Security at K_reg = 3; no record traffic; finish opens seq 1 only; no all-zero check (vacuous under T0).
- fs-records-s2b, (K_s, K_r, T_max) = (2, 3, 3): one bundle per object, key ID `fs_kid(1)`, v2 coins; taskings at seq 2 and 3 in "fresh" form (adversary 8-byte prefix + fresh bytes) or "chosen" form; Beacon finish opens seq 1..T_max before the gate, then K_r attempts from r = 1 with window, swap removal and exact entry state on failure; far branch above T_max uses model-only `fs_far_chain(chain_4, t)`, emits only `FsFarAccepted` and stops. Direction split E19: no Beacon send worker, no Server receive worker.
- fs-records-b2s, (2, 3, 2): Server makes K_r attempts from r = 0, routing on claimed sender `fs_kid(1)` (only AEAD and CTX separate peers); Beacon finishes at seq 1 then sends seq 1 and 2; far anchor `chain_3`. Two main processes: `FsRecordsB2sMain` (every Beacon pins the honest key and ID) and `FsRecordsB2sMainAnyPin` (attacker chooses every Beacon's pin). Bound files `-kr1/2/3` (failure-interleaving) and `-kr3-failstop`. Send forms fresh (na) and chosen.

Not covered: a 4th bundle per object; s2b 3rd tasking or 4th Beacon receive; b2s 3rd record or 4th Server receive; anything after a direction's first far acceptance; arbitrary reached states; P5, P7, F13 primitives; non-fresh registration payloads (including the default 0xFF); Server objects with another key or `server_kid` (E23); L1 case (iv); codec, persistence, process access, libsodium internals. S1, S2 and UKSr cover fresh plaintexts only. In s2b, A1, C1, C3, C4 and S3-beacon hold only for Beacons that pin the honest key.

#### 4.3.3 P1 fs-registration (published, `9e588c6`)

15 targets. Security at K_reg = 3: A1 (injective registration agreement, honest pins, runs without later records), A2 (bundle origin, pin free, corruption disjunct), R1, R1', S3-server (on `FsServerCommitted`), S3-beacon. Definitional R2 (K_reg = 2). Witnesses R3, R5, W2 (K_reg = 2), W1, W3 (K_reg = 1). Limitation R4 (honest-bundle premise; the disjunct form gave "cannot be proved"). Controls C-NOCHECK on R1 (K_reg = 2), C-UKS on A1 (K_reg = 1). Record pass on tree `f85e7c3` (+ log-name fix), recorded in `487acff`, 2026-10-04 18:09-18:53: 2614.0 s ProVerif, 2642.0 s wall (`pv-work/p1-fix/final2`). Reviews: three lenses (5 minor, 11 nit) fixed in `f85e7c3`; confirmation nits in `9e588c6`.

| Target | Time (s) | Target | Time (s) |
| --- | --- | --- | --- |
| A1 | 1029.12 | R2 | 2.44 |
| A2 | 113.69 | R3 | 1.49 |
| R1 | 413.70 | R5 | 2.69 |
| R1' | 582.24 | W1 | 0.07 |
| S3-server | 86.24 | W2 | 2.01 |
| S3-beacon | 378.41 | W3 | 0.04 |
| R4 | 0.04 | C-NOCHECK | 1.70 |
| | | C-UKS | 0.08 |

#### 4.3.4 P2 fs-records-s2b (published, `d937aab`)

16 targets. Security at K_r = 3: A1, A2, C1, C3, C4 in chosen form, S1 in fresh form (A2 and S1 pin-free). Witnesses A3, S4, C5c (K_r = 1), C5a, C5b (K_r = 2). Controls C-RETAIN on C1 and C3, C-STALE (K_r = 3), C-NOGATE (K_r = 1), C-FAILMUT (K_r = 2, inverted, TRUE expected). Record pass on tree `f18a089`, recorded in `34b5fe2`, 2026-10-05 02:09-03:52: 31/31 exact; registration 2641.5 s + s2b 3521.2 s = 6162.7 s ProVerif, 6194.1 s wall, 57% of OD7 (`pv-work/p2-fix/final`). Fail-stop measured (about 4 times cheaper) but not used in s2b. Reviews: L6 review applied in `dedd82f`; three P2 lenses (5 minor, 9 nit) fixed in `f18a089` (C5c became a genuine replay witness); confirmation nits in `500a7d9` and `d937aab`.

| Target | Time (s) | Target | Time (s) |
| --- | --- | --- | --- |
| A1 | 0.70 | A3 | 0.16 |
| A2 | 0.83 | C5a | 19.16 |
| C1 | 1086.85 (VmPeak 6974088 KiB, 66.5%) | C5b | 25.64 |
| C3 | 942.87 | C5c | 0.90 |
| C4 | 231.65 | S4 | 0.11 |
| S1 | 0.54 | C-RETAIN-C1 | 443.17 |
| C-NOGATE | 0.39 | C-RETAIN-C3 | 370.10 |
| C-FAILMUT | 23.26 | C-STALE | 374.89 |

#### 4.3.5 P3 fs-records-b2s (published, `c122164`..`b444623`, then 4.3.6)

18 targets, 8 security targets for 7 claims (C2 runs in two forms with one query file). Security at K_r = 3: A1, A2 (AnyPin, chosen); C2 (Main, fresh, failure-interleaving); C2-chosen-fs (Main, chosen, fail-stop); C3 (Main, chosen, Beacon-to-Server direction); C4 (AnyPin, chosen, fail-stop); S2 (AnyPin, fresh); UKSr (fresh; Main in the `8323943` pass, AnyPin since `974eedf`). Definitional C3-finish (K_r = 1, AnyPin). Witnesses C5a, C5b, C5c (K_r = 2, Main), S4, FAR (K_r = 1, Main), PINREAD (K_r = 1, AnyPin). Controls C-UKS on UKSr (K_r = 1; AnyPin since `974eedf`), C-RETAIN and C-STALE on C3 (K_r = 3).

Recorded pass on tree `8323943`, recorded in `b444623`, 2026-10-05 12:11-14:51 (`pv-work/p3-fix/final`): 49/49 exact, exit 0; registration 2644.8 + s2b 3435.7 + b2s 3517.9 = 9598.5 s ProVerif (sum of 49 rows; checker totals add to 9598.4), 9633.6 s wall, 89% of OD7. Reviews: three lenses (3 minor, 10 nit) fixed in `8323943`; the confirming review of `b444623` found that the docs' claim that pin-free C2, C3 and UKSr would exceed the per-target cap was unsupported, which triggered `974eedf`.

| Target (8323943 pass) | Time (s) | Target | Time (s) |
| --- | --- | --- | --- |
| A1 | 4.15 | C3-finish | 4.37 |
| A2 | 2.08 | C5a | 9.33 |
| C2 | 908.84 (VmPeak 6888868 KiB, 65.7%) | C5b | 11.22 |
| C2-chosen-fs | 246.03 | C5c | 22.80 |
| C3 | 392.91 | S4 | 0.72 |
| C4 | 1063.84 (59.1% of the time cap) | FAR | 0.52 |
| S2 | 1.50 | PINREAD | 1.15 |
| UKSr | 310.57 | C-UKS | 0.54 |
| C-RETAIN | 259.38 | C-STALE | 277.99 |

#### 4.3.6 P3 AnyPin follow-up (`974eedf`, `00ad609`, `287be25`, published)

**Commit `974eedf`** (2026-10-05 17:35:08, "Run UKSr and C-UKS in the pin-free b2s process"): `fs-records-b2s-uksr.pv` runs `FsRecordsB2sMainAnyPin` (query text unchanged); the checker requires every b2s query file to end, outside comments, with exactly one of the two main processes; regression test now 61 tests (two new); transcript-fidelity test pins the seven pin-free b2s query files with mutations (still 25 tests); inventory digests refreshed for the five changed files only; b2s guide, analysis and event-meaning reference updated (a new item under "Changes in stage P3" is marked as needing review). 9 files, +264/-42.

**Development runs** (pin-free against honest pins, through the checker's `check_target`, `pv-work/p3-anypin/dev/`): C3 TRUE 1109.32 s (about 2.9 times), VmPeak 5004440 KiB; UKSr TRUE 843.23 s (about 2.7 times), VmPeak 2841172 KiB; C2-chosen-fs no result, killed by the 1800 s timeout while still saturating (factor above 7.5; VmPeak 6999612 KiB); C-UKS FALSE with one trace in 1.46 s (the attacker chooses the honest pin). Pin-free C2 fresh failure-interleaving was not run (no room). **Decision:** UKSr and C-UKS move to the pin-free process (projected pass about 10170 s, 94%); C3 keeps honest pins because C3 plus UKSr projected to about 10880 s, over OD7. UKSr was chosen because its query links a Server receive to a Beacon send through the plaintext and PINREAD shows other-pin Beacons leak fresh plaintexts, whereas C3 mentions Server receives only. The pin-free C3 run is a development run, not evidence. C2 and C3 rest, for other pins, on the unreviewed simulation argument of b2s guide step 13 (E3).

**Full serial pass on `974eedf`** (`pv-work/p3-anypin/final/`, runner `run.sh`): queued and started 2026-10-05 17:35:14, ended 20:28:58, exit 0, wall 10423.4 s (2 h 53 min 43 s). Flake hashes recorded in `final/flake-sha256` match the proof-flake copy. FT test 25 passed; checker regression 61 tests OK before each scenario. 49/49 exact. Checker totals: registration 2607.6 s, s2b 3569.0 s, b2s 4212.2 s, total 10388.8 s ProVerif time (sum of rows 10388.74 s). Wall time is 96.5% of OD7's 10800 s, leaving about 377 s (6.3 min), more than the 94% projection because of run-to-run variance (for example b2s-C2 986.91 s against 908.84 s, s2b controls +8-10%) and UKSr 873.05 s against its 843.23 s development run. Every target printed the same saturation statistics as its reference run (the `8323943` pass, or the development run for UKSr and C-UKS), as computed by `final/table.py`. The only warnings are the known termination warnings of s2b-A2 and s2b-S1. A1 VmPeak 10135500 KiB (96.7% of the cap, 350260 KiB = 3.3% headroom).

| b2s target (974eedf pass) | Class | Process | Verdict | Time (s) | VmPeak (KiB) |
| --- | --- | --- | --- | --- | --- |
| A1 | security | AnyPin | TRUE | 4.28 | 674976 |
| A2 | security | AnyPin | TRUE | 2.13 | 561568 |
| C2 (fresh, failure-interleaving) | security | Main | TRUE | 986.91 | 6891236 |
| C2-chosen-fs | security | Main | TRUE | 264.00 | 2782828 |
| C3 | security | Main | TRUE | 402.19 | 3023492 |
| C4 (fail-stop) | security | AnyPin | TRUE | 1069.42 | 3542280 |
| S2 | security | AnyPin | TRUE | 1.49 | 506844 |
| UKSr | security | AnyPin (new) | TRUE | 873.05 | 2840288 |
| C3-finish | definitional | AnyPin | TRUE | 4.33 | 527080 |
| C5a | witness | Main | FALSE | 10.43 | 628040 |
| C5b | witness | Main | FALSE | 11.45 | 748968 |
| C5c | witness | Main | FALSE | 23.10 | 881960 |
| S4 | witness | Main | FALSE | 0.67 | 336292 |
| FAR | witness | Main | FALSE | 0.49 | 306724 |
| PINREAD | witness | AnyPin | FALSE | 1.10 | 374276 |
| C-UKS | control | AnyPin (new) | FALSE | 1.36 | 390724 |
| C-RETAIN | control | Main | FALSE | 276.30 | 2629444 |
| C-STALE | control | Main | FALSE | 279.49 | 2638468 |

Registration and s2b rows of this pass: all 31 exact, longest s2b-C1 1076.83 s and A1 1024.09 s. Regenerate the full 49-row comparison (read-only, imports the worktree checker, writes nothing) with `python3 /tmp/bc-arc-scratch/pv-work/p3-anypin/final/table.py /tmp/bc-arc-scratch/pv-work/p3-anypin/final`.

**Final state (2026-10-05, after 21:25).** `00ad609` ("Record the fs verification pass with pin-free UKSr", docs only) records this pass in the b2s guide, step 13 and its measurement table (seven queries measured in both pin processes: A1 2.1x, A2 2.0x, S2 1.8x, UKSr 2.7x, C3 2.9x, C4 10.8x, C2 chosen fail-stop above 7.5x), the analysis document, the event-meaning reference and the P1 guide. A two-lens confirming review (prose, gates) of `974eedf` and `00ad609` returned APPROVE_WITH_NITS twice: the pin-free C2 extrapolation was updated only in the guide, step 13(a) omitted the associated-data field of `FsBeaconEstablished`, the decisions bullet overstated why pin-free C3 is not a target, and the gates text overstated the mutations. `287be25` ("Align the b2s pin extrapolations across the documents", docs only) fixes all four; the extrapolation is now 1780 s to 10660 s from the 986.91 s honest-pin C2 everywhere. `codex/proverif-fs-records-b2s` was pushed at `287be25` and central fast-forwarded to `287be25`. Remaining reliance on the unreviewed step 13 simulation argument: b2s-C2 (both forms) and b2s-C3 run with honest pins only; A1, A2, S2, UKSr and C4 are pin-free by ProVerif. Pin-free C3 (TRUE in 1109 s) is a development run only, because it does not fit the OD7 budget next to pin-free UKSr (about 103% projected).

#### 4.3.7 Budget and memory

| Pass | A1 VmPeak (KiB) | Share of 10 GiB cap | Headroom (KiB) | Wall (s) | Share of OD7 |
| --- | --- | --- | --- | --- | --- |
| P1 record (`f85e7c3`) | 10130732 | 96.6% | 355028 (3.4%) | 2642.0 | n/a (registration only) |
| P2 record (`f18a089`) | 10139244 | 96.7% | 346516 (3.3%) | 6194.1 | 57% |
| P3 record (`8323943`) | 10135500 | 96.7% | 350260 (3.3%) | 9633.6 | 89% |
| AnyPin pass (`974eedf`) | 10135500 | 96.7% | 350260 (3.3%) | 10423.4 | 96.5% |

A1 fallback if memory fails: A1 at K_reg = 2 (about 3.4 s), which would be a weakening and needs owner approval. Longest runs: s2b-C1 (1077-1113 s), A1 (1024-1067 s), b2s-C4 (about 1064-1069 s). Any further fs target needs an owner budget decision or a separate serial group.

## 5. Findings reported to the owner

### 5.1 HB-95 on `main` and `vcvio`

The P0 C-NOGATE trace (G0 §9.2; `pv-work/p0/s2b/runs/s2b-nogate-A1-ks2-kr3-t3-v2-nx.log`) is the later-record substitution. Without the `decrypted.seq != 1` gate: (1) the attacker withholds the registration response; (2) the Server sends the new peer a later tasking whose first 8 bytes are a binding for a value `a` the attacker knows; (3) the attacker delivers a response with outer key ID `a` and that tasking in place of the sequence-one frame; (4) the Beacon commits with a key ID and payload the Server never built, so A1 is FALSE. G0 checked every step against `vcvio` `8330cde` (beacon.rs:452, 462-467, 491-505; pqxdh.rs:616-627). The fix is `5cbd76e` "Require sequence one for Beacon registration" (2026-09-07), which adds `if decrypted.seq != 1 { return None; }` (central beacon.rs:468). Re-checked today with `git merge-base --is-ancestor`: central `d937aab` contains it; `origin/main` (`61df284`), `vcvio` and `origin/vcvio` (`8330cde`) do not; 93 remote-tracking branches contain it. The owner said "I'll handle it" (2026-10-04, `main-lacks-seq1-fix.md`): do not port it. In the fs model the gate is present (s2b-A1 TRUE; witness A3 shows the gate is reached); C-NOGATE models the `vcvio` behaviour. Whether the older `origin/main` code (`src/beacon.rs`, 2026-08-09) is exposed in the same way was not checked **[unverified]**.

### 5.2 beacon.rs:499 is a dead check

`if self.server_id.as_bytes() != &server_binding.identity_public_key` (central beacon.rs:499) compares the pin with the copy of itself stored at construction (beacon.rs:74 and :81), so it cannot fail; the effective pin check is core pqxdh.rs:545. The Lean `Phase2Publication.finish` pin-versus-binding compare mirrors it and also cannot fail. Recorded in `c-work/pin-gate/plan.md` lines 25 and 49 only; no repository document mentions it (checked with `git grep` on the lane and central docs). No Rust change proposed (owner ruling of 2026-10-03).

### 5.3 The key-ID bound is the u64 domain

`server_number <= limit` in ProVerif `JointCreate` encodes the `u64` domain of `server_kid` in `Beacon::try_new(server_kid: u64, ..)` (beacon.rs:65-82, no runtime range check) on ProVerif's unbounded `nat`, reusing the Server counter limit because Rust ties the two; it is not a model mismatch. Documented in `doc/impl/registration-generated-process-control.md:25` by `605420b` (crate paths fixed in `d2c7b29`). The optional comment at the bound in the pvl (pvl:152) was not added.

### 5.4 Rust instances of the Server parse checks

See section 4.1 (T0a). `identityPoint`, `x25519Point` and `beaconIdentity` are constantly `true` in Rust; `kemKey` is not. The review rule in `doc/impl/server-authentication-design.md:122` forbids theorems that assume the first three return `false`. Lean docstrings (T0b) are deferred.

### 5.5 Same-seed Servers

The Rust consumed set is per Server object (server.rs:31); two objects built from one `id_seed` (server.rs:148-167) accept the same bundle (ProVerif R4), and a `RegistrationOutput` from one can be built on the other (pqxdh.rs:847-857) (anchors from plan OD2). The owner ruled on 2026-10-03 that same-seed Servers are one Server identity under the idealised proof Server, so R4 is an expected consequence classed `limitation`, and R1/R1' are stated per live object. OD2 does not settle L1 case (iv): a token accepted by one live object and built by another with the same key and `server_kid`; it stays open.

## 6. How to verify and run

### 6.1 Shared rules and the proof shell

- Locks: Lean only under `flock /tmp/bc-arc-scratch/lean.lock`; ProVerif only under `flock /tmp/bc-arc-scratch/proverif.lock`. One process of each kind at a time; while the owner's "alone on the machine" statement holds, one Lean and one ProVerif job may run side by side. `focused-during-pv.lock` is used only by Codex's `/tmp/beaconcrypt-withheld-pv-check.sh`.
- Proof shell: `nix develop --no-update-lock-file path:/tmp/bc-arc-scratch/proof-flake#proofs -c <command>`. Check first that `sha256sum /tmp/bc-arc-scratch/proof-flake/flake.{nix,lock}` equals the worktree's: `flake.nix` `2677cfb7960110181f7dcdaf2877b011bbfd2947252ce78f15130d4e7dc0a01d`, `flake.lock` `32701786c70092c0671ded22522847a4b406e806d208ce9f995df402d9c3f792` (re-checked today against central). The shell closure is protected by the GC root `/tmp/bc-arc-scratch/proof-profile` (-> `/nix/store/4a5hfy7d8p9793brf8q44wnnyjbnr84y-nix-shell-env`). `make` is not on the host PATH. ProVerif 2.05 is `/nix/store/6sshb9zipvahsxadc92m1pp9jny547yx-proverif-2.05/bin/proverif`; `Makefile:43` has `override PROVERIF := proverif`.
- Never: `nix develop path:<worktree>`, `make verify`, `lake build`, `nix-collect-garbage`, `git stash` (shared across worktrees), force-push, editing a runner script while its queue runs.

### 6.2 Lean lane checks

Run one module at a time with `-j1 -M8000`. Never write into `/tmp/beaconcrypt-registration-joint-olean`, `/tmp/beaconcrypt-registration-symbolic-olean` or any old lane overlay or check directory. Helpers are in `/tmp/bc-arc-scratch/c-work/pin-gate/helpers/`. Toolchain `/home/user/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean`.

| Lane (head) | Check one module | Argument | Output prefix (first `LEAN_PATH` entry) | Rest of `LEAN_PATH` | Runner / module list |
| --- | --- | --- | --- | --- | --- |
| T1/base (`8984399`) | `check-t1.sh` (`lake env` in central `proofs/lean`, timeout 600) | relative path without `.lean`, e.g. `BeaconcryptCore/Computational/PqxdhRegistrationScheduleSurface` | `/tmp/beaconcrypt-pin-width-olean/t1` | `/tmp/beaconcrypt-registration-joint-olean`, then lake's | none; `t1-logs/downstream.txt` (4) |
| T2 (`d2c7b29`) | `check-t2.sh` (lake env, timeout 600) | relative path | `/tmp/beaconcrypt-pin-width-olean/t2` | `/tmp/beaconcrypt-registration-symbolic-olean` | `run-t2.sh`; `t2-logs/downstream.txt` (29) |
| Joint services (`6ccf4b4`) | `check-svc.sh` (direct lean, timeout 900, `.olean` only) | short module name | `/tmp/beaconcrypt-pin-width-olean/svc` | `$(cat /tmp/beaconcrypt-registration-joint-service-check/leanpath)` | `run-svc.sh`; `svc-logs/downstream.txt` (32) |
| Symbolic (`5b28f90`) | `check-sym.sh` (lake env, timeout 600) | relative path | `/tmp/beaconcrypt-pin-width-olean/sym` | `/tmp/beaconcrypt-registration-symbolic-olean` | `run-sym.sh`; `sym-logs/downstream.txt` (45) |
| R1 (`204eff7`) | `check-r1.sh` (direct lean, timeout 180, `.olean` only) | short module name | `/tmp/beaconcrypt-pin-width-olean/r1` | `$(cat /tmp/beaconcrypt-registration-r1-restriction-check/leanpath)` | `run-r1.sh` (records each source's sha256); `r1-logs/downstream.txt` (34) |
| Evolving (`6ae17ba`) | `bash /tmp/beaconcrypt-evolving-record-check/check.sh <ShortModule>` (timeout 120; refuses to overwrite a linked artefact) | short module name | `/tmp/beaconcrypt-evolving-record-check/olean` | `$(cat /tmp/beaconcrypt-native-suffix-leanpath)` | `/tmp/beaconcrypt-evolving-record-check/resume-2026-10-02/tools/review-check.sh`, `review2-check.sh` |

Example: `bash /tmp/bc-arc-scratch/c-work/pin-gate/helpers/check-r1.sh PqxdhRegistrationR1Surface`. Runners are resumable: they skip modules marked `pass` in `<lane>-logs/status.tsv` and stop at the first failure; if a source changes after it passed, delete its line and every later line. The `seconds` column includes lock wait. Gate tools: module order `python3 /tmp/bc-arc-scratch/c-work/pin-gate/tmp/downstream.py <worktree> HEAD BeaconcryptCore.Computational.PqxdhRegistrationScheduleSurface`; statement gate `tmp/leandecls.py sigdiff <(git show A:F) <(git show B:F)`; M0 list `tmp/leandecls.py taint …`; inventory refresh `tmp/refresh-inventory-at.py`.

**First-`LEAN_PATH`-entry pitfall.** Lean 4.34 resolves every module of a package from the first `LEAN_PATH` entry that contains the package directory (`BeaconcryptCore`). A fresh output prefix holding only the module being compiled therefore fails on its imports (evidence: `t1-logs/check-PqxdhRegistrationScheduleSurface.attempt1-no-mirror.log`, "object file '…/t1/…/PqxdhRegistrationScheduleInitial.olean' … does not exist", exit 1). So each output prefix is a complete symlink mirror (`mirror-{t1,t2,svc,sym,r1}.sh`, each run once; they create links only inside the prefix, exclude the lane's downstream modules, never overwrite; rerun only if a new upstream module appears in the old tree). Prepending a new directory to an old leanpath in place would shadow later rebuilds in the old first entry, which is why every lane has its own prefix. All prefixes had 0 broken links on 2026-10-05.

**Hazards.** The svc and r1 prefixes keep links to the symbolic-only `PqxdhRegistrationAccept{Operations,Status,Receipt,Token}` oleans compiled against the pre-alignment `PqxdhRegistrationTableDispatcher`: nothing may import them through these prefixes. Never reuse a prefix for another lane. The old overlays and `/tmp/bc-arc-scratch/c-work/review-pause` review environments still hold pre-alignment downstream artefacts. Twelve shared modules reach central-only `PqxdhServerAuthPhase1Origins`/`Identity` only through `/tmp/beaconcrypt-server-auth-withheld-olean`.

**Retired helpers** (refuse with "RETIRED: use …/check-{t1,svc,sym,r1}.sh", exit 2; originals kept as `*.pre-retirement`): `/tmp/beaconcrypt-registration-joint-check.sh`, `/tmp/beaconcrypt-registration-symbolic-check.sh`, `/tmp/beaconcrypt-registration-joint-service-check/check.sh`, `/tmp/beaconcrypt-registration-r1-restriction-check/check.sh`. Retirement gaps: `/tmp/beaconcrypt-registration-identity-check.sh` still writes `-o` into `symbolic-olean` and `/tmp/beaconcrypt-registration-receipt-guards.sh` calls it (documented as retired in the symbolic lane but not refusing); `/tmp/beaconcrypt-registration-{identity,payload,tail}-generator-check.sh` write nothing but resolve the pre-alignment `symbolic-olean`. Do not use them.

### 6.3 ProVerif fs group

Whole group (the verification record; needs the machine alone; about 2 h 41 min to 2 h 54 min):

```sh
flock /tmp/bc-arc-scratch/proverif.lock nix develop --no-update-lock-file path:/tmp/bc-arc-scratch/proof-flake#proofs -c make -C <wt>/beaconcrypt-core SHELL=bash check-proverif-fs PROVERIF_FS_LOG_DIR=<dir>
```

Prefer copying the template `/tmp/bc-arc-scratch/pv-work/p3-anypin/final/run.sh` (edit `D` and `WT`), run with `nohup`: it records commit, status before, flake hashes, queued/start/end/exit, wall time, all logs and VmPeak via `pv-work/p2-fix/vmsampler.py`. `check-proverif-fs` (Makefile:255) runs the transcript-fidelity test, then `check-proverif-fs-{registration,records-s2b,records-b2s}` at `-j1`, each running `test-free-schedule-checker.py` then `check-free-schedule.py --scenario <s> --timeout 1800 --address-space-kib 10485760` (Makefile:87-88). `verify-in-shell` and `verify-proverif-in-shell` call it after `check-proverif` (Makefile:147-151, 161-165). The fs group is not in the 35-scenario `-j35` roster and not in CI.

One target (development runs must go through the checker so the exact-line check applies):

```sh
python3 beaconcrypt-core/proofs/pro-verif/check-free-schedule.py --scenario fs-records-b2s --list
python3 beaconcrypt-core/proofs/pro-verif/check-free-schedule.py --scenario fs-records-b2s --only b2s-C2 --log-dir /tmp/fs-logs --results /tmp/fs-results.tsv --timeout 1800 --address-space-kib 10485760
```

`--list` does not run ProVerif. Always pass `--address-space-kib` (the default 0 means no cap). Outside the proof shell also pass `--proverif <path>`.

Gates without ProVerif (run before every ProVerif-stage commit): `cargo test --locked -p beaconcrypt-core --test proverif_transcript_fidelity` (25 tests at `974eedf`, 227 Rust citations: 59 registration, 84 s2b, 84 b2s); `python3 beaconcrypt-core/proofs/pro-verif/test-free-schedule-checker.py` (61 tests); `make check-inventory` inside the locked shell (`nix develop ... -c make -C <wt>/beaconcrypt-core SHELL=bash check-inventory`; on the host it needs `LC_ALL=C`; at `974eedf` it counts 173 handwritten ProVerif files and 25 validation files); `cargo fmt --all -- --check`; `black --check` on the two checker files; `git diff --check`. Declaration allowlist: 65 entries at `974eedf` (1 nounif, 15 `[precise]`, 49 `set`), 61 at `d937aab`, 57 at `9e588c6`.

### 6.4 Pitfalls

- 10 GiB cap: always run ProVerif with `--address-space-kib 10485760` or `ulimit -v 10485760`.
- A1 headroom: registration A1 at K_reg = 3 peaks at 96.7% of the cap (3.3% headroom). Any change to `fs-common.pvl`, the registration libraries or the theory can push it out of memory; check VmPeak in every pass.
- Budget: the fs group now uses 96.5% of OD7 (wall). Adding any target needs an owner decision.
- Rerun the whole group whenever `fs-common.pvl`, the checker or any shared library changes; record each pass in a separate docs-only commit; compare saturation statistics with the previous pass to show comment-only changes alter no clause set (see `table.py`).
- `check-inventory` on the T2 lane base fails with "unreviewed handwritten-proverif file-set drift" (inventory gap 1, pre-existing).
- Lean: first-`LEAN_PATH`-entry resolution (section 6.2); reuse a same-commit `.lake` by copying, never symlinking.

## 7. Open items and next steps, in priority order

### 7.1 ProVerif (first priority)

1. **Done: record the AnyPin pass** (`00ad609`). On `/tmp/beaconcrypt-proverif-fs-b2s`, make a docs-only commit recording the pass in `pv-work/p3-anypin/final/` (tree `974eedf`, 17:35-20:28, exit 0, 49/49, 10388.8 s ProVerif, 10423.4 s wall, 96.5% of OD7, A1 3.3% headroom), following `b444623`: update the b2s guide's Results section (line 151 says the next commit records this pass), its budget item (line 232 projects "about 10 minutes" left; the measured figure is about 6 minutes), the measurement and step-13 budget figures, the analysis document's b2s bounds and pin paragraphs, and the P1 guide's registration time and pass time. Run the gates of section 6.3.
2. **Done: review** (two-lens confirming review, nits fixed in `287be25`). Original text: Confirming review (at least a gates lens and a prose lens, as `p3-confirm-gates`/`p3-confirm-prose`) of `974eedf` and the record commit, including the new event-meaning "Changes in stage P3" item, the checker's main-process rule and the FT mutations. Fix findings in follow-up commits; rerun the group only if a query, bound, shared library or the checker changes. Whether the owner requires a full three-lens review for `974eedf` is **[unverified]**.
3. **Done: publish P3** (`287be25` on origin; central fast-forwarded). Original text: Push `codex/proverif-fs-records-b2s` (new branch) and fast-forward `codex/full-proof-composition` from `d937aab` to the reviewed head (the b2s branch's parent is `d937aab`, so a fast-forward is possible); verify with `git ls-remote`.
4. **Done in part: refresh the central handoff.** A pointer to this file was added to the central pause README's resumption log in the same commit as this handoff; the P1-P3 details live here. Original text: The central pause README's resumption log stops at "The P0 scoping spike is running" (`533901f`); add the P1-P3 stages, the owner decisions OD1/OD2/OD7/OD11, HB-95, and a pointer to this handoff.
5. **Budget decision.** Ask the owner for a larger OD7 budget or a separate serial group before adding any P4-P8 target.
6. **P4 (F13), redefined after P0.** Re-running P1-P3 under a stronger theory is infeasible. Instead: (a) the t1enc registration set at K_reg = 2 (t1enc unmeasured on the record scenarios); (b) same-role DH only in small dedicated scenarios (not designed); (c) the torsion alias stays unmodelled; add the all-zero check (`pqxdh.rs:383-389`) with an event distinguishing it from a DH refusal (R5 does not witness it now); the KEM-controller library swap; the raw-ephemeral FALSE control; allowlist nx-a if t1enc is used. F13 stays partly open; same-role DH symmetry is shown nowhere.
7. **P5 strong secrecy.** SS1 diff-equivalence over the b2s sends; SS2 an s2b challenge behind the OD5 freshness gate. Models must publish the `Some`/`None` bit of every receive and finish (E11).
8. **P6.** `fs-aead-differential.pvl` and its two `.pv` files (differential controls, not counted); a `verdict-classes.tsv` manifest with an FT completeness test including the fs targets (18 b2s targets, the fail-stop targets, the pin-free process); an FT compact-text test equating the HKDF prefix (`crypto.pvl:72-95`) with `concrete.rs:85-131`.
9. **P8.** Legacy diffs: F11 relabels; failed-receive-compromise from 9 to 7 (remove two tautological correspondences); AEAD closed-control relabels; `active-classical` dedupe if approved (OD8 undecided). Documentation consolidation: `doc/formal-verification-analysis.md`, `doc/composition-assumptions.md`, `beaconcrypt-core/README.md` counts; stale "32 production scenario roster" comments at Makefile:495 and :510; "thirty-two named ProVerif scenarios" at `trusted-boundary.md:211`; "seventy-seven handwritten ProVerif artifacts" at `trusted-boundary.md:64` (inventory says 173); state which fs results are pin-free and which rest on E3 or E21. Also: a CI decision for the fs group; two broken anchors (`impl/formal-verification-stage-4.md#L123-L127`, `persistence.md#server-state-persistence`); the final OD11 stepwise serial verification (legacy targets at `-j1`, then `check-proverif-fs`, Lean, inventory, FT); an independent review before publication.
10. **P7 (optional).** Compromise and forward secrecy with reveals between worker steps; only if the owner decides OD9.
11. **Other ProVerif items.** A heuristic letting C2 and C4 with chosen records run in failure-interleaving form; a cheaper pin-free C2/C3; C-RETAIN on C2 and a b2s C-FAILMUT (not run); A1 headroom.
12. **Pending paper arguments** (needed before fs results can be cited as statements about the Rust API; until then cite as "symbolic results for the fs process under pending abstraction steps", OD10). Not written: L1 accept/build scheduling cases (i)-(v), case (iv) open; L2 one registration per record object, merged key IDs, routing (also the Server's routing by claimed sender); L3 failure neutrality and far collapse (OD4); L4 the send relation; L5 Beacon lifecycle (A1 injectivity, R1' and the finish collapse depend on it). L6 event projection reviewed in `dedd82f`, except the later `FsReceivedFrame`, the frame field of `FsReceiveRejected`, and every "Changes in stage P3" item (including `974eedf`'s). Written in the guides but not reviewed: E19 direction split (records guide step 4, b2s guide step 4), E20 v2 coins (records guide step 2), E21 fail-stop deletion argument (b2s guide step 12; used by C2-chosen-fs and C4), E3 pin-independence simulation (b2s guide step 13; until reviewed, C2 and C3 hold only for runs where every Beacon pins the honest key and ID; ProVerif could not check its root step: PIN gave "cannot be proved", PIN2 and PIN-ID were stopped). Recorded without further argument: E7, E16, E22, E23, E24. Dropped with OD1: L7, L8, fallback W.

### 7.2 Lean lanes (lower priority)

- **R1 restriction, step 4.** (1) Port the 109 modules missing from the lane byte for byte from `adabe9a` (`codex/server-auth-publication-composition`; the central Lean tree is unchanged since `959cdab`). (2) Record the port in `evidence/common-authentication-port.json`; never overwrite overlay symlinks. (3) Prove `native_root`: `RootExecution.execution` erases to the native handler run, via `game_erase`, `actual_state`/`program_native` and `finish_observation`. (4) Prove `RootAudit`/`audited_root`: one execution that retains the call journal. (5) Prove `journal_public` via `RootObserved.execution_public`. (6) Before porting, rename or qualify `PqxdhRegistrationR1Initial.Audit` (collides with `PqxdhServerAuthRootOccurrences.Audit`) and `PqxdhRegistrationR1Restriction.singleton` (collides with `Singleton.singleton`). **Step 5:** `laneFailure`; `generated_failure_le` (gates bounded by one, no pin test since the alignment); `generated_authentication` via `common_authentication_with_resources`; a separate lane resource ledger; the supplied-seed branch stays an exact equation with no security conclusion. **Step 6:** guide `doc/impl/registration-r1-restriction.md`, analysis appendix, guards; two independent reviews; a fresh topic from central; owner authorisation for integration.
- **Evolving record.** (0) Add `carried_reaches`: for `GeneratedContinuation.run` under `hashImpl` from `∅`, `result.2 = some selection` and `SampleChronology.Reached … (adversary selection) pending details cache after`; prototype `/tmp/bc-arc-scratch/c-work/rereview-evolving/CarriedReaches.lean` checks with exit 0 and the standard axioms (evidence `carried.log`, runner `run.sh` writes no artefact); not yet added. (1) Before phase: a compiler-level remainder-support bridge from `PqxdhLaterSavedPostCompiler.complete` to the original all-reply callback syntax, then a `resume_pre` twin with marker `none` via `Monitor.program_pre`. (2) Join frame and compiler: connect Chronology64 `run_not_used` with `SavedPostCompiler.complete` via `source_complete`. (3) Inside phase: use the actual pre-send counter and historical directional path, with no address-separation or fresh-cut premise. (4) Remaining: two-world prefix join and real/raw hop; Fresh/event implication and finish/refusal accounting; alias allowance `(8 + 67 * postCap) / 2^256` and the full ledger.
- **Joint services.** One dynamic scheduler joining the actual constructor, bundle and finish over the private service pools and native shared state. Prove the private-slot ownership invariant from generated construction (each live owner's identity index holds its exact seed; each InitSent owner's KEM index holds its exact active key pair), preserved by every scheduler operation including failed writers and retries; it discharges the CompiledOwner8 `identityOwned` and `kemOwned` premises. Then route permitted reveals from live fields, keeping erased historical pools inaccessible. Still missing consumers: Server converted-DH/signing side, identity/record/session selection, global query ledger, hybrids. Do not delete the old `noCreate`/`noSign` restrictions.
- **Symbolic schedule.** An adaptive archive/event invariant connecting the actual accept/build receipts to the maintained symbolic event coordinates within the same nine-capability execution, consuming `handler_valid`, `callback_origin`, `handler_journal` and `buildComplete`. The 10 untracked prototypes (`registration-joint-*control*.pv`, `registration-joint-control-queries.pvl`, `doc/impl/registration-symbolic-transition-plan.md`) use only the honest pin; rerun them when next working on the lane. Receipt manifests keep the old pvl hash `95bf6774…` as history.
- **Optional pin items (plan §9).** A Lean theorem that an InitSent Beacon with `xpkConv (absBytes pin) = none` gets `none` and the abort state from every finish (replacing the "by construction" sentences); a ProVerif Beacon control with a non-`ed_public` pin.
- **Stale markers to fix on next touch.** Symbolic README "Exact repository state" bullet on `02b7e4e`/`c637a52`; symbolic `review-status.json` `pin_width_alignment.lane_commit`; R1 README "Repository and publication state" and R1 `manifest.json` `status` (for `d5a6ffd`, `2708919`, `db60df8` and the RG3 follow-up) all say "local and not pushed" although `ls-remote` shows them published. The central pause README calls `codex/evolving-record-pause-2026-10-01` local-only; it was published 2026-10-02 19:43.

### 7.3 Deferred T0b (next central full build)

Lean docstrings for the central Server checks (plan §5.1), deferred because a docstring change in `PqxdhServerAuthExperiment.lean` or `PqxdhServerRootPreparation.lean` invalidates most of the computational olean graph and these files are hashed in `beaconcrypt-core/proofs/reviewed-inventory.txt`. Anchors (valid at `d937aab`; the four Lean files unchanged since `bb7b67e`): PqxdhServerAuthExperiment.lean:100; PqxdhServerRootPreparation.lean:5 and :56; PqxdhLiveBeaconBirth.lean:7, :27, :107; PqxdhServerAuthNegativeControl.lean:1532; the `Checks` code-block comment at `doc/impl/server-authentication-design.md:91`. The :100 docstring must also say `beaconIdentity` is always `true` for Rust (server.rs:452-453), matching `a0a67f5`. Inventory rows to refresh: 1183, 1036, 958, 1184 (row 1037, StaticDhSource, must stay unchanged), with `python3 /tmp/bc-arc-scratch/c-work/pin-gate/tmp/refresh-inventory-at.py <T0b-worktree>/beaconcrypt-core <four paths>`, then `make -C <T0b-worktree>/beaconcrypt-core check-inventory` in the locked shell. Gate RG5: the sigdiff shows DOC records only. Planned branch `codex/server-check-docstrings`, worktree `/tmp/beaconcrypt-server-check-docstrings` (not created).

### 7.4 Central integration of the Lean lanes

No registration or evolving lane is in central. Per the central pause README, port the work semantically into a fresh topic from current central (root imports, guards, checker and inventory entries, full validation); do not merge wholesale. Known inventory gaps to close then: (1) `check-inventory` on T2 lists 11 unlisted registration ProVerif files (`registration-beacon-admission.pvl`, `registration-build-lookup.pvl`, `registration-joint-operational-queries.pvl`, `registration-joint-schedule-queries.pvl`, `registration-joint-schedule.pv`, `registration-joint-schedule.pvl`, `registration-process-control-callback.pvl`, `registration-process-control-fixture.pv`, `registration-process-control-fixture.pvl`, `registration-process-dispatch.pvl`, `registration-process-return.pvl`; log `pin-gate/rg2-symbolic/inventory-t2.log`; pre-existing at `ae279d7`, recorded in `d2c7b29`), and the registration schedule Lean modules are not inventoried either (`755fa00`); (2) 12 of the 29 shared modules (PendingIdentity (Origins only), IdentityProcess, ResponseEncoding, PayloadProcess, TailPrimitives, ResponseTail, TailNative, TailOperations, TailCallback, TailProcess, TailEvents, TailEventRun) transitively import central-only `PqxdhServerAuthPhase1Origins`/`PqxdhServerAuthPhase1Identity` (in central since `edc701e`); direct importers PendingIdentity and IdentityProcess.

### 7.5 Questions still open with the owner

OD6, OD8, OD9 undecided **[no record found]**; confirmation of the `959cdab`/central Rust basis; acknowledgement of meaning changes M0-M5; L1 case (iv); budget beyond OD7; whether test-file changes trigger the mutation-suite requirement; whether `nix-collect-garbage` may ever be run (still forbidden).

## 8. Process conventions

- **Design first in scratch**, with critiques and owner decisions before building (pin gate: `c-work/pin-gate/plan.md`, `critic/`, `map-{lean,rust,symbolic}.md`; ProVerif: `pv-work/design/proverif-plan.md` §7.1).
- **Topic branch in its own worktree** `/tmp/beaconcrypt-<topic>`, branched from the current central HEAD; Claude's branches keep the `codex/` prefix.
- **Commit, then verify that exact commit, then record the pass in a separate docs-only commit** (pairs `7518974`->`1b09dbd`, `63369de`->`30eecfc`, `c122164`->`ddc0a33`, `8323943`->`b444623`). Record commits touch only `doc/formal-verification-analysis.md` and the stage guide(s).
- **Independent review through several read-only lenses** that re-run cheap checks themselves: ProVerif `pv-work/pN-review-{fidelity,integration,soundness}`, `pv-work/p2-l6-review`; pin gate `rg1-{fidelity,gates}`, `rg2-{lean,symbolic}`, `rg3-{r1,svc,sym}-{fidelity,integrity}` (findings `rg3-findings.json`), `rg4/`. Earlier Lean stages used hygiene, meaning, notion, rust, crypto, model, statement, transcription, docs, codepath, event, gaps, soundness and fidelity lenses. Major findings were checked adversarially before acting in earlier stages (`c-work/review-<stage>-verify-<lens>-<n>-notes.md`); for 2026-10-02..05 this step is **[unverified]** (no `verify-` files in `pv-work/`).
- **Fix in follow-up commits**; if a query, bound or the checker changes, rerun and record. **Confirming review** of the fixes (`pN-confirm-{gates,prose}`, `confirm-rg3/`); leftover nits get one more commit that says whether a rerun was needed (`9e588c6`, `500a7d9`).
- **Publish** fast-forward only, topic and central together, never force-push, then check with `ls-remote`. Every remote update since 2026-10-02 was a fast-forward ("update by push"); lanes were integrated with merge commits, not rebases (`67b8063`, `d5a6ffd`, `02b7e4e`, `2fd6b56`). Proof claims are published only after the independent and confirming reviews; archives and handoff branches may be published any time.
- **Commit messages**: short imperative sentence-case subject without full stop; prose body, one paragraph per line; for proof changes, Rust evidence with file:line, meaning changes M0, M1, … with affected statements, "No statement is weakened or deleted and no assumption is added" where true, and a "Validation:" or "Gates:" paragraph (see `716c631`, `9e588c6`); last line exactly `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. All commits are authored as `user <user@nixos.mschn.fr>`; only the trailer identifies the agent (Codex used `Co-authored-by: Codex <codex@openai.com>`).
- **Inventory digests** are refreshed only for monitored files that changed.
- **Long runs** use `nohup` scripts that record commit, status, flake hashes, times, exit, logs and VmPeak; measurement queues move each line to `<queue>.done` and `dev/history.txt` (`pv-work/p3-anypin/queue.sh`).
- **Notes**: every stage keeps a timestamped `NOTES.md` so interrupted agents can resume.

## 9. Scratch locations index

All under `/tmp/bc-arc-scratch/` unless absolute.

| Path | Contents |
| --- | --- |
| `handoff-2026-10-05/` | This README, the three fact files, `.lsremote-process.txt` (212-ref `ls-remote` snapshot at 19:07:32) |
| `lean.lock`, `proverif.lock`, `focused-during-pv.lock` | Locks |
| `proof-flake/`, `proof-profile*` | Two-file flake copy; GC root of the shell closure |
| `proverif2.05.tar.gz`, `pv-src/proverif2.05/` | ProVerif 2.05 source (fetched 2026-10-05 01:53) |
| `pv-work/design/` | ProVerif plan rev 2 and rev 1, toy probes `toy/`, `critique/`, legacy timing outputs |
| `pv-work/p0/` | P0 spike: `G0-report.md`, `s2b/` (incl. `NOTES.md:78` owner decisions, HB-95 trace in `runs/`), `b2s/`, `p0.3/` (theory variants in `lib/`), `p0.5-6/`, `l6/`, `g0-tools/` |
| `pv-work/p1`, `p1-review-*`, `p1-fix/final2`, `p1-confirm-gates`, `p1-nits` | P1 work, reviews, record pass |
| `pv-work/p2`, `p2-review-*`, `p2-l6-review`, `p2-fix/final`, `p2-fix/vmsampler.py`, `p2-confirm-{gates,prose}` | P2 work, reviews, record pass, VmPeak sampler |
| `pv-work/p3`, `p3-review-*`, `p3-fix/final`, `p3-confirm-{gates,prose}` | P3 work, reviews, `8323943` record pass |
| `pv-work/p3-anypin/` | AnyPin: `NOTES.md`, `dev/` (development runs, `results.tsv`, `history.txt`), `final/` (pass on `974eedf`: `run.sh`, `final-pass.log`, `logs/`, `vm-samples.tsv`, `table.py`, `exit`, `wall`), `commit1.msg`, `checker-frozen.py`, `queue.sh`, `edits/` |
| `pv-work/ft-nits-backup.rs` | Backup of the FT test before the P1 nits |
| `c-work/pin-gate/` | Pin-width plan `plan.md` (+ `plan-draft.md`), `critic/`, `map-*.md`, `helpers/`, `tmp/` (gate tools), `{t1,t2,svc,sym,r1}-logs/`, `pv-t2/` (incl. `badpin/`), `pv-t2-comment/`, review dirs `rg1-*`, `rg2-*`, `rg3-*`, `rg4/`, `confirm-rg3/`, `keyid/`, `m0/`, `gate-test/`, `libsodium-src/` |
| `c-work/rereview-evolving/` | `CarriedReaches.lean` prototype, `carried.log`, `run.sh` |
| `c-work/review-pause/` | Review environments (pre-alignment artefacts) |
| `c-work/` (other) | Milestone B, C, D stages and review files; `b-design/b-design.md` |
| top level (2026-09-27..29) | Audit files: `verified-findings.md`, `verify-*`, `milestone-a-g*`, `f*`, alias probes, `add-module-gates.py`, `refresh-inventory.py`, `commit-modules*.py`, `full*/` |
| `/tmp/beaconcrypt-pin-width-olean/{t1,t2,svc,sym,r1}` | Lane Lean output prefixes (symlink mirrors) |
| `/tmp/beaconcrypt-evolving-record-check/` | Evolving lane check helper, olean dir, `resume-2026-10-02/` notes and tools |
| `/tmp/beaconcrypt-registration-{joint-service,r1-restriction}-check/leanpath` | Lane `LEAN_PATH` suffixes |
| `/tmp/beaconcrypt-symbolic-interface-audit/README.md` | Codex symbolic-interface audit (also archived in central `integrated-evidence/`) |
| `/home/user/.claude/projects/-home-user-beaconcrypt/memory/` | Owner-decision memory files (section 2); `milestone-b-resume.md` looks superseded by Codex's integration `7ef820c`..`edc701e`, `e410d32` **[coverage of every B6/B7/B8b item unverified]** |

## 10. Items not verified

- The owner's 2026-10-05 pause request (relayed by the orchestrator only).
- OD6, OD8, OD9 decisions; the `959cdab` basis confirmation; owner acknowledgement of M0-M5.
- Confirming reviews of `8984399` and `5b28f90`; adversarial verification of findings in the 2026-10-02..05 stages.
- Whether test-file changes trigger the mutation requirement; whether `974eedf` needs a full three-lens review.
- Exposure of the older `origin/main` code to HB-95.
- The final-state paragraph of section 4.3.6 was written by the orchestrator from the commit log and review results, not re-verified by a separate agent.
- All P0-P3 timing numbers except the AnyPin pass are quoted from guides, notes, commit messages and logs; nothing was re-run for this document.
