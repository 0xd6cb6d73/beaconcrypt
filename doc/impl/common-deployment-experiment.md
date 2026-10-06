# Common deployment experiment: CE-3 compile-lemma trial

Status: CE-3 trial of handoff item 3 (the common computational/symbolic experiment), on branch `codex/deployment-experiment` over central `bccd853e`, not pushed and not integrated. An independent review returned APPROVE_WITH_NITS with one major and four minor findings; all are fixed in documentation, and none needed a Lean change. The plain-English explanation is the section "Common deployment experiment and its compile lemma (CE-3 trial)" of [the analysis](../formal-verification-analysis.md).

## What is proved

Twelve modules under `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/` define a first version of the common deployment experiment and prove that it compiles into an ordinary program of the existing initialized registration schedule (source14). The adversary talks to one Server, built from a generated seed, and to Beacons it creates with pins of its choice. It can issue coins, `create`, bundle, accept, build, finish, HMAC and BLAKE2b commands, and send and receive raw records on Server peers and Beacons. It gets no reveal command, no getter, no snapshot and no start input.

| Module | Statements | Content |
| --- | --- | --- |
| `PqxdhDeploymentInterface` | 3 | Command set, replies, mode O and the mode-P wrapper `observe`, `parsePin` (CE-1 subset). |
| `PqxdhDeploymentNative` | 5 | Native state with ghost raw counters, record, Server and Beacon steps, handler, generated-seed `game` (CE-2 subset). |
| `PqxdhDeploymentRecordCache` | 6 | Local HKDF, AEAD and frame writer with BLAKE2b sent to source14; `local_record`. |
| `PqxdhDeploymentCompile` | 1 | Public log, local copies, `peerView`, `ownerView`, `compile`, `merge`. |
| `PqxdhDeploymentCompileRecords` | 23 | `server_record`, `beacon_record`: local record commands agree with the native steps after merging. |
| `PqxdhDeploymentCompileRegistration` | 30 | Registration never reads copied kernels; every registration command commutes with `merge`. |
| `PqxdhDeploymentCompileStep` | 9 | `step_merge` for all commands under an invariant; generic `compile_simulation`, `compile_run`. |
| `PqxdhDeploymentCompileFootprint` | 12 | Accept, build, bundle and finish footprints reused from the existing registration proofs. |
| `PqxdhDeploymentCompileInvariant` | 24 | Invariant `Good`, its preservation per command, `compile_native`. |
| `PqxdhDeploymentCompileGame` | 3 | `construct_fields`, `compile_game`, `compile_source`. |
| `PqxdhDeploymentReadHistory` | 4 | `kernel_read`, `server_reveal`, `kernel_unreported`, `reveal_unreported`. |
| `PqxdhDeploymentCompileBudget` | 10 | `compile_bound` and its per-command lemmas. |

`compile_game` states that the generated-seed deployment game and the initialized native run of `compile A` have the same joint distribution of the Server's public data, the adversary's output, the whole merged deployment state and the runtime state. `compile_source` states the same for the annotated initialized execution that the KEM theorem T4, the root theorems and the report machinery use. `kernel_read` and `server_reveal` show that the compiled program's two internal reads leave the whole annotated state unchanged, and `kernel_unreported` and `reveal_unreported` show that the report wrapper emits nothing for them. `compile_bound` transports per-class command budgets to caps on the fourteen source14 query kinds. The identity, KEM, prekey and one-time read caps are zero.

All 130 statements carry exact `#print axioms` guards: 126 depend on `propext`, `Classical.choice` and `Quot.sound`, two on `propext` alone, one on `propext` and `Quot.sound`, and one on no axiom. No module uses `sorry`, `admit`, an axiom declaration, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.

## Contracts used

The owner approved four codec contracts of the common experiment on 2026-10-06. They are listed in both assumption lists: the functional contracts under "Assumptions made by the proofs" in [the analysis](../formal-verification-analysis.md#assumptions-made-by-the-proofs) and "Primitive guarantees, additional assumptions and idealizations" in [the composition assumptions](../composition-assumptions.md#primitive-guarantees-additional-assumptions-and-idealizations).

- Used by CE-3 (premises of `compile_native`, `good_step`, `compile_game` and `compile_source`): `Phase1ReadBack`, which gives a Beacon's identity key from its bundle bytes, and `Phase2ReadBack`, which gives the Server identity from a build response.
- Approved but not yet used: `FrameReadBack`, and the one-codec rule with `RawCtxServerRouting.DecoderAgreement` for the Server header router. The experiment and the compiled program already share the codec's frame reader and writer by definition, and the router stays a free parameter.

These are abstract message-model laws about the codec parameter, not facts about Cap'n Proto or any serialization implementation. The trial adds no hardness assumption, idealization or advantage term.

## Plan changes recorded

- Read caps. The plan's section 8 table bounds Server reveals by `qBuild` and established-kernel reads by `min(qCreate, qFinish)`. `compile_bound` gives looser caps: reveals at most the budget of Server send and raw-receive commands, and kernel reads at most the budget of Beacon send and raw-receive commands. `peerKernel` and `ownerKernel` read whenever no local copy exists, including for key IDs that are not installed and Beacons that are not established, and an empty answer is not kept, so such reads repeat. Soundness is unaffected: T4 `actual_le_real` instantiates on `compile A` with `compile_bound` as its budget premise, and its creation-count premise uses only the create cap. Later bills that count reveals or kernel reads use the record-command budgets. Gating the reads on the public log would need an amortized whole-run count in place of the per-command `weighted_bound` argument and changes to several checked modules, so it was not done.
- The local Server metadata placeholder (plan section 8 b) is unnecessary: Server metadata is `Unit`, and the invariant proves that the sender ID equals `setup.serverKeyId`.
- A peer's identity needs only the identity parse of the accept bytes, not the full signature check.

## Open points

- F1, awaiting an owner decision. The plan gives the adversary the Server's public identity key as input, but T4-T6, the report lines and `InitializedSchedule.source` run a fixed program with no input after the Server is generated, and no source14 command returns the Server key. In the trial the adversary therefore has no input and can learn the Server key only by parsing build responses. Learning it by registering first also shifts session ordinals and key IDs, so this is not an exact reduction from the plan's adversary. Options: (a) accept the input-free adversary as a recorded deviation, at no proof cost; (b) generalize the T4-T6 and report lines to programs that depend on the generated public identity; (c) add a Server-identity getter to source14 and re-prove the line over the extended interface. With the key as input only `Phase1ReadBack` would be needed; the trial needs `Phase2ReadBack` because it reads the Server identity from a build response.
- Post-run reveal mode. On 2026-10-06 the owner chose a post-run "later quantum" mode: after the run, every honest X25519 secret, every DH output and every honest Ed25519 identity secret is revealed, and only confidentiality is claimed. The interface stays open to it. Because `compile_game` equates the whole final deployment state, the mode can be added as a phase after the run that is a function of the final state, without changing `Command` or the compile cases. Open: on the compiled side the secrets are reachable only through source14's identity, prekey and one-time field reads, which `compile_bound` caps at zero, which interact with `revealedAt` and `GoodKem`, and which follow native erasure; the Server identity seed, ephemeral scalars and DH outputs have no read. Its cost is to be designed and confirmed before it is built.
- Not done: the `test` and `fresh` commands with the sampling swap, `CE.Logs`, mode P beyond the wrapper, the public functions `phase`, `owner`, `NoBundleFailure` and `designate`, the comparison of the transported caps with T4's ledgers, and the step from `compile A` to `tag work index`.

## Re-estimate

Only CE-3 is revised on the trial's evidence. CE-3 is about 7-12 agent-days in total against the plan's 18-30; about 4-6 were spent in the trial, and 3-6 remain: `test` and `fresh` with their budgets (1-2), the `CE.Logs` extension (1-3) and re-checking the existing modules (1). The CE-1 and CE-2 parts listed above were done inside the same time box. Their remaining parts and every other stage (CE-4 to CE-9, CE-11, CE-13, CE-14) keep the plan's ranges, unrevised. With only CE-3 revised, item 3 proper (plan 78-128) is about 67-110 agent-days in total and about 63-104 remaining. A lower figure would assume that the trial's speed carries over to stages it did not touch, which is speculative; CE-8, CE-11 and item 2 need new reductions rather than operational equalities. For F1, option (a) costs nothing; figures for (b) and (c) are speculative, and the plan's only comparable figure, for extending source14 and re-proving the T1-T6 line (section 8 fallback (b)), is 25-45 agent-days.

## Checks

Each module was checked on its own with Lean 4.34 (`-j1`, `-M8000`, timeout 180) under the shared lock, the root import was checked after each module commit, and the focused `check-inventory` passed after each commit. The review recompiled all twelve modules from source in a fresh prefix with the same results. The fix pass changed only documentation; `check-inventory` and `git diff --check` were run again. No full `lake build`, `make verify`, mutation testing or `nix-collect-garbage` was run.
