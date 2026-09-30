# B5a notes: PqxdhServerAuthNegativeControl (gate)

Task: stage B5a of Milestone B (design /tmp/bc-arc-scratch/c-work/b-design/b-design.md sections 4, 7 row B5a, 10). Worktree read-only: /tmp/beaconcrypt-authenticated-root-completion (branch codex/full-proof-composition). Compile only via:
`cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b5a/<file>.lean`

## Checkpoint 0 (started 2026-09-30)

- B4a olean present in worktree .lake (PqxdhServerAuthExperiment, built 09:51); worktree copy identical to /tmp/bc-arc-scratch/c-work/b4a/PqxdhServerAuthExperiment.lean.
- b4a/notes.md has no "Gate check for B5a" section at start of this stage (checked).

## B4a revision notice (coordinator, 2026-09-30)

B4a is being revised (renames: Query/game/Spec/Inv/Budget/handler/owner/Entry -> ServerAuthQuery, serverAuthGame, ServerAuthSpec, GameInv, ...; new invariant facts). Policy for B5a: every B4a declaration is referenced through ONE block of local abbreviations at the top of the module (section "B4a interface"), so a rename touches only that block. Dependency list is maintained below and updated at each checkpoint.

### B4a declarations used (running list)

(to be filled as the module grows)

## Checkpoint 1 (2026-09-30): architecture fixed, first evaluation lemmas compile

Approach (both controls): exact evaluation of the honest path plus a KEM split. `gameState` is unfolded into seed, scalar, beaconSeed, oneTime, keygen, phase1Run (deterministic), adversary run. Bound per key pair `keyError k := Pr[Bad k | encaps k.1]`; sum over keygen = Pr[Bad | sample] = kemError (`PqxdhKemCorrectnessError.error_probability`). At the encapsulation point use VCVio `probEvent_bind_le_probEvent`; before it `probEvent_bind_le_of_forall_le`; after it only support facts.

Premises chosen (ControlLaws, Prop): NonzeroHonestDh, RawCtxSourcePublication.BodyLength (existing AEAD functional law, needed because the Beacon's ValidFrame requires `80 < payload.length`, i.e. a nonempty AEAD body, which Pqxdh.Crypto does not guarantee), Phase1ReadBack / Phase2ReadBack / FrameReadBack (abstract message-model read-back laws, frame bytes nonempty), and writer totality (write1, write2, frameWrite). FunctionalDecapsulation passed separately (it is data).

Compiled so far (dev files Base.lean, Dev3.lean, Dev4.lean):
- phase1Run_eq (Phase 1 is `pure` of the writer outcome; via signing_eq/writing_eq/phase1Run_bind).
- beacon_prepare: the Beacon's Phase 2 prefix on an honest response evaluates to the explicit collected inputs (beaconCollected) and metadata; helpers server_conversion, accepts_public, accepts_server, beacon_second_eq, beacon_fourth_eq, beacon_admitted, peer_rootArray, liftCoins_pure.
- beacon_receive: on the Beacon's initial kernel, begin at sequence 1 requests one KDF step and resume opens with material `chainMaterial c receive_chain` (via Refinement KernelRefines.begin_receive_future_trace, initialize_refines, FutureOpenRefines).

## Checkpoint 2 (Beacon honest finish evaluated exactly)

Acc.lean (accumulated, compiles, ~870 lines) now also has: beaconTail, fromPayload_honest, native_hash_hit, native_base, beacon_open (CTX open of an honest record with cached commitment), beaconTail_kdf, arguments_of, beaconMaterial, beacon_raw (raw receive), beacon_afterRoot (stages LE64 keyId ++ payload via B9a afterOpening_of_binding), stage_prefix/stage_root/stage_native (handler compositions), onCtx_simulate, beaconControl, romReduction, rom_root_hit, finish_honest, drop_binding, and the key lemma beacon_finish: under the table hit at the Beacon's root input and the cached commitment, the RR-interpreted finish oracle returns `some payload` and the ghost gets `.beacon m_B` appended then `accept (some ⟨keyId, payload, absBytes AD⟩)`. Next: control adversary + its run, probability framework, NC assembly; then RN (Server collect/client/build).

## Checkpoint 3 (adapted to revised B4a; probability framework compiles)

Revised B4a (95 theorems) adopted. Single point of change for B4a names (Base.lean/Acc.lean header):
`open PqxdhServerAuthExperiment (Setup Codec Checks Adversary gameState body phase1Run Win Ghost GameState liftCoins rom_coins)` and `open PqxdhServerAuthExperiment renaming ServerAuthSpec → ExpSpec, authHandler → expHandler, serverAuthGame → expGame, ServerAuthQuery → ExpQuery, AuthInput → Input, familyCoins → coins, initialState → initial`. Other B4a declarations are referenced qualified or through local `open ... (names) in` on single declarations. Adaptation: the Beacon prefix now runs through B4a's `beaconPrefix`/`liftUnit`; `beacon_prepare` is restated for `(beaconPrefix …).run ()`, new `stage_prepare` (via B4a `simulateQ_liftUnit`), `lift_pure_state`; B4a `liftCoins_pure` used instead of a local copy. `forward`/`record` → `forwardFamily`/`recordTouch`. Added: runAdversary (+_bind/_pure/_query/_coins), advCoins, phase1Result, controlInput, keygenRun, keyError, body_run, keyError_average (sum over keygen of per-key error = kemError), kem_split (generic KEM split of gameState).

### B4a declarations used (running list)
Setup, Codec, Checks, Adversary, AuthInput, ServerAuthSpec, ServerAuthQuery, authHandler, serverAuthGame, gameState, body, phase1Run, phase1Impl, projection, freshBeacon, binding, initialState, Win, W1, W2, W3, Partner, Ghost, Ghost.accept, GameState, Game, familyCoins, liftCoins, liftCoins_pure, liftUnit, simulateQ_liftUnit, rom_coins, forwardFamily, recordTouch, onCtx, stageImpl, beaconPrefix, beaconAuxUnit, beaconAux, beaconNative, beaconFamily, finishOracle, acceptedOf, Accepted.ofStaged, toWord32, unitRatchet, Touch.

## Checkpoint 4 (negative_control PROVED; gate half 1 passes)

Acc.lean (1240 lines) compiles; `negative_control` depends only on [propext, Classical.choice, Quot.sound]. Statement: `1 - kemError setup ≤ (Pr[= true | serverAuthGame setup codec checks true (controlAdversary setup codec payload)]).toReal` under `laws : ControlLaws setup codec`, `functional : FunctionalDecapsulation setup.kem`, `payload ≠ []` (checks arbitrary). Pieces: parsePhase1/parse_honest, controlOf, dhValue, controlBytes, controlKeyId (= 0), controlAdversary (coins e, coins encaps, .hmac zeroSalt rootInput, local root/material/AD/seal, .hash commitment, frameWrite, write2, .finish), identity_conversion, beaconSecond_eq, beaconFourth_eq, beacon_third_eq, beacon_input_eq, randomOracle_cached, run_hmac, run_hash, static_present, phase1Result_some, control_bound (per-key), game_win, negative_control. Uses of laws: nonzero (Beacon DHs and static DH present), bodyLength (ValidFrame 80 < payload length), phase1 + phase1Total, phase2 + phase2Total, frame + frameTotal. No Checks premise (adversary does not run the Server's admission checks). Next: relay_not_win (Server collect/client/build evaluation, material equality, ¬W1/¬W2/¬W3).

## Note (coordinator): pending final B4a renames initialState → initialGameState, hash_step → hashOracle_step
`initialState` appears only in the header renaming line (`initialState → initial`); `hash_step` is not used. The switch is a one-line edit of the header.
- Final B4a (aec2ee2, 106 theorems) adopted: header renaming now initialGameState → initial (hash_step unused).

## Checkpoint 5 (relay_not_win in progress)
Added (compiles): server_verify, honestVerified, honestInputs, run_lambda, apply_map, lambda_bind, lift_bind_apply, beacon_conversion, server_accepts, ephemeral_public, ephemeral_identity, serverPrefix_honest (all checks pass: prefix = sample e, encaps, honest inputs), serverPrefix_eq (all check outcomes), acceptAfter (copy of acceptOracle's continuation, tied by rfl in run_accept), run_accept, acceptAfter_honest (one table read; touch/pending/consumed updates), sealHandler (+_aead/_hash/_frame), tail_seal, tailImpl_kdf_run, send_material, tail_send (first send: record under chainMaterial of the initial send chain, cached commitment, frame bytes, logged context). Next: prepare_commit_fields, build_published (support of the build), material equality Server/Beacon, relay per-key bound.
- Checkpoint 5b: prepare_commit_fields, tailImpl_aux, build_published, material_agree, server_input_eq, honest_localNonzero, run_build, relayFinish/relayBuild/relayAdversary (restructured), relay_after_accept (after an honest accept and with correct decapsulation, no run of build+finish wins: either no acceptance, or partner 0 is the unique partner and its logged seal has exactly the accepted key ID, payload and AD) — all compile.

## Checkpoint 6 (GATE PASSES: both controls proved)
Acc.lean (~2270 lines, backup Acc.gatepass.lean) proves `negative_control` and `relay_not_win`, both with axioms [propext, Classical.choice, Quot.sound]. Added: no_acceptance, acceptAfter_none, relay_bound, relay_not_win. relay_not_win needs no nonempty-payload premise (a published build already implies a nonempty plaintext). Next: cleanup (warnings, docstrings, module docstring), split ControlLaws into RelayLaws (read-backs, nonzero, bodyLength) + writer totality, guards, final compile, report.

## Checkpoint 7 (final module; gate passes)

Final file: /tmp/bc-arc-scratch/c-work/b5a/PqxdhServerAuthNegativeControl.lean (2832 lines; source without guards Acc.clean.lean, backup of the pre-docstring cleanup Acc.clean.bak.lean). Compile command (through the lock): `cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b5a/PqxdhServerAuthNegativeControl.lean`. Result: exit 0, no errors, no warnings from the module (only lake's two "local changes" notices for Hax and aeneas), about 10 s wall time.

Counts: 87 theorems, 35 definitions, 2 abbreviations, 2 structures, 1 instance; 87 repository-form axiom guards (66 on [propext, Classical.choice, Quot.sound], 17 on [propext], 3 on [propext, Quot.sound], 1 with no axioms). Every declaration has a docstring; no `@[simp]`; no forbidden words; `set_option linter.deprecated false in` is used on 9 declarations, as in B4a.

Changes since checkpoint 6: unused simp arguments and deprecated lemma names removed; unused declarations (signing_eq, beaconTail_kdf, stage_root, apply_map) removed; laws split into `RelayLaws` (nonzero, bodyLength, phase1, phase2, frame) and `ControlLaws extends RelayLaws` (phase1Total, phase2Total, frameTotal); `relay_not_win` takes only `RelayLaws`. Added the design's budget items: `advCoins_bound`, `coins_bind`, local `IsServerQuery` (accept, build, reveal) with its decidability instance, `control_no_server` (bound 0 on Server queries), `control_budget` (`AuthBudget … 0 1 1`) and `relay_budget` (`AuthBudget … 1 0 0`). Plain-English module docstring and section headers added; terse docstrings rewritten.

Final statements:
- `negative_control (setup) (codec) (checks) (laws : ControlLaws setup codec) (functional : FunctionalDecapsulation setup.kem) (payload) (nonempty : payload ≠ []) : 1 - kemError setup ≤ (Pr[= true | serverAuthGame setup codec checks true (controlAdversary setup codec payload)]).toReal`
- `relay_not_win (setup) (codec) (checks) (laws : RelayLaws setup codec) (functional : FunctionalDecapsulation setup.kem) (payload : Option Pqxdh.Bytes) : (Pr[= true | serverAuthGame setup codec checks false (relayAdversary payload)]).toReal ≤ kemError setup`

### B4a declarations used (final list, aec2ee2)
Through the header (single point of change): Setup, Codec, Checks, Adversary, gameState, body, phase1Run, Win, Ghost, GameState, liftCoins, rom_coins, and renamed ServerAuthSpec, authHandler, serverAuthGame, ServerAuthQuery, AuthInput, familyCoins, initialGameState. Qualified or through local `open … in`: AuthBudget, IsAcceptQuery, IsRomQuery, IsHashQuery, phase1Impl, projection, freshBeacon, binding, W1, W2, W3, Partner, sealed, beaconInput, firstBeacon, rootInput, Ghost.empty, Ghost.accept, Game, liftCoins_pure, liftUnit, simulateQ_liftUnit, forwardFamily, recordTouch, onCtx, stageImpl, beaconPrefix, beaconAuxUnit, beaconAux, beaconNative, beaconFamily, finishOracle, acceptedOf, Accepted.ofStaged, acceptOracle, serverPrefix, serverAux, sessionImpl, sessionFamily, buildOracle, tailImpl, nativeTail, tailAux, settle, generateEphemeral, encapsulate, toWord32, hmacOracle, hashOracle, unitRatchet, Touch constructors.

Gate result: PASSES. No B4a definition problem found. No LSP files were opened for this stage.


## Checkpoint 8 (review fixes, 2026-09-30)

Review notes: /tmp/bc-arc-scratch/c-work/review-b5a-{meaning,hygiene}-notes.md. Backups before the fixes: Acc.review0.lean (checkpoint 7 source), Acc.review1.lean (after renames, W1 and narrowed totality).

1. W1. `negative_control` now states `1 - kemError setup ≤ (Pr[fun result => W1 setup result.1 result.2.1 result.2.2.1.ghost | gameState setup codec checks true (controlAdversary setup codec payload)]).toReal`. `control_bound` bounds `¬ W1` (the reviewer's proof: the final `Or.inl` dropped). New generic `kem_lower` (lower KEM split) turns a per-key-pair bound on a missed event into `1 - kemError ≤ Pr[event]`. `negative_control_win` is the `serverAuthGame` form, derived in one step from `W1 → Win` and `game_win`.
2. Relay liveness. New `relay_live`: under `ControlLaws setup codec limit`, `FunctionalDecapsulation`, the accepting checks `acceptAll`, `payload.getD registrationWitness ≠ []`, `8 + length ≤ Usize.max`, `length + 88 < limit` and `setup.serverKeyId ≠ core.num.U64.MAX`, `1 - kemError setup ≤ (Pr[fun result => result.2.2.1.ghost.acceptance ≠ none | gameState setup codec acceptAll false (relayAdversary payload)]).toReal`. Per key pair: `relay_live_bound`. New lemmas: `next_key_id_some`, `prepare_commit_some`, `acceptAll`, `Publishes`, `build_publishes` (converse of `build_published`), `seal_written`, `tail_seal_written`, `send_written`. `relay_after_accept` now concludes `¬ Win ∧ (Publishes … → acceptance ≠ none)`; `relay_bound` uses `.1`, `relay_live_bound` uses `.2` with `build_publishes`. The key-ID premise is needed because B4a's initial Server control has `last_key_id = setup.serverKeyId`, and `server_next_key_id` returns `KeyIdExhausted` at the maximum.
3. Witness. Not added to the module: it needs `PqxdhHypothesisWitness` (toyCrypto, toyHmac, toyKem, toyFunctional, Base, baseImpl), whose import adds 77 modules, including PqxdhAuthenticatedEvolvingSecrecy, to the import closure of B5a and of every stage that imports B5a. Left for B5b, as the design places it. Checked in scratch instead: WitnessCheck.lean (module text plus that import plus the reviewer's witness adapted to `ControlLaws … limit`) compiles and proves `control_wins` (Pr[W1] ≥ 1), `relay_loses` (Pr[Win] ≤ 0) and `relay_accepts` (Pr[acceptance] ≥ 1 for `relayAdversary none` with `acceptAll`), all on [propext, Classical.choice, Quot.sound]. B5b can start from it.
4. Narrowed writer totality. `ControlLaws` now takes a size bound `limit`: `phase1Total` (unchanged; Phase 1 candidates have fixed-size fields), `frameBounded` (frame writer succeeds when `frame.payload.length < limit`) and `phase2Bounded` (Phase 2 writer succeeds when its application ciphertext is the frame writer's output on such a frame, for every key ID, ephemeral, identity and KEM ciphertext). `negative_control` takes `short : payload.length + 88 < limit`. Helpers `frame_written`, `phase2_written`, `protected_length`.
5. Renames and hygiene: `sourceDhReply_some` → `dhReply_of_nonzero`, `keyError` → `keyPairError`, `keyError_average` → `keyPairError_average`, `beacon_second_eq` → `beacon_staticDh_some`, `beacon_fourth_eq` → `beacon_oneTimeDh_some`, and also `coins_bind` → `advCoins_bind` (it clashed with PqxdhProtocolRegistration.coins_bind). Docstring references qualified (`PqxdhChallengeSecretRouting.FunctionalDecapsulation`, `PqxdhServerAuthAssumptions.NonzeroHonestDh`, `RawCtxSourcePublication.BodyLength`, `PqxdhServerAuthAssumptions.X25519ClassLaw`); `ReadWritable` dropped. The B4a header open line (single point of change) now also opens `W1 W2 W3 acceptOracle` so that the docstring references resolve. `relay_bound` states `none`. Budget docstrings say "at most". ControlLaws docstring says the Beacon publishes. Module docstring rewritten (W1, liveness, narrowed totality, witness deferral).

Checks: every backticked identifier in the docstrings was run through `#check`; the only unresolved tokens are the namespace `PqxdhServerAuthExperiment`, the design names `ctx_seal_open` and `honest_session_accepted`, and parameter names (`e`, `seed`, `limit`). Under the planned B6 header (`open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointDhExtractRoot PqxdhServerAuthExperiment PqxdhServerAuthNegativeControl`) all 141 module names resolve without ambiguity (Collide.lean).

Final: PqxdhServerAuthNegativeControl.lean, 3293 lines, 100 theorems, 37 definitions, 2 abbreviations, 2 structures, 1 instance, 100 guards (78 on [propext, Classical.choice, Quot.sound], 18 on [propext], 3 on [propext, Quot.sound], 1 with no axioms). Compile through the lock: exit 0, no errors or warnings from the module (only lake's two "local changes" notices), about 12 s. `set_option linter.deprecated false in` on 13 declarations.

B4a declarations newly used in this checkpoint: IsAcceptQuery, IsRomQuery, IsHashQuery and AuthBudget (unchanged), W1 (now in the statement of negative_control), Ghost.accept (in relay_after_accept), settle, tailAux, tailImpl (in build_publishes), initialGameState via `initial` (server control and peers).
