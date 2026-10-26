# B4a notes: PqxdhServerAuthExperiment

Task: stage B4a of Milestone B (design /tmp/bc-arc-scratch/c-work/b-design/b-design.md, owner decisions 2026-09-30: two Server oracles `.accept`/`.build`).
Worktree (read-only): /tmp/beaconcrypt-authenticated-root-completion. Compile via the shared lock only:
`cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b4a/<file>.lean`

## Checkpoint 0 (exploration done, 2026-09-30)

Decisions:
- Game monad `M := StateT (GameState KemSK) (OracleComp RootSpec)`; ProbComp work lifted by `coins` (simulateQ of `.inl` queries).
- `.accept raw : Option Nat` (session index = accept counter), `.build session payload : Option Response`, pending table `Nat → Option Returned`, build consumes entry (Rust moves `RegistrationOutput`, server.rs:429-436).
- Server prefix: `PqxdhServerStaticDhSource.prefixImpl serverDomain serverAux (fun _ => pure ())` on `collect raw`; root: `PqxdhServerRelatedRootConsumer.client binding input` with family forward + `Touch.session index m` log.
- Build tail: ProbComp in `StateT (SharedState (List SealContext)) ProbComp` via `tailImpl` = `registrationImpl ∘ₛ nativeAdapter` + seal log on successful seal (TailSpec `.inl (.inr input)`), lifted. Fidelity lemma planned: projecting the log gives `registrationImpl` run (spike `server_send_factor` applies).
- Beacon finish: `PqxdhPhase2DhStage.stage` under prefixImpl beaconDomain + family forward (Touch.beacon) + native tail on ctx; then `PqxdhBeaconPhase2Publication.finish`; acceptance snapshot write-once.
- owner: `Option (Fin (Q+1))`; Beacon index Q also covers the degenerate "no Beacon input" case (documented); sessions ≥ Q excluded by budget counter invariant.

## Checkpoint 1 (definitions compile)

PqxdhServerAuthExperiment.lean compiles (~4 s) with: Setup, Codec, Checks, Query/QuerySpec/Spec, Input, Adversary, IsAcceptQuery/IsRomQuery/IsHashQuery (+Decidable), Budget, Accepted, Touch, Snapshot, Ghost(+accept), GameState, Game, coins, liftCoins, forward, record, onCtx, toWord32, generateEphemeral, encapsulate, serverAux (StateT (List Bytes) ProbComp), serverPrefix, binding, sessionFamily, sessionImpl, acceptOracle, tailAux, nativeTail, tailImpl (seal log), settle, buildOracle, beaconAux (ProbComp), beaconNative, beaconFamily, stageImpl, Accepted.ofStaged, acceptedOf, finishOracle, hmacOracle, hashOracle, reveal, handler, projection, phase1Impl, freshBeacon, phase1Run, initial, body, gameState, rootInput, beaconInput, Partner, sealed, W1-3, Win, BadB, CollB, touchInput, owner, Entry, romCandidates, padded, CandHit, game, sessionCollGame, Accepted.fields, fields_inj, ofStaged_fields, sealed_fields, sealed_eq_iff.
Convention: `set_option linter.deprecated false in` before decls using Pr[...] (as PqxdhServerAuthAssumptions).
Next: generic lemmas run_rel / count_bound, then Inv/Grows invariant, snapshot_prefix, win_le_games, finish_single_shot, seal_once_per_session (Nodup of seal indices), reveal_post_registration (peers send_sequence = 1), empty_payload.

## Checkpoint 2 (invariant machinery compiles, no sorry)

Added and compiled: run_rel, run_count, run_bind_support (generic); liftCoins_support/mem, coins_support, forward_support, onCtx_support, record_run; Local (+refl/trans, local_of_eq/ctx/record), family_step, sessionFamily_shape, beaconFamily_shape, sessionImpl_step, stageImpl_step; nativeImpl_keeps, sharedImpl_keeps, nativeTail_keeps, tailImpl_log, build_log_length (via build_bound .seal); unitRatchet, build_support (every build result: ok (none, server) or publish with seq-1 kernel, nonempty payload); Inv (frozen, touched, sealedBelow, pendingBelow, pendingFresh, sealOnce, peers), Grows (+refl/trans), inv_initial, inv_of_local, Ghost.accept_* lemmas; accept_step, build_step, inv_of_local_other, finish_step, hmac_step, hash_step, handler_step; run_inv, run_sessions, body_reachable, gameState_reachable.
Next: snapshot_prefix, win_frozen, w3_collB, seal_once_per_session, build_consumes, reveal_post_registration, finish_single_shot, empty_payload, partner_iff_root_input, win_le_games, then docstring + guards + cleanup of unused simp args.

## Checkpoint 3 (all planned B4a lemmas compile, no sorry)

Added: snapshot_prefix, win_frozen, beaconInput_prefix, w3_collB, seal_once_per_session, build_consumes, reveal_post_registration (send_sequence = 1), finish_inactive, finish_phase, finish_single_shot, empty_seal_bound, empty_payload, session_references, session_root_input, beacon_root_input, partner_iff_root_input (input-level, with Beacon-side References/converted hypotheses), owner_some, win_cases, win_le_games (ENNReal, Budget premise, any revealSeed).
Next: rom_coins, tail_native (log projection = registrationImpl run), beaconNative_ordinary; module docstring with restriction list; guards; cleanup of unused simp args/deprecations.

## Checkpoint 4 (complete draft compiles cleanly, 2567 lines, 73 guarded theorems)

Added rom_coins, forgetAux, nativeImpl_forget, sharedImpl_forget, nativeTail_forget, tail_native, beaconNative_ordinary; module docstring with restriction list (docstring.txt); guards generated from axioms-out.txt (73 theorems; sealed_fields has no axioms; others within propext/Classical.choice/Quot.sound). No warnings. Backup: PqxdhServerAuthExperiment.checkpoint4.lean. SpikeLink.lean checks that spike `server_send_factor` rewrites the build tail after `tail_native`.
Remaining: final review, report.

## Checkpoint 5 (DONE)

Final file PqxdhServerAuthExperiment.lean: 2567 lines (2154 before guards), 73 theorems, 73 guards, 0 warnings, ~6 s compile (compile.log). Axioms ⊆ {propext, Classical.choice, Quot.sound}; sealed_fields uses none. No sorry/admit/axiom/native_decide words.
Deviations recorded in the final report (accept returns Option Nat; Budget.accept; consumed as bytes; pending as partial map; owner convention; win_le_games in ENNReal; partner_iff_root_input at reached-input level; reveal_post_registration = send_sequence 1).

## Revision R (coordinator, after three-lens review; notes in ../review-b4a-{rust,notion,hygiene}-notes.md)

Backup of reviewed version: PqxdhServerAuthExperiment.v1.lean. Guards stripped during revision; regenerate at end (theorems.txt/AxiomProbe flow).
R1 DONE: renames Query→ServerAuthQuery, Spec→ServerAuthSpec, game→serverAuthGame, Inv→GameInv, Budget→AuthBudget, handler→authHandler, owner→entryOwner, Entry→EntryEvent, forward→forwardFamily, reveal(def)→revealKernel, initial→initialState, record→recordTouch, coins→familyCoins, Local→LocalStep, Input→AuthInput, family_step→family_local (constructor ServerAuthQuery.reveal unchanged).
Plan: R2 Touch.session gains reply (logged after derive), client_run; R3 liftUnit/beaconAuxU/beaconPrefix/stage_run/BeaconReached; R4 Installed + build_support; R5 GameInv (Reader Response setup publicValue) with provenance/atomic/pinned/initSentClean fields, beacon clauses in steps, phase1_pinned; R6 exports (reveal at reached states, snapshot_atomic, owner_beacon_no_partner, owner_session_partner, seal_touched, pending_root, partner run-level, finish_single_shot run-level); R7 docs + guards.
R2-R5 DONE (compiles, no sorry): Touch.session 3-arg (reply logged after derive), client_run, liftUnit/simulateQ_liftUnit/liftCoins_pure/bind, beaconAuxUnit, beaconPrefix, stageImpl prefix via liftUnit, BeaconReached, ctxOnly_run, stage_run, toWord32_some, beaconReached_facts, phase1_pinned, Installed, fresh_slots_empty, first_send_installed, build_support (kdf hyp, Installed), tailImpl_kdf, GameInv (16 fields), InitSent, SessionOrigin, BeaconOrigin, inv_initial, Ghost.accept_old/new, finish_phase, acceptedOf_none, inv_accept_touch, inv_add_pending, accept_step, build_step (+log conjunct), finish_step, inv_adversary_touch, hmac_step, hash_step, authHandler_step. Removed: sessionFamily_shape, sessionImpl_step, stageImpl_step, family_local (renamed from family_step), beaconFamily_shape, inv_of_local, inv_of_local_other.
Next R6: Reachable/Support/Partnering/Decomposition/Interfaces from partBC.lean adapted.
R6 DONE: Reachable (run_inv, run_sessions, run_inactive, reachable_inv, body_reachable, gameState_reachable w/ challenge publicValue), Support (snapshot_prefix, win_frozen, firstBeacon_prefix, firstBeacon_after, beaconInput_prefix, w3_collB, snapshot_atomic, seal_touched, pending_root, seal_once_per_session, build_consumes, reveal_post_registration [reached states, Installed], reveal_gameState, finish_inactive, finish_single_shot [run-level], empty_seal_bound, empty_payload), Partnering (session_references, session_root_input, beacon_root_input, root_inputs_iff [input-level, no accepted premise], partner_iff_root_input [run-level]), Decomposition (owner_some, find_atomic, owner_beacon_ghost, owner_session_ghost, owner_beacon_no_partner, owner_session_partner, owner_beacon_only_w1, owner_session_not_w1, win_cases, win_le_games), Interfaces unchanged + forward-ref docstring. File compiles clean, 2986 lines (no guards yet).
Next R7: module docstring rewrite, docstring nits, guards, counts.
R7 DONE: module docstring (docstring2.txt) with 12 restrictions; citations fixed; guards regenerated (95 theorems / 95 guards; axioms 76 full, 11 propext+Quot.sound, 7 propext, 1 none). Final compile clean ~7 s (compile.log). SpikeLink re-checked OK. Backup of pre-revision: PqxdhServerAuthExperiment.v1.lean.

## Final fixes after re-check (recheck-b4a-{fixes,regressions}-notes.md)

- Renames: initialState → initialGameState, hash_step → hashOracle_step (CTX-stage clashes).
- GameInv.sealTouched / frozenSealed strengthened to `∃ message root, Touch.session entry.1 message (some root) ∈ …` (seal_touched export likewise). The full link from a seal to the root it was sealed under (key level) is left to B9b's `compiled_build_selected`.
- client_run left disjunct is now `¬ localNonzero input ∧ extra = []`; stage_run left disjunct now carries `∃ final, (none, final) ∈ support (beaconPrefix … .run ())`.
- Docstrings fixed: GameInv, client_run, stage_run, phase1_pinned, reveal_post_registration and module ("receive chain and receive counters are the initial ones, its send counter is one"), restriction 11 (secret getters = reveals excluded by 2 and 7; others public or post-acceptance, beacon.rs:90,114,193,210, server.rs:179-181).
- Ghost session touches carry the derived root (reply). B8b's history_erase must ALSO erase the replies in ghost.touches and in the snapshot touches. Added section Erasure: eraseTouch, eraseSnap, eraseGhost, firstBeacon_erase, beaconInput_erase, touchInput_erase, session_mem_erase, adversary_mem_erase, partner_erase, win_erase, badB_erase, collB_erase, entryOwner_erase, entryEvent_erase (from reviewer's recheck-b4a-regressions-erase.lean).
- Final: 3711 lines (3136 before guards), 106 theorems / 106 guards, 76 defs, 11 structures, 2 inductives, 4 abbrevs, 3 instances; compile clean ~7 s; SpikeLink re-checked. Backup before these fixes: PqxdhServerAuthExperiment.v2.lean.
