# B6 notes: PqxdhServerAuthGapDh

Task: stage B6 of Milestone B (design /tmp/bc-arc-scratch/c-work/b-design/b-design.md, section 5 A1-A3, "Details of sym_complete", 6.1, 8-10). Module `Computational/PqxdhServerAuthGapDh`, namespace `BeaconcryptCore.Computational.PqxdhServerAuthGapDh`. Main result `badB_le_gapDh`: Pr[BadB | gameState false] ≤ serverGapDhAdvantage (extractor (scanClient …)).
Worktree (read-only): /tmp/beaconcrypt-authenticated-root-completion. Compile via lock only:
`cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b6/<file>.lean`
Do not touch /tmp/bc-arc-scratch/c-work/b8b/.

## Checkpoint 0 (exploration, 2026-09-30)

Read: design; B4a (PqxdhServerAuthExperiment, aec2ee2: two oracles accept/build, GameState has pending, Touch.session has reply, body/gameState/BadB/CandHit/romCandidates/padded/GameInv/AuthBudget, client_run, stage_run, run_rel, run_count); B2 (static_iff, scalar_iff, sourceScalarDh_nonzero, serverGapDhAdvantage, candidate_eq_serverGapDh); B3a (romImpl, rom_public_oracle, rom_derive_oracle, rom_rejected, rom_root, rom_forward, rootExpand_outside); PqxdhJointGapDh (serviceImpl, reply, testInput, testInput_full, sourceInput, candidateGame, extractor_signing, extractor_game_uniform); PublicDomain (serverDomain.available, beaconDomain.available: rejection of a derive is publicly decidable).

Plan:
- SymState = ⟨history, table : List (Key × HmacBlock)⟩, Key = concrete bytes | message m. cacheOf seed scalar table bytes = first entry whose concretization = some bytes (first-wins = randomOracle cache semantics, since the cache only inserts on a miss) -> no invariant needed.
- symImpl on the family Spec over OracleComp AdversarySpec: coins forwarded; sign forwarded to the Gap-DH signing service (exact; body never signs -> scanClient_signing = 0 via a no-sign query bound of body); publicHmac in table domain = lookup (concrete) ; derive = public rejection via domains, else lookup (message).
- `same q e` comparisons: concrete/concrete bytes; concrete/known-third message: testServer (1 decision); concrete/selected-third: testInput (2 decisions); message/message: public coordinates + DH1 by static_iff (class law, fixed reference scalar) + third: known/known bytes, known/selected decideDh true (1), selected/selected scalar_iff.
- sym_step: per query, flattened with serviceImpl (mapStateTBase + flattenStateT), projection drops the Gap-DH history and concretizes the table; proof via stateless service simulation (answers independent of history).
- sym_complete: map_run_simulateQ_eq_of_query_map_eq; then A2 = candidate probability equality.
- A1 badB_candidate: fused two-layer run (simulateQ_mapStateTBase_run_eq_map_flattenStateT of romImpl∘ₛreduction over authHandler), lockstep invariant adversary touches = zero-key 192-byte publicHmac messages of the family history (touches_history, honest_no_rom_public), count via run_count on ghost adversary touches (candidates_length).

## Checkpoint 1 (A2+A3 compile, Dev6.lean, no sorry)

Dev6.lean compiles (few s). Contents: SymKey, SymState(+empty), referenceScalar, decision, ServerAddress, serverBytes, serverCoordinate, testServer, concreteTest, thirdSame, messageSame, symSame, symLookup, symCoins, symRead, symAccepts, symImpl, scanClient, answer (stateless Gap-DH answers), keyInput, symCache, concretize; service_fst (run output independent of decision history), answer_coins, answer_decision, read_second/fourth/kem, assemble_inj, serverCoordinate_some_iff, testServer_answer, input_known, input_selected, concreteTest_answer, thirdSame_answer, messageSame_answer, symSame_answer, symLookup_answer, symCache_append, symRead_answer, symAccepts_iff, symRead_concretize, sym_step, sym_complete, concretize_empty, scanClient_answer, candidate_game, candHit_eq_gapDh (Pr[CandHit | gameState false] = serverGapDhAdvantage (extractor scanClient), premise X25519ClassLaw only).
Design deviation: no flattenStateT; instead `answer` (stateless services) + `service_fst` + `QueryImpl.simulateQ_mapStateTBase_run` + `map_run_simulateQ_eq_of_query_map_eq` (no invariant needed: first-wins = cache semantics).
Next: A1 (touches_history via fused run of romImpl∘ₛreduction over authHandler, honest_no_rom_public, candidates_length), badB_candidate, badB_le_gapDh; then signing/decisions/uniform counts.

## Checkpoint 2 (MAIN RESULT compiles: badB_le_gapDh, Dev14.lean, no sorry)

Added (Dev7-Dev14): IsPublicRoot/IsSignRoot/IsTableRoot (+Decidable), sign_public, table_public, Quiet (+quiet_pure/bind/get/set/modify/liftCoins/forward/record/onCtx), familyCoins_quiet, forward_bound, IsPublicClient, client_quiet, session_step, quiet_session, quiet_accept, quiet_build, IsPublicTail, IsPublicStage, tail_quiet, stage_quiet, stage_step, quiet_stage, quiet_finish, quiet_hash, honest_no_rom_public; adversaryTouches, romMessages, tableMessage, romMessage, romMessage_quiet, tableMessage_quiet, rom_step, rom_quiet, accept_touches, build_touches, finish_touches, adversary_step, fusedImpl, fused_run, Lockstep, fused_lockstep, fused_count, gameState_fused, touches_history, adversary_count, romCandidates_eq, candidates_length, mem_padded, firstBeacon_mem, badB_candidate, badB_le_gapDh.
badB_le_gapDh premises: X25519ClassLaw setup.source.crypto; rom budget `∀ input, (adversary input).IsQueryBoundP IsRomQuery qH`.
Next: resource statements scanClient_signing (0), scanClient_decisions, scanClient_uniform (generic potential lemma run_potential; body derive count ≤ Q+1 via finish single-shot potential), then docstring/guards/cleanup.

## Checkpoint 3 (inner counts compile, Dev17.lean)

Added: run_potential (generic potential bound, k budgets), IsFamilyRequest/IsDeriveRoot/IsCoinRoot (+Decidable), derive_family, Costs (+costs_pure/bind/seq/mono/get/set/modify/liftCoins/forward/record/onCtx), familyCoins_costs, IsClientFamily, client_costs, session_costs, accept_costs, build_costs, IsTailFamily, IsStageFamily, tail_costs, stage_costs, stage_costs_step, initSentFlag (+_zero, _le), finish_costs, familyCoins_bound, hmac_run, hmac_costs, hash_costs, body_bound, body_sign (0 signing), body_table (≤ qH), body_derive (≤ Q+1, potential Q + initSentFlag via finish_step single shot).
Next: outer counts for symImpl∘ₛreduction (sameCost/lookupCost, concreteCount/messageCount, step bounds, table growth), then scanClient_signing, scanClient_decisions (bound 2qH(Q+1) + 2(Q+1)(qH+Q+1)), scanClient_uniform (u + 64(qH+Q+1) given body coin bound u).
