# B8b notes: PqxdhServerAuthEntryFactor (entry factoring)

Task: stage B8b of Milestone B (design /tmp/bc-arc-scratch/c-work/b-design/b-design.md sections 5 (C, D_j, E_j, F_j), 8-10). Owner decision 2026-09-30: two Server oracles `.accept`/`.build` (B4a has pending tokens holding the root).
Worktree (read-only): /tmp/beaconcrypt-authenticated-root-completion. Compile via the shared lock only:
`cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b8b/<file>.lean`
Do not touch /tmp/bc-arc-scratch/c-work/b6/ (B6 runs concurrently). Never lake build, never nix-collect-garbage.

## Checkpoint 0 (exploration, in progress)

Read: design sections 1-10; spike SpikeServerSend.lean + notes; B4a notes + module definitions (lines 1-740 of PqxdhServerAuthExperiment.lean: GameState, authHandler, acceptOracle, buildOracle, finishOracle, hmacOracle, events, entryOwner, EntryEvent); B8a notes + KeySchedule (Output := FullOutput × RootOutput, Distinguisher := Output → ProbComp Bool, realGame = prk ← $ᵗ HmacBlock; D (keySchedule prk), uniformGame, keySchedule_bound, keySchedule_bound_context, withContext).
VCVio tools found: ProgramLogic/Relational/SimulateQ/Basic.lean (relTriple_simulateQ_run, probEvent_le_of_relTriple_simulateQ_run, probEvent_le_of_relTriple_imp), RandomOracle/DeferredSampling.lean (evalSPMF_bind_comm), EvalDist/Monad/Measure.lean (evalDist_bind_bind_swap), StateProjection (map_run_simulateQ_eq_of_query_map_eq).

Plan sketch (to be refined):
- G1: gameState projected to (seed, scalar, ghost); history dropped by projection.
- Eager lemma (generic): lazy handler samples at the start of the designated step (session j's accept, or the Beacon's active finish for j = Q) = sample first then eager handler.
- Identical-until-bad coupling (generic, own lemma via RelTriple): real game vs factored game; bad = adversary table query at the programmed entry; states related up to erasure of roots.
- Factored game: flattened handler over (game state, cache, hidden input, factor); builds of hidden sessions use spike `factored`; Beacon's stage on hidden entry uses the factor.

### Build infrastructure (checkpoint 0)

Scratch modules live in `src/B8bScratch/<Name>.lean` (module name `B8bScratch.<Name>`; declarations still in namespace `BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor`). `./build.sh <Name>` compiles one through the shared lock and writes `olean/B8bScratch/<Name>.olean`, so later scratch modules can `import B8bScratch.<Name>`. `./build.sh --check <abs file>` elaborates a file with the scratch olean path (no olean). Top-level module prefix must NOT be `BeaconcryptCore` (Lean then looks for all BeaconcryptCore oleans in the scratch dir). For delivery, rename modules to `BeaconcryptCore.Computational.*` and fix imports.

### Architecture decided (checkpoint 0)

Chain for fixed j:
1. G = gameState (nested: authHandler over RootSpec, then romImpl ∘ₛ reduction). Flatten with VCVio `simulateQ_mapStateTBase_run_eq_map_flattenStateT` (StateT/Basic.lean:234) → flat handler over (GameState × FamState).
2. Designated step: j < Q: accept query with sessions = j; j = Q: finish query with Beacon phase initSent. `famProg prk` = romImpl∘reduction but a derive miss stores prk. G1E(prk) = flat handler with famProg prk on the designated step only.
   Per-step swap (designated step): 𝒟[flat step] = 𝒟[do prk ← $ᵗ HmacBlock; G1E prk step]. Generic outer eager lemma (done := sessions > j, resp. ¬InitSent) gives 𝒟[G run] = 𝒟[do prk; G1E prk run].
3. Coupling per prk: G1E(prk) vs factored game G3(out := keySchedule prk), generic identical-until-bad RelTriple lemma (own): post (eq answers ∧ R) ∨ (bad₁ ∧ bad₃), bad absorbing, product coupling (`OracleComp.ProgramLogic.Relational.relTriple_prod`, FromUnary.lean) for bad pairs. Transport by `probEvent_le_of_relTriple` (Relational/Basic.lean).
   bad₃ := ∃ R, hidden = some R ∧ Touch.adversary R ∈ touches. bad₁ (j<Q) := GameInv ∧ ∃ R m r, Touch.session j m r ∈ touches ∧ rootInput m = some R ∧ Touch.adversary R ∈ touches; (j=Q) firstBeacon = some m ∧ rootInput m = some R ∧ adversary touch R. E_j → ¬bad₁ via GameInv.sessionOnce / beaconInput.
   R: GameInv on G1E game; ctx, server, sessions equal; beacon equal up to the established kernel; eraseGhost equal; pending equal except marked sessions (root_j = expandRoot prk vs sentinel); cache1 = cache3 + {hidden ↦ prk}; hidden R ∉ cache3; hidden = some R → owner touch with input R exists.
4. G3(out): hand-written flattened handler over State3 (game, cache, hidden, marks); hidden derive replies sentinel and marks the session; marked builds run the log-aware factored build (spike `factored` generalized to tailImpl's seal log); Beacon derive at hidden runs the factored afterRoot (generic Beacon machinery PqxdhInitialGenericBeacon/PqxdhInitialGenericBeaconNative + RawCtxSelectedChain.receive_source) with kernel resolved; adversary table query at hidden: bad, fixed answer.
5. keySchedule_bound_context with context = (seed, scalar, beaconSeed, oneTime, keys, published); D_j := decide E_j of G3 run. uniformEntryGame j := context; out ← $ᵗ Output; D.
No extra (pairs)/2^256 term expected: KDF (kdfImpl) is stateless (kdf_step), CTX cache entries coincide on both sides.

## Checkpoint 1 (2026-09-30 ~19:50): generic lemmas, skeleton, flat couplings compile

Scratch modules compiled (olean in olean/B8bScratch): 
- `Generic` (evalSPMF_bind_congr_support, relTriple_map_same, relTriple_support [inlined product coupling, FromUnary olean is not built], UntilBad, support_run_bad, relTriple_until_bad, probEvent_le_until_bad, done_run, eager_run).
- `Skeleton` (Reply {rejected, root, hidden}, sentinel, Reply.value/isHidden, ServerState, SealState, Marks, FlatState, Services {derive, table, hiddenBuild, hiddenAfter}, afterDerive, acceptStep, afterBuild, buildStep, finishOutcome, finishStep, hmacStep, hashStep, skeleton, realDerive, realServices).
- `Flat` (interp + morphism lemmas, CoinForward, family_coins, interp_liftCoins, interp_simulateQ, interp_onCtx, rom_coinForward, project, run-form lemmas, client_run_flat, derive_couple, accept_couple, interp_run, hmacStep_run, buildStep_run, finishStep_run, interp_run_onCtx_simulateQ, stage_game, coin/reveal/hash/hmac/build/finish_couple).
Proof style that works: `.run` lemmas (interp_run_*), `relTriple_bind (relTriple_refl _)` on shared prefixes, `relTriple_pure_pure ⟨rfl, rfl⟩` at leaves; rfl-lemmas `xStep_run` to unfold skeleton steps (simp does not unfold match-lambda defs under `.run`).
Next: assemble flat_couple (cases on query) + game-level inequality (gameState ≤ skeleton real game), Context/contextSample definitions.
