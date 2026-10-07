# Handoff item 2: implementation plan for the correlated Extract/HKDF hybrid at the actual joint sampler (revision 2)

Snapshot of the working plan, copied on 2026-10-08 from the scratch file `/tmp/bc-arc-scratch/extract-design/plan.md` (SHA-256 `cab40d7b9c2fb48aac9d97de65dd1499cf7c94dab5f23d3297e1fd97380c240e`). The authoritative decisions are in its numbered decision sections (sections 16 to 19); later changes live in the scratch copy until the next integration.

Status: design plan only, revised on 2026-10-06 after the adversarial critique `critique.md` in this directory. It comes from a read-only survey of the central worktree `/tmp/beaconcrypt-authenticated-root-completion` (branch `codex/full-proof-composition`, commit `bccd853e`) and the two maps `map-kdf.md` and `map-consumers.md`. No module, document, commit or push was made; the previous text is kept as `plan.v1.md`. Every critique point was re-checked against the source at `bccd853e` and the VCVio package of the stage D `LEAN_PATH` before it was accepted or rejected (section 15).

Scratch Lean checks, all with Lean 4.34, `-j1 -M8000`, timeout 180, under `/tmp/bc-arc-scratch/lean.lock`, with the stage D `LEAN_PATH` and no artifact output:

- `probe/DesignProbe.lean` (first version) printed 19 signatures: `authenticated_selected_opaque`, `expanded_uniform_bound`, `expandedGame_eq`, `PqxdhCorrelatedExpandHybrid.uniformGame`, the five key-schedule hops and `init_split`, `keySchedule_bound_context`, `stepExpandReduction_query_bound`, `romImpl`, VCVio `identical_until_bad_with_flag`, `probEvent_exists_finset_le_sum`, `owner_realization`, `tail_observation`, `rom_history_append`, `PqxdhCorrelatedExtractFamily.randomGame` and `extractRealGame`. It exited 1 because `client_root` was outside its imports.
- `probe/RevisionProbe.lean` printed 18 further signatures: `KemOpaqueCosts.client_root`, `KemOpaqueSuffix.program_native`, `PqxdhServerAuthBeaconFactor.primitive_factor`, `native_tail`, `beacon_afterRoot_factor`, `PqxdhPhase2DhRootConsumer.afterRoot_source`, `withRoot`, `PqxdhServerAuthEntryFactor.source_factor_services`, `PqxdhRegistrationSchedule.sourceKind`, `uniformCost`, `selected_game_uniform`, `logged_server_send_factor`, `postDecapsulation`, `publicFamily`, VCVio `tvDist_simulateQ_run_le_probEvent_output_bad`, `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage`, `Pqxdh.INFO_PQ_ne_INFO_R` and `rootHybrid`. Two names failed because they were given the wrong namespace.
- `probe/RevisionProbe2.lean` (exit 0) printed those two under their real namespace: `PqxdhServerAuthEntryFactor.relTriple_until_bad`, `probEvent_le_until_bad`, `done_run` and `eager_run`.

Every other citation was checked by reading the source.

Prefixes: `C/` is `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/` of the central worktree. VCVio paths are relative to the package in the stage D `LEAN_PATH`.

## 0. Recommendation and scope of this plan

This plan delivers the registration segment of handoff item 2, not all of item 2. It proves a real-to-ideal-keys transfer for source14, from T6's opaque KEM-ideal game to a game in which the selected root and the first record's keys in both directions are ideal. Evolving keys, skipped keys, record replay and later records cannot be expressed in source14, because source14 has no record send or receive command (its requests are create, bundle, accept, build, finish, hmac, hash and reveal, plus field reads). Item 2 is therefore complete only when the same ordered hybrid is carried into item 3's common experiment. Section 10 and owner input 6 describe how this plan is built so that this carry-over reuses its handler-level lemmas instead of redoing them.

Take route R1 for item 2 (owner decision 2). R1 introduces no new primitive game, but it extends the scope of two listed items from Server authentication to this line: the restricted zero-salt 192-byte Extract random oracle (an idealization, `formal-verification-analysis.md:809`, `composition-assumptions.md:63`) and the Extract PRG-type game on an independent uniform 32-byte input (an additional assumption, `formal-verification-analysis.md:806`). That extension needs owner decision 2 and owner input 2. No item-2 statement is published before decision 2.

Under R1, the hidden-candidate root step costs a statistical guessing term with coefficient one, `(qHmac + qAccept + qFinish) / 2^256`. This needs the prefix-dependent form of G1 in section 3. Every later step is an existing ordinary game: the HMAC-SHA-512 PRF (standard) and the Extract PRG-type game on `uniform32` (additional, as above). The non-standard correlated Extract family is not used.

The hybrid runs in this order, starting from T6's opaque KEM-ideal game:

1. equalities that remove the candidate from every program and private observer;
2. one statistical step that splits the shared table into a public table and a hidden coordinate-keyed table, valid only because the slice is a random oracle;
3. the existing ordered root-Expand hybrid;
4. equalities that make the first candidate entry's 108-byte schedule the only thing its consumers read;
5. the existing key-schedule chain (four hops and one zero-loss split);
6. composition with T5.

## 1. Facts re-checked for this plan (central `bccd853e`)

**Start game and candidate draw.**
- `opaqueBranch` is at `C/PqxdhRegistrationJointKemRawOpaque.lean:304-316`. The candidate draw `uniform ← $ᵗ MlKemSharedSecret` is at :312, after `sourcePreOpaque` and the challenger encapsulation.
- `opaquePost` (:265-280) passes the candidate only to `PqxdhDynamicKemJointRouter.post` (which wraps `PqxdhDynamicKemRouter.post`) and to `opaqueResume`.
- `authenticated_selected_opaque` (:328-361) states `𝒟[event <$> split …]{true} ≤ 𝒟[opaqueBranch … kemIndex index false]{true} + ofReal(IND-CCA + correctnessError) + Σ_target jointEUF`. Its premises are `functional`, `shortRejects` (with `setup.wiring`), `certified` and `capacity`.

**The decision.** `KemGame.decision` (`C/PqxdhRegistrationJointKemGame.lean:14-17`) returns `outcome.1.1` when `result.2 = some (some outcome, _)` and `false` when the selection is inactive or the run stopped. `outcome.1.1` is `decideTag decision`: the adversary's decision together with "the selected accept returned a session" (`C/PqxdhRegistrationJointAcceptCutTag.lean:27-34`). It reads no native state, history, ghost or transcript, but it does read the stop status, so every erasure must preserve stop status.

**The shared table in source14.** All honest and adversary reads of the zero-key 192-byte slice go to one `HmacOracle.randomOracle` cache in the native state, directly, not through `PqxdhExtractRomFamily.romImpl`'s `.derive` requests:
- The Server root: `KemOpaqueClient.romRoot` (`C/PqxdhRegistrationJointKemOpaqueClient.lean:57`) calls `PqxdhServerAuthNative.romRootBytes` (`C/PqxdhServerAuthNative.lean:18-26`). It reads `state.1.cache` and appends `.derive message (some prk)` and `.publicHmac prk rootExpandInput …` to the history. `loggedRoot` adds a ghost touch (:409-413).
- The Beacon root: `sourceRoot` (:1153-1157) reads the same cache and writes no history. Source14's Beacon tail is `sourceBeaconTail = withRoot (sourceRoot setup.hmac) (nativeCtx ∘ beaconNative)` (:1187-1189).
- The adversary's `.hmac`: `publicFamily` (`C/PqxdhRegistrationJointPublicShared.lean:15-23`) reads the same cache when the key is `zeroSalt` and the message is 192 bytes long, and is real otherwise. It is definitionally `romImpl`'s `.publicHmac` branch (`family_source`). The `hmac` wrapper adds a ghost touch.
- `eraseObservers` (:1149-1150) clears the family history and the ghost. `tail_observation` (:1206) is the existing erasure law for the Beacon tail.
- The honest ratchet never touches the table: Beacon and Server ratchet requests are answered by `RawCtxSourceHkdf.response setup.source.crypto` (`PqxdhServerAuthBeaconFactor.native_kdf`, `C/PqxdhServerAuthBeaconFactor.lean:393`).

**The candidate in the router and pool.**
- `PqxdhDynamicKemRouter.postDecapsulation` (`C/PqxdhDynamicKemRouter.lean:64-76`) returns `some candidate` exactly when `index = selected ∧ ciphertext = challenge`. Other owners decapsulating the same ciphertext with their own keys get their real outputs.
- The router's `.decapsulate` branch records the query and its reply in the pool transcript (`record (.decapsulate index ciphertext) reply state`, :49-51; `PqxdhLiveKemBirth.record`, `C/PqxdhLiveKemBirth.lean:33-34`). `PqxdhLiveKemRouting.preImpl` (`C/PqxdhLiveKemRouting.lean:138-143`) keeps a similar history. Neither the router nor `preImpl` reads its transcript.

**Root input layout.** `PqxdhCorrelatedExtractFamily.familyInput m s = padFF32 ++ m ++ s`, with `familyInput_source` relating it to `hiddenRootIKM` (`C/PqxdhCorrelatedExtractFamily.lean:23-31`) and `KemOpaqueClient.accepted_bytes` (:30) identifying the Server's bytes. `randomImpl`/`randomGame` (:42-53) are the ideal side only; no advantage term of that module is used.

**Root Expand.**
- `PqxdhCorrelatedExpand.compile` (`C/PqxdhCorrelatedExpand.lean:23`), `expandedGame` (:171, starts from the empty cache) and `expandedGame_eq` (:175): the random-PRK family game with real Expand equals the root-valued game.
- `PqxdhCorrelatedExpandHybrid.expanded_uniform_bound` (`C/PqxdhCorrelatedExpandHybrid.lean:289`): for any client `OracleComp RootSpec Bool` with `IsQueryBoundP IsRoot q`, the distance to `uniformGame` (:156) is at most `Σ_{i<q}` of one-query HMAC PRF advantages of `indexedReduction` (:226). This `IsRoot` (:114) counts every root query, cache hits included. It is a different predicate from `KemOpaqueCosts.IsRoot` (`C/PqxdhRegistrationJointKemOpaqueCosts.lean:15`), which `client_root` (:22) bounds by 1.

**Key schedule.** In `C/PqxdhServerAuthKeySchedule.lean`:
- `rootHybrid` (:124) is `root ← $ᵗ RootOutput; D (fromRoot source root)`.
- After it come four hops, each an equality with one reduction's advantage: `initExtract_hop` (:314), `initExpand_hop` (:323), `stepExtract_hop` (:331) and `stepExpand_hop` (:339). Between the second and third hops sits the zero-loss distribution equality `init_split` (:259).
- `initExtract_hop` and `stepExtract_hop` take `SourceFullCorrect` (`C/PqxdhFullSecretInputKdf.lean:148`).
- G2 below is exactly the middle segment of the proof of `keySchedule_bound` (:346-372).
- Query bounds: `rootExpandReduction_query_bound` (:414), `initExpandReduction_query_bound` (:420) and `stepExpandReduction_query_bound` (:429).
- `fromRoot_model` (:188) ties `Output` to `Pqxdh.ratchetOut` on the left chain of `Pqxdh.rootChains`, followed by the right chain.

**Per-call factor lemmas for the same native code.**
- `PqxdhServerAuthLoggedSendFactor.logged_server_send_factor` (`C/PqxdhServerAuthLoggedSendFactor.lean:367`): `simulateQ (tailImpl …) (PqxdhServerRegistrationPublication.build source pending root …)` equals a factored build that consumes only the 108-byte material. Source14's build uses exactly this program (`C/PqxdhServerAuthNative.lean:505-520`).
- `PqxdhServerAuthBeaconFactor.primitive_factor` (`C/PqxdhServerAuthBeaconFactor.lean:319`) is generic in the monad `m`, in the primitive handler (given its ratchet branch is `RawCtxSourceHkdf.response`) and in `prepared : PqxdhBeaconPhase2Preparation.Prepared Response`. It states that `PqxdhBeaconPhase2Publication.afterRoot decode prepared (rootArray root)` consumes only `factor source root`.
- `native_tail` (:373) rewrites `beaconNative ∘ₛ nativeTailAdapter` to `sourceTail (nativePrim …)`.
- `beacon_afterRoot_factor` (:404) is their composite for `PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending` with `pending : PqxdhPhase2DhMetadata.Prepared Response`. Its bridge to an `original` preparation is `PqxdhPhase2DhRootConsumer.afterRoot_source` (:32-38), which needs `PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending` for one Beacon prekey `scalar`.
- `PqxdhPhase2DhRootConsumer.afterRoot_unchanged` (:111) and `raw_unchanged` (:101) show that `withRoot` changes nothing after the root callback.
- `PqxdhServerAuthEntryFactor.source_factor_services` (`C/PqxdhServerAuthEntryServices.lean:36`) is the service-level template.
- `revealKernel` (`C/PqxdhServerAuthExperiment.lean:511-512`) reads only installed peer kernels, never a pending root.

**Generic tools.**
- `PqxdhServerAuthEntryFactor.relTriple_until_bad`, `probEvent_le_until_bad`, `done_run` and `eager_run` (`C/PqxdhServerAuthEntrySimulation.lean:88,122,142,160`). The until-bad pair allows distinct state types `σ₁ σ₂`.
- `key_first` and `key_first_context` (`C/PqxdhServerAuthCtxMaterial.lean:95,112`).
- VCVio `tvDist_simulateQ_run_le_probEvent_output_bad` (`VCVio/ProgramLogic/Relational/SimulateQ/Epsilon.lean:202`). It needs both handlers over one `StateT (σ × Bool) (OracleComp spec')`, agreement on unflagged transitions and a monotone flag, and bounds the tvDist by the flag probability in the run of `impl₁`.
- VCVio `probEvent_exists_finset_le_sum` (`VCVio/EvalDist/Monad/Basic.lean:917`), `ProbComp.boolDistAdvantage_triangle` (`VCVio/CryptoFoundations/SecExp.lean:102`) and `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage` (:123). The older `probOutput_true_le_add_ofReal_boolDistAdvantage` (:129) is deprecated and is not used.
- The tvDist-to-advantage pattern is at `C/AdaptiveCtxPrefixValidation.lean:151-166`.

**Bill kinds and bills.**
- `PqxdhRegistrationSchedule.sourceKind` (`C/PqxdhRegistrationScheduleResources.lean:16-25`) numbers the request kinds: 3 accept, 5 finish, 6 hmac. T5's `budget` ranges over `PqxdhRegistrationJointRevealCosts.SourceKind = Fin 9 ⊕ Fin 5` (`C/PqxdhRegistrationJointRevealCosts.lean:17-22`), and `.inl` lifts these kinds. The plan writes `qAccept = budget (.inl 3)`, `qFinish = budget (.inl 5)` and `qHmac = budget (.inl 6)`.
- `PqxdhRegistrationSchedule.uniformCost caps qInit` (:34-36) already includes every table draw: 64 per `.hmac`, `96 + encapsCost` per accept (32 scalar plus one 64-byte table miss, `PqxdhServerAuthNativeUniformCosts.accept_uniform`) and `69 · max 64 decapsCost` per finish (including `sourceRoot_uniform`).
- `selected_game_uniform` (`C/PqxdhRegistrationJointAcceptCutEuf.lean:118-125`) takes `initBound` and `KemBound setup caps`.

**Contracts already inside `setup`.** `ProductionHkdfPrefixConsistent` (`C/PqxdhJointKdf.lean:176`) is the field `prefixConsistent` of `FixedHkdfSha512NoSaltSource` (`C/PqxdhJointKdfGame.lean:128-130`), so it already sits inside every `setup.source` of T5. Of the contracts used here, only `SourceFullCorrect` is new to this line.

**Scope of the listed idealizations.** Every listing of the Extract ROM is scoped to Server authentication: `composition-assumptions.md:42,:63`, `formal-verification-analysis.md:809`, `trusted-boundary.md:543` and `audit-0b4039e-remediation-plan.md:93-95`. Stage D keeps the source's ROM root interpreter but explicitly does not choose the KDF backend of item 2 (`registration-accept-kem-join.md:243`, `trusted-boundary.md:847`).

**Fixed-HKDF root consumers that must not be reused.** Several modules look reusable but answer roots by the real fixed HKDF, or rely on the recipient-correctness contract:
- `PqxdhPhase2DecapsulationRouting.derive` (`:35-41`, `.known` branch through `productionHiddenRoot`; the module header relies on supported recipient-correctness);
- `PqxdhCorrelatedExpand.rootPost`, `rootResume`, `rootReduction` and `reduction_expanded_eq` (`C/PqxdhCorrelatedExpand.lean:34-60`);
- `PqxdhChallengeSecretRouting` (`:105`, `:130`, and its `MlKem768RecipientCorrectness` premises);
- HB-102 `PqxdhBeaconPhase2Routed`, whose `.root` answer is `RawCtxSourceHkdf.rootResponse source.crypto input` (`:87`);
- `PqxdhPhase2DhRootConsumer.native_root`, `root_source`, `nativeRootReply`, `root_complete` and `tail_source` (`:55-90`, `:209-240`);
- `KemOpaqueReal.root`, `root_source`, `impl` and `client_source` (the separate fixed-HKDF reading of the opaque client).

In source14 every non-hidden root reads the ROM table, so using any of these would change the backend of other roots, and the step would no longer be an equality. The reusable parts are only these:
- the type `PqxdhPhase2DecapsulationRouting.Shared` and `materialize` (already imported by `KemOpaqueSuffix`);
- the `PqxdhBeaconPhase2Shared` lemmas, which are generic in `interpret : Shared → Word32`;
- `PqxdhPhase2DhRootConsumer.withRoot`, `afterRoot`, `afterRoot_source`, `afterRoot_unchanged` and `raw_unchanged`;
- `PqxdhCorrelatedExpand.compile`, `rootImpl`, `expandedGame` and `expandedGame_eq`;
- `KemOpaqueClient.romImpl` and `romRoot`.

**Rust (authoritative).**
- `finish_registration` returns `None` unless the Beacon is in `InitSent` (`beaconcrypt/src/beacon.rs:401-404`), and every failure calls `abort_registration` (:486-489), which moves to `Aborted` (:176-182). No path re-enters `InitSent` with the same `pq_key` (:270-283, :373). So the owner holding KEM key `k` decapsulates at most once in its life. This is a Rust fact; the Lean-model counterpart is optional stage T.
- The root input is always 192 bytes, because DH4 is mandatory and all-zero DH outputs are rejected. It is built at `beaconcrypt-core/src/pqxdh.rs:380-407` and derived by `derive_root_key_input` (`beaconcrypt/src/pqxdh.rs:46-59`), which is called at `server.rs:414` and `beacon.rs:458`.

## 2. Start game and end game

**Start (H0).** `opaqueBranch setup codec checks ensureInit supplied decision work runtime count kemIndex index false`, joined to T5 by `authenticated_selected_opaque`.

**End (H4 = `idealKeysBranch`).** The same game with the same key generation, prefix, challenger encapsulation, stopped router, CCA evaluation, stop status and decision. It has no candidate draw and the following private root semantics:

- **Hidden reads.** Every root request that would read the shared table at `familyInput m u` instead reads one consistent table keyed by the 128-byte coordinates `m`, whose roots are uniform 32-byte values. These are the Server's selected private root request and every routed Beacon root request, where the owner of KEM index `kemIndex` decapsulates the exact challenge ciphertext. Hidden reads are identified only by public handles: the selected raw-accept ordinal, KEM creation index `kemIndex`, the owner's KEM index and the exact challenge ciphertext. No step compares a value with `u`.
- **Entry 0.** For the first hidden coordinate in execution order (entry 0), the 108 bytes `(key32 ‖ next32 ‖ nonce12, right32)` are drawn uniformly. Entry 0 is the Server's selected session whenever its root derivation is reached. The Server build of the session holding that token, and every Beacon finish whose root hits entry 0, consume only these 108 bytes. Installed kernels contain only `next32` and `right32`.
- **Other roots.** Every other root read reads the public lazily sampled table with real Expand: other sessions, attacker-owned candidates, other KEM keys, other owners decapsulating the challenge ciphertext with their own keys, and the adversary's `.hmac` on the zero-key 192-byte slice.
- **Everything else.** Every other HMAC/HKDF evaluation is the real function.

## 3. Target statements

**G1, generic, new module `PqxdhExtractRomHiddenSuffix`.** Statistical, with no protocol content. The post-phase budget depends on the prefix outcome, so that prefix cache keys and post-cut reads share one cap. This is what gives coefficient one.

```lean
abbrev TableOracle := Pqxdh.Bytes →ₒ HmacBlock                                    -- direct reads of the zero-key 192-byte slice
abbrev HiddenSpec := unifSpec + (PqxdhCorrelatedExtractFamily.ExtractOracle + TableOracle)
def IsDirect : HiddenSpec.Domain → Prop                                            -- `.inr (.inr _)`
-- shared world (literal): one cache starting at the prefix cache; hidden m ↦ read at familyInput m secret; direct x ↦ read at x
-- split world: hidden m ↦ read of a separate Message-keyed cache (ExtractOracle.randomOracle); direct x ↦ read of the public cache
noncomputable def sharedGame (prefix : ProbComp (HmacOracle.QueryCache × C)) (client : C → OracleComp HiddenSpec Bool) :=
  do let p ← prefix; let secret ← $ᵗ MlKemSharedSecret; (simulateQ (sharedImpl secret) (client p.2)).run' p.1
noncomputable def splitGame prefix client := do let p ← prefix; (simulateQ splitImpl (client p.2)).run' (p.1, ∅)
theorem hidden_suffix_bound (prefix client) (Q : ℕ)
    (keys : HmacOracle.QueryCache × C → Finset Pqxdh.Bytes) (residual : HmacOracle.QueryCache × C → ℕ)
    (covers : ∀ p ∈ support prefix, ∀ x, p.1 x ≠ none → x ∈ keys p)
    (bounded : ∀ p ∈ support prefix, (client p.2).IsQueryBoundP IsDirect (residual p))
    (total : ∀ p ∈ support prefix, (keys p).card + residual p ≤ Q) :
    (sharedGame prefix client).boolDistAdvantage (splitGame prefix client) ≤ (Q : ℝ) / 2 ^ 256
```

Proof route for G1 (route (a), chosen; route (b) is the fallback):

1. **Common state.** Restate both worlds over `σ = public cache × hidden map`. The representation handler `sharedRep secret` answers a direct read `x = familyInput m secret` from the hidden map and every other direct read from the public cache.
2. **Representation lemma.** `sharedImpl secret` from `p.1` equals the projection of `sharedRep secret` from `(p.1, ∅)` under `cache x = if x = familyInput m secret then hid m else pub x`, whenever `p.1` has no key of that shape. The proof uses `map_run_simulateQ_eq_of_query_map_eq`; no invariant is needed. A prefix cache that already holds such a key is an initial-collision case, charged through `keys`.
3. **Identical until bad.** `sharedRep secret` and the flagged split handler `splitFlag secret` agree on every unflagged transition. The flag is set exactly when a direct read has the shape `familyInput m secret`, and it is monotone. VCVio `tvDist_simulateQ_run_le_probEvent_output_bad` applies with `impl₁ = splitFlag secret`, so the flag is bounded in the split world, where `secret` is otherwise unused.
4. **Pure-observer lemma.** The flagged split run equals the plain split run with a direct-read log, with the flag computed afterwards as `∃ x ∈ log, ∃ m, x = familyInput m secret`. The plain run does not use `secret`, so the draw is deferred after it.
5. **Union bound per fixed outcome.** Condition on `p` and the log, and apply `probEvent_exists_finset_le_sum` over `keys p ∪ log`. Each point has probability at most `2^-256` (the suffix determines `secret`). A support lemma gives `log.length ≤ residual p` from `bounded`, so the bound for fixed `p` is `((keys p).card + residual p)/2^256 ≤ Q/2^256`, and the expectation over `p` keeps this bound. The template is `CtxNonceAeadIndDollar.modifiedNonceAeadINDDollarRandomProbe_le`.
6. **To the advantage.** Pass from tvDist to the advantage as in `AdaptiveCtxPrefixValidation.lean:151-166`.

Fallback route (b): use `PqxdhServerAuthEntryFactor.relTriple_until_bad`/`probEvent_le_until_bad` with distinct states (one cache against public cache × hidden map), plus a new coupling-to-tvDist lemma. Steps 4 to 6 are unchanged.

**G2, generic, new module `PqxdhKeyScheduleFromRoot`.** For any `D : Distinguisher`, under `correct : SourceFullCorrect source hmac`:

```text
(rootHybrid source D).boolDistAdvantage (PqxdhServerAuthKeySchedule.uniformGame D)
  ≤ (extractRealGame hmac uniform32 (initExtractReduction source hmac D)).boolDistAdvantage (extractUniformGame uniform32 (initExtractReduction source hmac D))
    + (hmacPrfRealGame hmac (initExpandReduction source D)).boolDistAdvantage (hmacPrfRandomGame (initExpandReduction source D))
    + (extractRealGame hmac uniform32 (stepExtractReduction hmac D)).boolDistAdvantage (extractUniformGame uniform32 (stepExtractReduction hmac D))
    + (hmacPrfRealGame hmac (stepExpandReduction D)).boolDistAdvantage (hmacPrfRandomGame (stepExpandReduction D))
```

It is proved from `initExtract_hop`, `initExpand_hop`, `init_split`, `stepExtract_hop`, `stepExpand_hop` and the triangle inequality, as in `keySchedule_bound` (:346-372), and modifies no existing module.

**T7, item-2 registration-segment theorem, new module `PqxdhRegistrationJointKemIdealKeys`.** Two-sided:

```text
(opaqueBranch … kemIndex index false).boolDistAdvantage (idealKeysBranch … kemIndex index)
  ≤ (qHmac + qAccept + qFinish) / 2^256
    + Σ_{i < qRoot} AdvPRF(indexedReduction hmac rootClient i)
    + AdvExt_uniform32(initExtractReduction source hmac entryD) + AdvPRF(initExpandReduction source entryD)
    + AdvExt_uniform32(stepExtractReduction hmac entryD) + AdvPRF(stepExpandReduction entryD)
```

- **Clients.** `rootClient : OracleComp PqxdhCorrelatedExpand.RootSpec Bool` and `entryD : PqxdhServerAuthKeySchedule.Distinguisher` are the explicitly constructed source14 clients of stages S2 and S3.
- **`qRoot`.** It is `1 + qFinish`, or `2` with optional stage T.
- **Premises.** The expected premises are only `certified` (for read and root counts) and `SourceFullCorrect setup.source setup.hmac`. `functional`, `shortRejects`/`setup.wiring` and `capacity` belong to T5 and so enter only T8. Any further premise that turns out to be needed is escalated, not silently added.
- **Docstring.** It states that the step S1c, which removes the hidden entries' dependence on the secret and their reachability by direct reads, is valid only because the zero-key 192-byte slice is modelled as a random oracle (R1), and that R1 also gives the hidden entries at distinct coordinates their mutual independence. Without that idealization it would be the forbidden decorrelation.

**T8, composite, new module `PqxdhRegistrationJointKemKeyTransfer` (theorem `authenticated_ideal_keys`).**

```text
𝒟[event <$> split …]{true} ≤ 𝒟[idealKeysBranch …]{true} + ofReal(IND-CCA + correctnessError) + Σ_target jointEUF + ofReal(ε_item2)
```

- **Terms.** `event` is T5's `Decided ∧ GoodKem ∧ Protected`, and `ε_item2` is the right side of T7.
- **Proof.** It is proved from `authenticated_selected_opaque`, T7 and `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage`, which matches T5's `𝒟[…]{true}` form.
- **Direction.** It is one-sided because T5 is.
- **What it is not.** It is a real-to-ideal-keys transfer for an arbitrary decision. It has no test query and is not a secrecy theorem. A real-or-random test bit belongs to item 3's common experiment, and the module docstring and guide say so.

**T8b, bills companion.** Every reduction in `ε_item2`, with its challenge-query count and its local uniform, base and decapsulation bills, derived from `certified`, `KemBound setup caps` and `initBound` (section 5).

**Optional T7-all (stage S7).** Every candidate entry is ideal, not only entry 0. This adds four key-schedule terms per extra entry. With the tightening lemma that is one extra entry; otherwise an indexed lazy-table hybrid is needed.

## 4. The ordered correlated hybrid

| Step | From → to | Kind | Loss | Discharged by |
| --- | --- | --- | --- | --- |
| S0a | H0 → H0a: erase family history and ghost touches/seals, and the whole KEM pool/router transcript and `preImpl` history (queries and replies), keeping stop status | program/distribution equality | 0 | `eraseObservers`, `tail_observation`, new per-handler projection lemmas with `map_run_simulateQ_eq_of_query_map_eq`, a "never read" lemma for the KEM transcripts, and the decision reading only `outcome.1.1` and stop status |
| S0b | H0a → H0b: the Beacon finish of the owner of `kemIndex` on the exact challenge ciphertext carries `Shared.challenge`; its root request becomes a private `(coordinates, marker)` request; the router is no longer asked that query, so its candidate argument is dead | equality | 0 | `PqxdhBeaconPhase2Shared` (`owner_realization`, `prepare_continuation`, `admitted_exact`, `cleared_related`), `PqxdhPhase2DecapsulationRouting.Shared`/`materialize` only, `PqxdhRegistrationJointPreparation.compiler`, `postDecapsulation`; pattern of `KemOpaqueSuffix.after_replace` and `KemOpaqueSuffix.program_native` |
| S1b | H0b = `sharedGame prefix post` | equality (flattening into a services skeleton) | 0 | new skeleton module; `familyInput_source`, `KemOpaqueClient.accepted_bytes`; small new table-consistency lemmas for the direct `HmacOracle.randomOracle` reads of `romRootBytes`, `sourceRoot` and `publicFamily`; the honest ratchet never touches the table because it is answered by `RawCtxSourceHkdf.response` |
| S1c | `sharedGame` → `splitGame` (H1) | statistical, R1 idealization; the one step that removes the hidden entries' dependence on the secret and their reachability by direct reads (R1 gives their mutual independence), valid only under the ROM | `(qHmac + qAccept + qFinish)/2^256` | G1; the R1 Extract-ROM contract; prefix table-read log and `covers`; cut-split of `certified` giving `(keys p).card + residual p ≤ qHmac + qAccept + qFinish` (precedents `scan_bound`, `tag_bound`, `selected_certified`) |
| S2 | H1 = `expandedGame hmac rootClient` → H2 = `PqxdhCorrelatedExpandHybrid.uniformGame rootClient` | computational, standard | `Σ_{i<qRoot} AdvPRF(indexedReduction hmac rootClient i)`, 1 challenge each | internalization: `rootClient` runs the prefix, key generation, CCA evaluation, BLAKE2b ROM and public table inside the client; equality `splitGame = PqxdhCorrelatedExtractFamily.randomGame (simulateQ (compile hmac) rootClient)`; `expandedGame_eq`; `expanded_uniform_bound`; `IsRoot` bound transported from `KemOpaqueCosts.client_root` and `certified` through the pool, router, generated-finish compiler and CCA wrapper |
| S3 | H2 = `rootHybrid source entryD` | equality | 0 | first-fresh-entry eager sampling (`eager_run`/`done_run`); Server: `logged_server_send_factor`; Beacon: `native_tail` and `primitive_factor` at source14's `original` under `nativeCtx`, with `afterRoot_unchanged` for `withRoot` (fallback: `beacon_afterRoot_factor` through `afterRoot_source` with a per-owner `ReadyRel` built from the owner registry at the finish); pending-root placeholder projection |
| S4 | `rootHybrid source entryD` → H4 = `uniformGame entryD` = `idealKeysBranch` | computational: 2 × Extract PRG-type on `uniform32` (additional, listed, scope extension) and 2 × HMAC PRF (standard) | G2 terms; 1/1/1/2 challenge queries (Extract, PRF, Extract, PRF) | G2; `SourceFullCorrect` |
| S5 | T5 ∘ T7 | composition | T5 terms | `authenticated_selected_opaque`, `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage` |
| S6 (hand-off) | H4 rewritten with the challenger key first (or last) | equality | 0 | `key_first`, `key_first_context`, `evalSPMF_bind_bind_swap` |

Why S1c costs only a guessing term of coefficient one:

1. In H0b the candidate `u` is uniform and is used only as the 32-byte suffix of hidden table reads.
2. The two worlds differ only if some non-hidden read has suffix `u`. The non-hidden reads are the prefix cache keys, the adversary's zero-key 192-byte `.hmac`, other Server roots and other Beacon roots (other keys, other ciphertexts, implicit rejection, and other owners decapsulating the challenge with their own key).
3. In the split world `u` is used by nothing but that test.

Every such read is counted by an existing cap: one table read per accept, one per finish and one per `.hmac`. The prefix's reads and the post-cut reads share that cap through the cut-split.

Why S2 and S4 are ordinary games: after S1c each hidden PRK is an independent fresh uniform block, so the root Expand is HMAC under a uniform secret key. The initializer and step Extracts take as hidden input the uniform root and the uniform first chain. The game no longer contains `u`, so the `Unit`-context `uniform32` sampler applies.

## 5. Losses and query bills

`ε_item2 = ε_rom + ε_exp + ε_ks`, every term with coefficient one:

- `ε_rom = (qHmac + qAccept + qFinish) · 2^-256`, a statistical term that holds for all adversaries. It covers entries cached before the challenge draw and all reads after it, through G1's prefix-dependent residual. If the cut-split proves disproportionately costly, the fallback is the uniform-constant form `2 · (qHmac + qAccept + qFinish) · 2^-256`, which is sound but has coefficient two. Publishing that form needs owner input 10.
- `ε_exp = Σ_{i<qRoot} AdvPRF_HMAC-SHA-512(indexedReduction hmac rootClient i)`. Each reduction makes one challenge query. `IsRoot` counts cache hits, so the conservative `qRoot` is `1 + qFinish`: at most one Server selected root (`client_root`) and at most one routed root per finish attempt. Optional stage T (`PqxdhRegistrationJointBeaconFinishOnce`, a Lean-model terminal-abort lemma) tightens it to `2`.
- `ε_ks = AdvExt(initExtractReduction) + AdvPRF(initExpandReduction) + AdvExt(stepExtractReduction) + AdvPRF(stepExpandReduction)`, all built from `entryD`. The HMAC challenge counts are 1 and 2 (`initExpandReduction_query_bound`, `stepExpandReduction_query_bound`). Each Extract game receives one challenge block.
- No `(L+1)/2^256` value-consistency term arises: every hop is an exact equality with its reduction, and each reduction samples the other entries itself. There is no selection loss, because the target is fixed by public handles.

**Local bills of each constructed reduction (T8b).** Each reduction runs the whole source14 run as local code. Under `KemBound setup caps` and `initBound`, its bills are:

- the per-kind source bill `Σ_kind budget (.inl kind) · PqxdhRegistrationSchedule.uniformCost caps qInit kind`, which already contains every public table draw (64 per `.hmac`, 64 inside each accept's `96 + encapsCost`, the root inside each finish's `69 · max 64 decapsCost`), plus the `32 · (count + 1)` reserved seeds, i.e. the existing `selected_game_uniform` bill `32·(count+1) + total caps qInit budget`;
- the opaque prefix charges `server_prefix_uniform` and `accept_uniform`, carried over to the opaque resumption in stage S8 (the open bill of the stage D guide);
- hidden draws not in the source bill: 64 bytes per hidden PRK up to S2, 32 bytes per uniform root afterwards, and 108 bytes for entry 0 in the ideal worlds;
- KEM key generation, encapsulation and CCA decapsulation as in T5b (one logical decapsulation per finish, `budget (.inl 5)`), and signing `3·qBundle`;
- the existing `client_root ≤ 1`, `client_calls ≤ 4`, `tail_calls ≤ 6` and `client_uniform 64`.

No reduction makes a public query beyond the forwarded `certified` caps. Deterministic primitive evaluation, table lookup and coordinate comparison keep their runtime cost and are not declared free.

## 6. How correlation of repeated ciphertext uses is preserved

- **H0.** One candidate `u` is shared by the Server's private root and every routed Beacon decapsulation of the exact challenge ciphertext under key `kemIndex` (`postDecapsulation`). One table is keyed by the full 192 bytes, so equal coordinates share an entry. Different DH coordinates give distinct entries that share the hidden suffix `u`.
- **S0b.** The marker compiler keeps exactly this sharing: `materialize u .challenge` at every routed root.
- **G1 real side.** This is the exact joint sampler: one `secret` for all hidden reads and one table. The plan never replaces these reads by independent Extract calls, never forms a per-use `SecretInputKdf` instance and never assumes independence.
- **S1c.** This is the only step that separates the hidden entries from the secret: afterwards they no longer depend on the secret and no direct read reaches them, at a cost of the guessing term. Their mutual independence at distinct coordinates comes from modelling the 192-byte slice as a random oracle (R1), in both worlds. Without decision 2 this step would be exactly the forbidden decorrelation; T7's docstring and the guide say so.
- **S2.** `expanded_uniform_bound` keeps equal messages on one PRK and one root.
- **S3–S4.** The Server build and every Beacon finish at entry 0's coordinates read one shared 108-byte value. Kernel reveals answer from the same value.
- **Aliases.** X25519 encoding aliases give equal DH words, hence the same entry. This matches the owner's R1 partnering rule of identical root input (`audit-0b4039e-remediation-plan.md:114`).
- **Equal roots.** Equal roots at distinct coordinates are reproduced exactly by every hop, because each reduction simulates the other entries itself.

## 7. How the KEM value stays out of the public KDF context

- No `SecretInputKdf.Context` or `SecretInputSampler` ever contains `u`. The root step is not a `SecretInputKdf` game: it is G1, in which `u` is a challenger value whose only role in the split world is the deferred guessing test.
- The only Extract samplers used are `uniform32` with `Unit` context, in S4. Their hidden inputs are the uniform root and the uniform first chain, in a game from which `u` has already been removed.
- **Private carriers of `u`, all removed by S0a and S0b before any reduction is formed:**
  - the family history (`.derive` message and PRK, the root-Expand `.publicHmac`);
  - ghost touches and seals;
  - the KEM pool/router transcript and the `preImpl` history, erased whole (queries and replies), so that S0b's removal of the routed `.decapsulate` query is an equality;
  - the Beacon's prepared record and `RootKeyInput`;
  - the cache keys, which S1c moves into a coordinate-keyed hidden table.

  S0a begins with a grep of every state field whose type can hold a `MlKemSharedSecret`, a 32-byte word or a `RootKeyInput`. The grep also covers the identity-routing and signing transcripts (`PqxdhRegistrationJointSigningTranscript.messagesAt`, `PqxdhRegistrationJointRoutedHistory`), and S0a proves, rather than assumes, that they hold no `u`.
- The S2 PRF reductions use `scanSampler` contexts, which hold the client's stopped state. The type `SecretInputSampler (Prefix Bool)` cannot show what its closures capture. The check is therefore a stated lemma, not a type grep: `rootClient` is defined from `splitGame`, which draws no candidate, by the S2 equality `splitGame = randomGame (simulateQ (compile hmac) rootClient)`. A definition-level term grep confirms that `rootClient` contains no `$ᵗ MlKemSharedSecret`.
- Public HKDF and HMAC evaluations are never randomized. Outside the approved slice they are the real function in every hybrid; on the slice they are the same lazy table in every hybrid. Only secret-keyed Expand outputs (PRF) and hidden-input Extract outputs (PRG-type) are replaced. No public projection is masked.
- **Inherited ROM caveat.** `work` is quantified after `setup`, so it can evaluate the real `setup.hmac` on the slice, and that is unrelated to the table. This is the standard random-oracle-model heuristic, and the guide states it. No value is programmed anywhere: the eager sampling of S3 is a distribution equality, not programming.

## 8. Coverage of the handoff list

| Item | Status in this plan (registration segment only) |
| --- | --- |
| Full 32-byte root | Registration segment: uniform and consistent for every candidate entry (H2), via a real 47-byte Expand under `INFO_PQ`. |
| 64-byte initial output, both halves | Registration segment, entry 0 (S4 hops 1–2 and `init_split`). Other candidate entries keep a uniform root and real initial HKDF (optional S7). |
| 76-byte step output and projections `first32`/`second32`/`final12` | Registration segment, entry 0's left chain (S4 hops 3–4). `fromRoot_model` ties the layout to `Pqxdh.ratchetOut`/`rootChains`, and `SourceFullCorrect` ties production HKDF to Extract plus Expand. |
| Labels | Fixed by definitions: `rootExpandInput` (`INFO_PQ`), `firstExpandInput .ratchet` and `expandFull .ratchet` (`INFO_R`), with `Pqxdh.INFO_PQ_ne_INFO_R` (`BeaconcryptCore/Model/Pqxdh/Primitives.lean:93`). Labels are never randomized. The initial/step shared-prefix alias on the root is irrelevant, because no honest step takes the root as input; a coincidence is absorbed exactly by the Extract hop. |
| Both directions | Registration segment, first record only: Server→Beacon uses `key32 ‖ next32 ‖ nonce12` of `step(L)`; Beacon→Server uses `right32 = R`. Later records are not covered (item 3 experiment). |
| Evolving keys | Not covered; needs item 3's record commands. H4 supplies independent uniform seeds `next32` and `right32`. Each later step is `stepExtract_hop` plus `stepExpand_hop` on a uniform chain, after marker compilation of the ratchet kernel (MarkedTransfer15 route) or the HB-112 byte-recognition testers (`3(Etest + Htest + 2^-352 + Q/2^256)` per hop). |
| Skipped keys | Not covered; needs item 3's record commands. At most 51 steps per receive (`RawCtxKdfBudget.begin_remaining`, `C/RawCtxKdfBudget.lean:29`). Each skipped key is one step output stored in `receive_slots`, and a kernel reveal discloses only those descendants. |
| Replay | Registration segment only, by equalities: Server consumed set, Beacon terminal abort, and response replay to other owners counted as direct reads in `ε_rom`. Record replay and consumption need item 4's raw receive lift. |
| Permitted reveals | Registration segment. Server `.reveal` and the Beacon `.kernel` read answer from H4's `next32`/`right32`. Identity, prekey and one-time reads are harmless to item 2, whose entropy comes only from `u` (no DH secrecy is used). A `.kem` read of `kemIndex` stops the run (`GoodKem`). |
| Descendant-only compromise | Registration segment, first record: `key32` is independent of `next32`, `nonce12` and `right32` in H4, so revealing kernels compromises only descendants. No post-compromise security is claimed. |

Not covered by design: forward secrecy against a later disclosure of KEM key `kemIndex` (`GoodKem` is whole-run); persistence, snapshots, codec internals and running-code access; primitive implementations.

## 9. Stages, modules and effort

Effort is in agent-days for one agent using single-module checks. It is re-baselined against the Server-authentication single-entry work (`PqxdhServerAuthEntry*`: 16 modules, about 6,400 lines, for one fixed Beacon and a smaller command set) and the 40–60% underestimate found in the previous join. Lean checks serialize on the single lock, so parallel lanes help only for the generic stages. Module names were checked as unused at `bccd853e`.

| Stage | New module(s) | Content | Effort | Depends on |
| --- | --- | --- | --- | --- |
| S0a | `PqxdhRegistrationJointKemObserverFree` | Field grep (section 7). Observer-free post-phase. Per-handler projection lemmas; whole-transcript erasure of the KEM pool/router and `preImpl` history with "never read" lemmas; stop status preserved. `opaqueBranch … false` equals the observer-free branch. | 4–6 | — |
| S0b | `PqxdhRegistrationJointBeaconOpaqueFinish` | Source14 Beacon finish marker compiler: preparation `.decapsulate` → `Shared`; root request → private `(coordinates, marker)`. Equality with materialization. Dead router candidate argument. | 6–10 | S0a |
| S1a | `PqxdhExtractRomHiddenSuffix` | G1 with prefix-dependent residual: common-state representation, VCVio until-bad, pure-observer lemma, deferred union bound, initial-collision case. | 4–7 | — |
| S1b | `PqxdhRegistrationJointKemPostSkeleton` | Flattened post-phase skeleton parameterized by services `{serverRoot, beaconRoot, table, hiddenBuild, hiddenAfter}`, mirroring `PqxdhServerAuthEntrySimulation.Services`/`skeleton`. Equality with H0b under native services. Backend-generic restatement of `resume_lift`, as a new lemma. | 10–18 | S0b, decision 2 |
| S1c | `PqxdhRegistrationJointKemRomSplit` | Instantiate G1. Prefix table-read log or domain-cardinality invariant for `keys`; cut-split of `certified` into prefix reads and residual. | 4–7 | S1a, S1b |
| S2 | `PqxdhRegistrationJointKemRootExpand` | `rootClient` with internalized state; `splitGame = randomGame (simulateQ (compile hmac) rootClient)`; `IsRoot` transport; `expanded_uniform_bound`. | 3–6 | S1c |
| S3a | `PqxdhRootFirstEntry` | Generic: the first fresh entry of `uniformImpl` is eagerly sampled (`eager_run`). | 1–2 | — |
| S3b | `PqxdhRegistrationJointKemEntryFactor` | `entryD`; Server factor via `logged_server_send_factor`; Beacon factor via `native_tail` and `primitive_factor` at source14's `original` under `nativeCtx`, with `afterRoot_unchanged` (fallback: per-owner `ReadyRel` and `afterRoot_source`); pending-root placeholder; `uniformGame rootClient = rootHybrid source entryD`. | 6–10 | S1b, S2, S3a |
| S4a | `PqxdhKeyScheduleFromRoot` | G2 (generic). | 0.5–1 | — |
| S4b | `PqxdhRegistrationJointKemIdealKeys` | `idealKeysBranch`, T7. | 1–2 | S3b, S4a |
| S5 | `PqxdhRegistrationJointKemKeyTransfer` | T8, and T8b with the S8 bills. | 2–3 | S4b, S8 |
| S6 | `PqxdhRegistrationJointKemKeyFirst` | Key-first form of H4 for item 4 (`key_first_context`). | 0.5–1 | S4b |
| S8 | `PqxdhRegistrationJointKemRootCosts` (+ opaque prefix costs) | Carry `server_prefix_uniform`/`accept_uniform` over to the resumption; reduction bills with `KemBound` and `initBound`. | 3–5 | S2, S3b |
| S9 | — | Guards, guard liveness, scans, inventory, receipts, guide `doc/impl/registration-kem-key-transfer.md`, analysis section, assumption and trusted-boundary updates, independent review and rework. | 5–8 | all |
| X (if staging option (i)) | inside S0a, S0b, S1b, S3b | Handler-level lemmas over an open command sum `SourceSpec + Ext`, with a frame condition on `Ext` handlers (section 10). | 3–6 | owner input 6 |
| opt. T | `PqxdhRegistrationJointBeaconFinishOnce` | `qRoot ≤ 2`: the owner of `kemIndex` decapsulates at most once (Lean-model `InitSent` guard and terminal abort). | 2–3 | S0b |
| opt. S7 | `PqxdhRegistrationJointKemSecondEntry` or generic `PqxdhLazyTableHybrid` | Every candidate entry ideal. | 2–3 with T, 4–6 generic | S4b |

**Totals.**
- The core total is about 50–86 agent-days.
- With the extensibility work X it is about 53–92.
- The optional stages add 4–9.
- If neither X nor staging option (ii) is chosen, about 25–45 of the core days are at risk of rework in item 3.

**Phases.**
- **P0, no decision needed.** These stages are generic or pure source-correspondence equalities:
  - S1a, S3a and S4a are generic and assumption-free, and can start at once in parallel;
  - S0a and S0b are on the critical path.
- **Gate.** Owner decision 2, input 2 and input 6 come before S1b. S1b is the largest stage and is useful only under R1.
- **P1.** S1b, S1c, S2, S3b, S4b, S8.
- **P2.** S5, S6, S9.

**Decision gates.**
- No item-2 statement is published before decision 2. S2, S3b and S4b are standard or equality hops, but their games presuppose the ROM split world.
- After a 1–2 day spike inside S1b, choose between the services skeleton (recommended: S3b reuses it, as the Server-authentication entry proof did) and the layered `relTriple_until_bad` coupling (fallback, risk 1).
- S7 is done only if item 3 makes candidate entries other than entry 0 adversary-selectable test sessions.

## 10. Interfaces handed to items 3 to 5

- **Staging and reuse (owner input 6).** No hop can be appended to H4 as a game, because source14 has no record commands. Evolving keys, skipped keys, record replay and later records must run in item 3's common experiment. Two options:
  - **(i) Recommended: registration segment now, built for reuse.** S0a, S0b, S1b and S3b are proved per handler over an open command sum `SourceSpec + Ext`. `Ext`'s handlers are assumed to satisfy a frame condition: they read neither `u`, nor the KEM pool transcript, nor hidden table entries, nor entry 0's root except through the installed `next32`/`right32` and the 108-byte factor. Source14 is the instance with empty `Ext`, and item 3 reuses the handler-level lemmas with record commands as `Ext`. Theorem-level reuse of T7 would also need T5/T6's opaque branch to be generic in the command set. That is outside item 2 and is decided with item 3.
  - **(ii) Build item 3's experiment first** and run the whole item-2 hybrid once inside it. Only G1, G2 and S3a are reused unchanged.
- **I-4 (CTX, item 4).** In H4, entry 0's `key32` is used exactly once to seal (the Server build consumes the pending token). It is opened by at most one Beacon finish per owner, or at most one in total with the tightening lemma. S6 puts `key32` in the shape of `AdaptiveCtxDynamicKnownKeys.sourceGame`'s challenger key (`$ᵗ CtxKey` first) or of `firstPrepare`/`firstIdeal` (key last); both orders are equal by `evalSPMF_bind_bind_swap`. `nonce12`, `next32` and `right32` are private simulator data, and every other key is a known key computed by the reduction. A KDF request at a hidden chain is answered from the factored value, never from a public random table.
- **I-5 (evolving, items 3 and 5).** H2 is a consistent uniform root table of type `RootOracle.QueryCache` keyed by 128-byte coordinates. This is the shape of HB-111/112's `PqxdhInitialSourceInitialSecrecy.Input` (`other` parameter, `cache : RootOracle.QueryCache`), reached without the correlated-family term. H4 adds entry 0's 108-byte value. Constraints on reuse:
  - The consumer must be re-instantiated with ROM-backed `other` services and a ROM-world `prior`. The existing `prior` (`C/PqxdhInitialPreparedSourceInput.lean:67-69`) is the fixed-HKDF correlated-family preparation `PqxdhCorrelatedExtractFamily.prepare`.
  - Any HB-111/112 lemma that assumes real HKDF for other roots, or for adversary side sessions on the 192-byte slice, does not transfer. The module header says all public HKDF evaluations run as real computations.
  - The common experiment's record commands (item 3) are needed, and the HB-111 `noSign`/`noCreate` restrictions must not be imported.
  - `codex/evolving-record-composition` (`94bc9538`) is not an ancestor of central.
- **Ordering contract for later stages.** Items 3 to 5 continue the same ordered hybrid after the H4-equivalent point of their experiment. Each evolving step adds an Extract on `uniform32` followed by a two-query PRF, and each skipped key the same; then come the CTX hops. They must not re-randomize any value fixed earlier in the chain, and must not use the public table for any value other than the 192-byte slice.

## 11. Risks and fallbacks

1. **S1b size.** Flattening the whole source14 post-phase (owners, identity routing, KEM pool and router, open backend, Beacon tail, build, reveals, field reads) is the largest task, with elaboration-memory risk under `-M8000`.
   - Mitigations: state equalities per handler with `map_run_simulateQ_eq_of_query_map_eq`; keep the skeleton polymorphic in services; never `simp`-unfold the whole program; follow `PqxdhServerAuthEntryFlat`/`EntryState`.
   - Fallback: a layered `relTriple_until_bad` coupling with the cache relation `cache₀ = cache₁ ∪ {familyInput m u ↦ F m}` and per-layer lifting, without flattening.
2. **A missed carrier of `u`.** The KEM pool/router transcript was not in the maps. Grep every state type, the identity transcripts included, before S0a, and prove decision invariance for the complete projection.
3. **Beacon marker compiler (S0b).** It must keep:
   - the exact source order (decapsulation before the four DH calls);
   - the no-op `.eraseShared`;
   - every rejection and abort branch;
   - the stop status.

   Selection is by public KEM creation index, never by comparing secret keys.
4. **`resume_lift` is not generic in the backend.** Add a new generalized lemma; do not modify the existing one.
5. **Read accounting for `ε_rom`.** The cut-split is required for coefficient one. Cache keys at the cut must be covered by a prefix read log or a cardinality invariant, and prefix reads plus the residual must stay within `certified` (precedents `scan_bound`, `tag_bound`, `selected_certified`, the HB-104 `S+51R+K` ledgers). Fallback: `2Q/2^256` with owner approval (owner input 10).
6. **Factor-lemma fit (S3b).** Source14's Beacon tail is `withRoot (sourceRoot hmac) (nativeCtx ∘ beaconNative)` on `original : PqxdhBeaconPhase2Preparation.Prepared Response`.
   - Primary route: `native_tail` plus `primitive_factor`, which is generic in `prepared` and the monad, under a `nativeCtx` lift, with `afterRoot_unchanged` for `withRoot`.
   - Fallback: `beacon_afterRoot_factor` via `afterRoot_source`, with a per-owner `ReadyRel` built from the owner of `kemIndex` in the registry (`prepared_related`, `cleared_related`).
   - The build's seal-ghost logging is erased in S0a before S3b.
7. **"Entry 0".** It is defined as the first hidden read in execution order. It equals the Server's selected session whenever the Server derives its root: the accept is atomic, and the challenge ciphertext is unpublished before it. Otherwise the theorem still holds, about the first hidden entry. `idealKeysBranch` identifies hidden reads by public handles only (section 2). The guide states this reading.
8. **Direction of the composite.** Only T7 is two-sided; T8 inherits T5's one-sided form. Consumers must not claim a two-sided end-to-end distance, and T8 is not a secrecy theorem.
9. **Rejected-route contamination.** Do not use the fixed-HKDF root consumers listed in section 1, or the programming lemmas of `PqxdhHiddenRoot` and `PqxdhJointKdfGame`. Reuse only the parts listed there, VCVio's generic lemmas, and the definitions already used by the opaque client (`hiddenRootIKM`, `KnownPqxdhRootCoordinates`).
   - **Statement check.** No new statement may contain `jointKdfView`, `fixedHkdfSha512JointStream`, `PqxdhCorrelatedExtractFamily.advantage`, `PqxdhCorrelatedExtractFamily.reduction`, `PqxdhCorrelatedExtractFamily.prepare`, `PqxdhCorrelatedExtractFamily.realGame`, `PqxdhJointDhExtractFamily` games, `productionHiddenRoot`, `RawCtxSourceHkdf.rootResponse`, `rootPost`, `rootResume`, `rootReduction`, `PqxdhChallengeSecretRouting.*`, `PqxdhBeaconPhase2Routed.*`, `KemOpaqueReal.*` or `MlKem768RecipientCorrectness`. The check is an exact-token grep, because `FixedHkdfSha512NoSaltSource` legitimately appears through `setup.source`.
   - **Proof check.** A direct-reference constant scan of every new declaration, not the transitive closure (T5's closure may contain some of these), with a liveness test.
10. **Contract creep.** `SourceFullCorrect` enters a headline of this line for the first time (owner input 4). `ProductionHkdfPrefixConsistent` is already inside `setup.source`.
11. **Loose `qRoot`.** `1 + qFinish` is sound but loose; optional stage T tightens it.
12. **Compute.** The machine is shared:
    - one-module checks only;
    - no full `lake build` before the final matrix;
    - Nix only through the locked minimal flake;
    - never `nix-collect-garbage` during proof work.
13. **Name collisions.** Several reused short names (`uniformGame`, `Services`, `resume`, `impl`, `IsRoot`) collide; use qualified names, as stage D did.
14. **Theorem-level reuse needs T5/T6 generic.** Even with option (i), T7 itself is about source14's `opaqueBranch`. Item 3 reuses the handler lemmas, and its own opaque branch must be built. This is the residual rework that option (i) does not remove.

## 12. Points needing owner input

1. **Decision 2, the KDF backend for item 2.** Recommend R1.
   - **Content.** The R1 contract as stated is enough (`composition-assumptions.md:63`; `formal-verification-analysis.md:809`; `audit-0b4039e-remediation-plan.md:93-95,:114`). Item 2 uses only lazy uniform answers on the zero-key 192-byte slice, shared by honest roots and the counted `.hmac` capability. It programs no chosen values, and it is classical only.
   - **Scope.** No new primitive game is needed, but the idealization's scope must be extended from Server authentication to the registration/KEM key-transfer line. The extension is the reason S1c may decorrelate hidden entries. The listing sites to update are `composition-assumptions.md:42,:63`, `formal-verification-analysis.md:809` and `trusted-boundary.md:543`.
   - **Inherited caveat.** The adversary can evaluate the real `setup.hmac` on that slice, and that evaluation is unrelated to the table, as in every random-oracle model.
   - **The alternative.** Fixed HKDF with the correlated Extract family needs approval to extend that non-standard assumption to source14. It also needs a ROM-free source14: T5/T6 re-proved over real HKDF for the Server, Beacon and public HMAC, for which only `KemOpaqueReal.client_source` exists. That is at least 15–25 additional agent-days, and it leaves a non-standard term (the correlated-family advantage) that no standard assumption bounds.
2. **The Extract PRG-type game on `uniform32`.** It is used twice in S4. It is listed as additional (`formal-verification-analysis.md:806`) and named in R1's approved wording ("keep the existing HMAC-PRF and Extract games"). Confirm its use on this line; this is a scope extension.
3. **Target scope.** The main theorem with entry 0 ideal and other candidate entries at uniform roots, or every candidate entry ideal (S7).
4. **Contracts in the headline.** Confirm that `SourceFullCorrect` may appear in T7/T8, in addition to the inherited T5 premises (`functional`, `shortRejects` with `setup.wiring`, and `setup.source.prefixConsistent`).
5. **Statement form and naming.** Confirm the deliverable of the registration segment: two-sided T7 to the ideal-key game, and one-sided T8 (`authenticated_ideal_keys`, a key transfer, not a secrecy theorem) composed with T5. Source14 has no test query; a real-or-random test bit belongs to item 3's common experiment.
6. **Staging (section 10).** T7/T8 do not complete item 2. Choose (i) registration segment now with handler-level lemmas over an open command sum (recommended, +3–6 days), or (ii) item 3's common experiment first. Under either option, confirm that the evolving-key, skipped-key, record-replay and later-record segments of the one ordered hybrid are delivered in item 3's experiment and not claimed before.
7. **`qRoot`.** Conservative `1 + qFinish`, or `2` via the terminal-abort lemma (optional stage T).
8. **Inherited decisions.** Decision 5 (independent review before integration and publication) and decision 6 (existential owner address and unread owner constant) remain open and apply unchanged.
9. **The HB-111 endpoint.** Confirm that connecting to `PqxdhAuthenticatedRootEndpoint.authenticated_uniform_bound` (stage D plan section 9 item 2) is dropped under R1. It is a fixed-HKDF/family route, and its correlated-family term (`:174-175`) is absent here.
10. **Fallback loss.** If the cut-split of `certified` proves disproportionately costly, may `ε_rom` be published in the sound coefficient-two form `2·(qHmac + qAccept + qFinish)/2^256`?

If any step appears to need a premise that is not derivable (for example a router coin law, or an observer that is in fact read), work stops and the step is escalated, not assumed.

## 13. Validation and documentation

**Per module, in dependency order:**
- direct check with the command of the stage D guide and a fresh scratch olean prefix (the first `LEAN_PATH` entry that contains `BeaconcryptCore` must hold every rebuilt dependency);
- empty log, so no deprecated lemma (in particular not `probOutput_true_le_add_ofReal_boolDistAdvantage`);
- an exact `#print axioms` guard per statement allowing only `propext`, `Classical.choice` and `Quot.sound`;
- a guard-liveness file;
- binder, constant and source scans: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe`.

**Specific checks:**
- the exact-token statement grep and the direct-reference constant scan of risk 9, each with a deliberately failing liveness case;
- the S2 lemma that `rootClient` is defined from the candidate-free `splitGame`, plus a definition-level term grep for `$ᵗ MlKemSharedSecret` in `rootClient`, `entryD` and `idealKeysBranch`;
- a grep that `ε_item2` contains only `boolDistAdvantage` terms of `hmacPrfRealGame`/`hmacPrfRandomGame` and `extractRealGame`/`extractUniformGame` with `uniform32`, plus the explicit `2^-256` term.

**After each stage:**
- root import check with `timeout 180`;
- inventory rows and module blocks;
- focused `make -C beaconcrypt-core check-inventory` in the locked minimal flake, with no `comm` warning;
- `git diff --check`;
- a receipt JSON.

**Documentation (no mid-sentence line breaks):**
- the guide `doc/impl/registration-kem-key-transfer.md`: the hybrid table, the S1c decorrelation and its dependence on R1, the entry-0 reading, the ROM caveat, the one-sided composite, bills and staging;
- a plain-English explanation in `doc/formal-verification-analysis.md` (required by AGENTS.md for new proofs);
- once decision 2 is taken, updates to `composition-assumptions.md` and `trusted-boundary.md`. They state that the scope of the Extract ROM and of the Extract PRG-type game is extended to this line, that no new primitive game was added, and that the correlated Extract family is not used.

No production Rust changes, so no mutation testing applies.

## 14. What this plan does not claim

- Completion of handoff item 2. This is the registration segment only; evolving, skipped-key, record-replay and later-record segments are not covered.
- A secrecy theorem with a test query. T8 is a real-to-ideal-keys transfer for an arbitrary decision.
- A bound on public fixed HKDF, any public random-table term, or reuse of the legacy capstones.
- A ROM-to-real-HKDF transfer.
- Forward secrecy against a later disclosure of KEM key `kemIndex`.
- An adversary-chosen test session or global target selection (item 3).
- A primitive implementation proof.
- Coverage of persistence, snapshots, codec internals or running-code access.

## 15. Critique responses

Each point of `critique.md` was re-checked at `bccd853e` before it was adopted.

| Critique point | Verdict after re-check | Where addressed |
| --- | --- | --- |
| 3.1 G1 uniform constants give `2Q/2^256`; VCVio `:202` needs one state type | Accepted. `certified` bounds only the whole run, so uniform `c0`, `qDirect` each need `≤ Q`. `Epsilon.lean:202` takes `impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) …)`. | G1 restated with `keys`, `residual`, `total`; route (a) common state with a representation lemma, flag bounded in the split world (`impl₁`), pure-observer lemma, union bound per fixed outcome, initial-collision case; route (b) fallback; S1a 4–7; S1c cut-split; owner input 10 for the coefficient-two fallback. |
| 3.2 Item 2 not closed; append-only hand-off not realizable; T8 naming | Accepted. Source14's request kinds are 0–8 with no record command (`PqxdhRegistrationScheduleResources.lean:16-25`). Sub-point (b) is adopted with a limit: handler-level lemmas over `SourceSpec + Ext` with a frame condition remove most rework, but theorem-level reuse of T7 would also need T5/T6 generic in the command set, which is outside item 2. | Sections 0, 8 (rows relabelled "registration segment"/"not covered"), 10 (options (i)/(ii)), 14; stage X; risk 14; owner input 6; T8 renamed `PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys` with a "not a secrecy theorem" docstring. |
| 3.3 Contamination guard misses fixed-HKDF root consumers | Accepted and extended. Re-check found further fixed-HKDF items in `PqxdhPhase2DhRootConsumer` (`native_root`, `root_source`, `nativeRootReply`, `root_complete`, `tail_source`), in `KemOpaqueReal`, and `PqxdhCorrelatedExpand.reduction_expanded_eq`. The guard must be a direct-reference scan, because T5's transitive closure may contain these constants. | Section 1 (forbidden and reusable lists), S0b row, risk 9, section 13. |
| 3.4 Decision 2 understated outside section 12; gate too narrow | Accepted. Every ROM listing is scoped to Server authentication, and stage D explicitly leaves the backend open (`registration-accept-kem-join.md:243`). | Sections 0, 1 (scope paragraph), 4 (S1c kind), 6, 7 (ROM caveat), 9 (gate: no publication before decision 2; S1b after it), 12.1–12.2. |
| 3.5 S3b factor fit is more than a `nativeCtx` lift | Accepted, with a cheaper primary fix. `primitive_factor` (`PqxdhServerAuthBeaconFactor.lean:319`) is generic in `prepared` and the monad, so `native_tail` plus `primitive_factor` at source14's `original` avoids the per-owner `ReadyRel`. The `ReadyRel`/`afterRoot_source` route is kept as the fallback. Budget 6–10 kept. | Section 1, S3 row, S3b row, risk 6. |
| 3.6 S2 needs state internalization and `IsRoot` transport | Accepted. `expandedGame` and `randomGame` start from `∅` over `RootSpec`/`FamilySpec`, and `KemOpaqueCosts.IsRoot` is a different predicate. | Section 1, S2 rows (sections 4 and 9), S2 3–6. |
| 3.7 Bills and premise lists not exact | Accepted. `uniformCost` already includes the table draws (`accept_uniform`'s 96 = 32 + 64; finish `sourceRoot_uniform`). `selected_game_uniform` takes `KemBound` and `initBound`. `ProductionHkdfPrefixConsistent` is a field of `FixedHkdfSha512NoSaltSource`. | Section 1 (bills, contracts), T7 premises reduced to `certified` and `SourceFullCorrect`, T8b, section 5, risk 10, owner input 4. |
| 3.8 Transcript erasure order; identity transcripts; type-based sampler grep | Accepted. The router records the query and reply together (`PqxdhDynamicKemRouter.lean:49-51`), so S0b's removal of the query requires whole-record erasure in S0a. | S0a row (whole KEM transcript and `preImpl` history, "never read" lemmas, stop status), section 7 (identity transcripts, lemma replacing the type grep), section 13. |
| 3.9 Effort arithmetic and calibration | Accepted. The old table summed to 39–67. The re-baseline takes the critique's per-stage figures, except that S1c is raised to 4–7 for the prefix read log and cut-split: core 50–86. Extensibility X adds 3–6, and the 25–45-day rework risk is stated. | Section 9. |
| 3.10 Template citations | Accepted. `rom_side`, `derive_then_public`, `public_then_derive`, `rom_cache_mono` and `rom_history_append` concern `romImpl`'s `.derive`, while source14 roots read `HmacOracle.randomOracle` directly. One nuance: `ratchet_input_ne` is a length fact about extracted ratchet requests, not a `romHmac` lemma, but it is still unnecessary, because the honest ratchet is answered by `RawCtxSourceHkdf.response`. | Section 1 (shared table), S1b row. |
| 3.11 Interface I-5 | Accepted. `prior` uses `PqxdhCorrelatedExtractFamily.prepare`, and the HB-111/112 header says all public HKDF runs real. | Section 10 I-5. |
| 3.12 Deprecated lemma; "four hops"; nix wording; entry-0 handles | Accepted. `SecExp.lean:128-129` marks the old lemma deprecated since 2026-09-15. | Section 1 (generic tools, key schedule wording), T8, S5 row, section 13; risk 12; section 2 and risk 7. |
| Status paragraph probe claim inaccurate | Accepted. The first probe printed `identical_until_bad_with_flag`, `keySchedule_bound_context` and `extractRealGame`, and omitted several cited lemmas. Two new probes were run for this revision. | Status paragraph. |
| Citation names: `PqxdhRegistrationSchedule.sourceKind`, `PqxdhServerAuthEntryFactor.source_factor_services`, `Pqxdh.INFO_PQ_ne_INFO_R` path, `SourceKind = Fin 9 ⊕ Fin 5` | Accepted. All were printed by the revision probe. In addition, neither document noted that `relTriple_until_bad`, `probEvent_le_until_bad`, `done_run` and `eager_run` are also in namespace `PqxdhServerAuthEntryFactor`; fixed. | Sections 1 and 8. |
| "`program_native` is not in `KemOpaqueSuffix`; nearest is `PqxdhServerAuthNative.program_native`" | Rejected. `PqxdhRegistrationJointKemOpaqueSuffix.program_native` exists at `C/PqxdhRegistrationJointKemOpaqueSuffix.lean:75` (marker interpretation gives the original suffix), and the revision probe printed it. The original citation was correct; it is kept, now fully qualified. | S0b row. |
| `decideTag` line range `:28-35` | Corrected to `:27-34` (`accepted` at 27-30, `decideTag` at 32-34). The plan's earlier `:33-39` was also off. | Section 1. |
| Decision also reads stop status | Accepted. | Section 1 (decision), section 2, S0a row, risk 3. |
| Section 4 audit: optional `qRoot = 2` needs a Lean-model lemma, not only Rust | Accepted. | Section 1 (Rust), section 5, stage T. |

## 16. Owner decisions (2026-10-06)

- Route R1 is extended to this line: the zero-salt 192-byte Extract step is a programmable random oracle under the explicit contract approved for Server authentication. It must be listed in both assumption lists, and public HKDF evaluations outside that slice stay real.
- Accepted as ordinary primitive games: HMAC-SHA-512 as a PRF, and HKDF-Extract on a uniform 32-byte key.
- `SourceFullCorrect` may appear as a premise of T7/T8, as a functional-correctness contract on a trusted primitive.
- Order: item 3's common experiment is designed first, and this plan is implemented afterwards against it. Lemmas should be written so the common experiment can reuse them.

## 17. Claude's implementation decisions (2026-10-07)

The owner delegated proof-internal choices to Claude.
- S7 is built: every hidden entry is ideal. It reuses Codex's `PqxdhRecordLiftLazyTable`, which is approved as a plan change, and the CE Beacon-side eligibility (CE plan input 6) needs it.
- Stage T is built: the root-query count is 2 instead of the conservative `1+qFinish`.
- The coefficient-one `(qHmac+qAccept+qFinish)/2^256` term is the target. The `2·…` fallback is used only if splitting the read budget proves infeasible, and is documented if used.
- The HB-111 endpoint is dropped under R1, as planned. Family-B results are reused only for their backend-generic components.
- Hidden-entry build and finish keep the `PqxdhServerAuthSendFactor.factored` and `PqxdhServerAuthBeaconFactor.factored` forms, as committed to Codex (CE plan §26).
- The stage order is: S0a, S0b and the generic lemmas G1, S3a and G2 first; then S1b, S1c, S2, S3b, S4b, S7, T and S8; then S5, S6 and S9.

## 18. Service signature fixed by CE-11 (2026-10-07)

Recorded from the CE-11 design revision (`/tmp/bc-arc-scratch/common-experiment/ce11/design-v2.md` §5.4 and §5.7, critique M8). It fixes interfaces only; no stage effort, statement or assumption of this plan changes. Citations are at central `7609c3c8` (`C/` = `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/`).

S1b's skeleton exposes its two hidden-entry services with exactly the field types of `PqxdhServerAuthEntrySimulation.Services` (`C/PqxdhServerAuthEntrySimulation.lean:256`): `hiddenBuild : PqxdhServerRelatedRootConsumer.Returned → Option Pqxdh.Bytes → ServerState → StateT SealState ProbComp (RustM (Option PqxdhServerRegistrationPublication.Response × ServerState))` and `hiddenAfter : PqxdhPhase2DhMetadata.Prepared Response → StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp (Option PqxdhBeaconPhase2Publication.Staged)`, where `ServerState = PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)` (`:244`) and `SealState = RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)` (`:247`). CE's native build already runs on a `SealState` (`PqxdhServerAuthNative.nativeBuild` `:505` runs `tailImpl` on `([], ctx)`), so the CE ideal game uses these services without conversion.

On a hidden entry with 108-byte value `value : PqxdhServerAuthKeySchedule.Output`, S1b and S3b instantiate the services as `(PqxdhServerAuthEntryFactor.factorServices setup codec checks context value).hiddenBuild` and `.hiddenAfter` (`C/PqxdhServerAuthEntryServices.lean:20`): the logged `PqxdhServerAuthLoggedSendFactor.factored` and `PqxdhServerAuthBeaconFactor.factored` with `nativePrim`, both at `PqxdhServerAuthCtxMaterial.factor value` (the forms committed in CE plan §26 and §17 above). CE-11a's `buildFactor_services` and `finishFactor_services` are these fields at `value = joinOutput m seed`, and its erased and split wrappers (`finishErasedSvc`, `buildSplit`, `finishSplit`) have the same types.

S7 keeps the per-slot 108 bytes in Codex's persistent lazy table with state `PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftInterface.Slot n →ₒ PqxdhServerAuthKeySchedule.Output)` (a `QueryCache × Counts`, `C/PqxdhRecordLiftLazyTable.lean:26`), with n = 2 under T, and reads it only through `PqxdhRecordLiftLazyTable.impl j` (`:41`). CE-11a's `represent` erases the counts with `LazyOracleDiscard.impl_project` and needs two properties of S1b's registration core: it reads hidden-slot outputs only through this slot service (`CoreNatural`), and it names the commands at which a slot's 108 bytes are first drawn (expected: the hidden build and the hidden finish, the first-touch classes of CE-11's `allowanceG`).

## 19. Increment 1 built (2026-10-08)

S0a, S0b (with the router completion `opaqueBranch_freeRouter`), G1 (`hidden_suffix_bound`, coefficient one), S3a (`eager_first`, `uniformGame_first`) and G2 (`fromRoot_bound`) are built on `claude/extract-composition` (reviewed at 2fb286d9; review-fix commit 298c42dc: 6 modules, 133 theorems, each with an exact axiom guard, after the guard fix of the two `@[simp]` router lemmas) and reviewed (semantic and hygiene: approve with nits; confirming review of 298c42dc: approve with nits). No planned statement was false, weakened or given a new assumption. Correction found by the semantic review: after S0b the candidate is still a suffix of the shared Extract-table cache keys, so S1c must remove it from the cache keys, not only from the two private interpreters. Re-estimate of the remaining stages: 21-41.5 agent-days, the sum of the per-stage figures (S1b 5-10, S1c 2-4, S2 2-4, S3b 3-6, S4b 0.5-1, T 1-2, S7 1-3, S8 2-4, S5/S6 1.5-2.5, S9 3-5), against the plan's 38.5-66 for the same stages. S1b remains the main risk; it starts from `freeRouterBranch` and must expose the service signature of §18.
