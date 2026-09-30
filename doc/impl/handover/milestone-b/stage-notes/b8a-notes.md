# Stage B8a notes: `Computational/PqxdhServerAuthKeySchedule`

Module: `/tmp/bc-arc-scratch/c-work/b8a/PqxdhServerAuthKeySchedule.lean`, namespace `BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule`. Worktree `/tmp/beaconcrypt-authenticated-root-completion` (branch `codex/full-proof-composition`, HEAD `7a9190f`). No tracked file edited, no git state change.

## Checkpoint 0: reading done

- Design sources read: `b-design.md` section 3 (`entryLoss`, the five KDF terms and `uniform32`), section 5 (rows E_j and F_j), section 7 (B8a row, wave 3), section 8; plan section 6 headings.
- Existing lemmas read: `PqxdhSecretInputKdf` (`expandReduction`, `extractRealGame`, `extractUniformGame`, `hmacPrfRealGame`, `hmacPrfRandomGame`, `first32_uniform`, `hmacRandom_eq_independentRoot`, `sourceRootAdvantage_le_extract_add_hmac`, `expandReduction_hmac_query_bound`), `PqxdhFullSecretInputKdf` (`SourceFullCorrect`, `expandFull`, `fullExtractReduction`, `fullExpandReduction`, `fullExpandReduction_real`, `fullHmacRandom_eq_independent`, `sourceFullGame_eq_extract`, `joinBlocks_uniform`, `pairSample`, `initialPrefix_expandFull`, `fullExpandReduction_hmac_query_bound`), `RawCtxSelectedInitialSecond.second_observed`, `PqxdhJointKdf` (`productionStream`, `ProductionHkdfPrefixConsistent.ratchetPrefix`), `RawCtxSourceHkdf.response`/`initialResponse` (native 76- and 64-byte adapters are `c.hkdf _ INFO_R 76/64`), spike S (`Factor := RatchetKdfResponse × RootOutput`, `factor source root = (response (chain_0), other)`).

## Plan

Output type `Output := FullOutput × RootOutput` (76 + 32 = 108 bytes). Real function, from the design's `f PRK := (step (first32 init), second32 init)`, `init := HKDF(expandRoot PRK, INFO_R, 64)`:

- `initializer source root := c.hkdf root INFO_R 64` (production 64-byte HKDF, same bytes as `initialResponse`);
- `step source chain := productionStream c (ratchet.address chain)` (production 76-byte HKDF, same bytes as `response`);
- `keySchedule source hmac prk := (step (first32 init), secondChain init)` with `init := initializer source (expandRoot hmac prk)`; the root Expand is the real public HMAC.

Hybrids: real (uniform PRK) → uniform root → uniform init PRK → uniform init (64 bytes) → split into two uniform halves (`second_observed`, 0 loss) → uniform step PRK → uniform 108 bytes. Five reductions: `rootExpandReduction` (HMAC PRF, 1 query), `initExtractReduction` (Extract on `uniform32`), `initExpandReduction` (HMAC PRF, 1 query), `stepExtractReduction` (Extract on `uniform32`, draws the second half itself), `stepExpandReduction` (HMAC PRF, 2 queries, draws the second half itself).

## Checkpoint 1: draft compiled

- Third compile clean. Fixes on the way: `SecretInputSampler Unit` cannot be the expected type of a `do` block (Lean reads `SecretInputSampler` as the monad), so the two samplers carry a `ProbComp (Unit × Pqxdh.Bytes)` ascription; `initializer_eq` closes by `change`/`rw [prefixEq]`/`rfl`; distribution equalities are stated with `𝒟[·]` (measure API) and converted from the existing `𝒮[·]` lemmas with `evalDist_eq_of_evalSPMF_eq`, which removes all `evalSPMF` deprecation warnings without `set_option linter.deprecated false`.

## Checkpoint 2: compiled, guarded (final)

Compile: `cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b8a/PqxdhServerAuthKeySchedule.lean`: exit 0, about 3.3 s wall, about 4.0 GB peak RSS, no errors or warnings (stderr has only Lake's "local changes" notices for Hax and aeneas), all 27 `#guard_msgs` pass. Output in `compile-final.out`/`compile-final.time`.

File: 645 lines, sha256 `b78db5dd0cb9b4eff1ceda607c54a3f7e971ef54e22cf1de21ea6226edf89723`. Imports `PqxdhFullSecretInputKdf` and `RawCtxSelectedInitialSecond` (for `second_observed` and `secondChain`).

Counts: 24 definitions (2 abbrevs), 27 theorems, 27 repository-form guards. No `sorry`/`admit`/`axiom`/`native_decide` word; no `@[simp]`; every declaration has a docstring; module docstring one paragraph per line. Axioms: `initializer_eq`, `step_eq`: `[propext]`; the other 25: `[propext, Classical.choice, Quot.sound]`.

Main statement (namespace `BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule`, opens `PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf`):

```lean
theorem keySchedule_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    (realGame source hmac distinguisher).boolDistAdvantage (uniformGame distinguisher) ≤
      (hmacPrfRealGame hmac (rootExpandReduction source distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (rootExpandReduction source distinguisher)) +
        (extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)) +
        (hmacPrfRealGame hmac (initExpandReduction source distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (initExpandReduction source distinguisher)) +
        (extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)) +
        (hmacPrfRealGame hmac (stepExpandReduction distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (stepExpandReduction distinguisher))
```

Scratch meaning checks (`B8aMeaningCheck.lean`, a copy of the module plus `PqxdhHypothesisWitness` import and 7 checks; output `meaning.out`): (1) `keySchedule_bound` instantiates at `toySource`, `toyHmac`, `toy_full_correct`, so the premise is satisfiable; (2) with the real Extract the two output components are `Pqxdh.ratchetOut c (rootChains c (rootSecret c ikm)).1` and `(rootChains c (rootSecret c ikm)).2`; (3) `uniform32` is the design's sampler by `rfl`; (4) reduction 3 queries `INFO_R ++ [1]` and `rootExpandInput = INFO_PQ ++ [1]` by `rfl`; (5) the Expand messages have lengths 42, 106 and 47; (6) `Fintype.card Output = Fintype.card UInt8 ^ 108`; (7) a deliberately wrong guard fails, as intended (the only error), which confirms the guard mechanism is active.

## Deviations and choices

- The design gives only the name and the five loss terms. Chosen: output type `FullOutput × RootOutput`; the distinguisher is context-free as in the design's `uniform32` (Unit context); added `keySchedule_bound_context` (side information sampled before the PRK, folded into the distinguisher by `withContext`), since B8b's prefix is sampled before the table entry.
- Reductions 1, 4, 5 reuse `expandReduction`, `fullExtractReduction`, `fullExpandReduction` (the Expand ones with the trivial sampler `unitSample := pure ((), [])`); reductions 2 and 3 are new (the 64-byte initializer uses only the first Expand block, so reduction 3 makes one query).
- The step-hop reductions draw the independent second half of the initializer themselves (Unit-context Extract game, as in `entryLoss`).
- Hop lemmas are equalities (`*_hop`); the only inequalities are four triangle inequalities in `keySchedule_bound`.
- Extra helpers beyond the design: `fromRoot_model`, `keySchedule_extract`, `keySchedule_hmac` (for B8b), and the challenge-query counts 1, 1, 2 of the PRF reductions.

## Merge TODO (tracked files, not done here)

- Copy to `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhServerAuthKeySchedule.lean`.
- Add `import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule` to `BeaconcryptCore.lean`.
- `proofs/check-inventory.sh`: `[handwritten-lean]` count +1 (merged once per wave).
- `proofs/reviewed-inventory.txt`: `handwritten-lean<TAB><sha256><TAB>proofs/lean/BeaconcryptCore/Computational/PqxdhServerAuthKeySchedule.lean`.
- Plain-English explanation in `doc/formal-verification-analysis.md` at B11.
