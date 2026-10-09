# Private suffix-cache observation law

`PqxdhRecordFactsPrivateCache.replay_observation` compares the existing per-key shared replay interpreter with an interpreter that omits the private hash-cache lookup whose value a replay receive discards. This is an exact distributional statement about a complete adaptive `ReceiveSpec` continuation, starting from any supplied state. It introduces no cryptographic assumption or security bound.

## What is retained

The compared observation is the program's full returned result together with `AdaptiveCtxSharedHash.Local` and the shared public hash cache. Thus it includes every successful seal, nonce history, public input, private input, and raw-attempt count. The replay optional plaintext is unchanged. Every adversary-visible coin and public hash query still uses the existing linked interpreter. Honest seals still use the existing AEAD output and the actual lazily sampled private suffix digest; they may reveal a digest whose private lookup was postponed. The only projected-away field is the private suffix dictionary.

The `LawEq` conclusion quantifies over arbitrary probability-program continuations of that entire observed result. It is stronger than equality of a single marginal return bit. `replay_observation` also permits arbitrary initial private and public caches: it does not silently replace an initial cache with an empty one.

## The exact raw step

For any raw attempt, `rawBase` increments `rawAttempts`, including parser rejection. If parsing fails, it returns `none`, performs no private query, and adds no private input. If parsing succeeds, it records the exact `outerSuffix` point in `privateInputs` and returns the same `replayPlaintext` lookup against the prior successful-seal history as production's modeled replay interpreter. It leaves the suffix dictionary alone and records the point as a deferred completion.

`raw_factor` shows that running this step and then completing that point reconstructs the existing `AdaptiveCtxSharedReplay.linkedImpl` raw step exactly, including the entire state. The comparison does not put an unobserved plaintext in the submitted bytes or change the receive target.

## Why later seals remain correct

A discarded lookup may precede a later seal at the same suffix. Simply treating that later lookup as initially absent would lose the correlation. The proof instead uses the existing `LazyOracleDiscard` commutation theorem for a genuine lazy random-oracle cache. Completing a cache point before any subsequent erased step has the same distribution as completing it afterward. This includes a subsequent seal that queries that same point and returns its digest.

`suffixLens` focuses only the suffix dictionary inside the nested local/shared state. `localRead_commutes` and `localUpdate_commutes` frame the histories around this dictionary; `privateLookup_exact` identifies the existing lookup with the ordinary lazy random-oracle operation; `privateAccess_commutes` retains the private-input log when applying lazy-query commutation. `seal_commutes` derives the result for the whole seal program, and `sealing_exact` identifies that program with the existing linked seal handler.

`rawBase_commutes` handles the parser and replay dictionary. `linked_nonraw_commutes` covers coins, public hash queries, and seals. `pointed_factor` and `pointed_commutes` assemble every query kind, then `replay_observation` applies `LazyOracleDiscard.discard_erase_proj` to the entire adaptive program. No generator order is exchanged using a marginal-distribution premise.

## Query accounting and scope

The compared programs have the same logical raw-attempt count and exactly the same private/public input logs. Their internal uniform-draw counts may differ because the erased interpreter omits cache completions whose values are never used. The theorem does not assert cost equality and does not reduce any source or reduction query budget. Applications must continue to charge the original interpreter's permitted private lookups and draws, and must account separately for any statistical bound proved in the erased game.

This module is a per-key operational helper. It does not yet lift the law to the global record world, prove `OriginStatement` or `BindingStatement`, or supply a publication-guessing or collision bound. It covers the replay endpoint; the random-seal endpoint needs its own extension. The primitive contracts, arbitrary raw decoder, and source/model correspondence remain those of the imported interfaces. It neither models snapshots nor asserts physical erasure.

## Validation and integration

All thirteen public theorems have guarded `#print axioms` checks. Only Lean's ordinary `propext`, `Classical.choice`, and `Quot.sound` appear. The module was checked directly against the published central `959b715460dbc271ff2c617df9dd64f1d0f73234` dependency basis in a private output directory. No Rust or ProVerif file changes are involved.

Root import, maintained analysis text, and reviewed trust-boundary inventory updates are deferred to the integration stage. This guide is a local theorem explanation, not a claim that the full record-lift milestone is complete.
