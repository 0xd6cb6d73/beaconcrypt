# Per-entry Server authentication and its actual key-schedule reductions

The B8b endpoint is `PqxdhServerAuthEntryFactor.entry_le_uniform`. For every adaptive adversary and selected operation `j : Fin (Q + 1)`, it bounds the original authentication experiment's `EntryEvent` probability by the concrete experiment using one uniform 108-byte selected output, plus five explicitly constructed component advantages. The selected operation is Server accept attempt number `j` when `j < Q`, or the Beacon's first active finish when `j = Q`. It is an operation coordinate, not a public-key comparison, an honest-target premise or an assumption that a root input is fresh.

The five reductions are B8a's root-Expand HMAC PRF reduction, Extract of a uniform 32-byte root, initializer-Expand HMAC PRF reduction, Extract of a uniform 32-byte first chain, and full step-Expand HMAC PRF reduction. They all consume the same `entryReduction`: the real source context sampler followed by the actual adaptive protocol interpreter and final decision. The three PRF challenge-query caps are respectively one, one and two. The two Extract endpoints retain their established uniform 32-byte sampler and trivial external context. The entire 76-byte step and 32-byte opposite directional chain are supplied jointly; no projection is resampled independently.

The permanent functional premise is `SourceFullCorrect`, the production no-salt HKDF-SHA-512 Extract/Expand wiring contract already used by B8a. The surrounding experiment is the approved R1 game, where only zero-salt Extract on a 192-byte PQXDH root input is a programmable random oracle. HMAC outside that precise interface, root Expand, public HKDF, ordinary chain derivations and known-key operations stay real. This theorem does not derive that ROM contract from collision resistance, does not restore the rejected public-HKDF/random-table interpretation, and proves no primitive implementation property.

## Exact source run and private omitted entry

The context sampler retains the original R1 experiment's order: Server identity seed, Beacon prekey scalar, Beacon identity seed, one-time seed, ML-KEM key generation, then the complete actual Phase-1 owner. It retains the full private context and exposes it through the experiment's original public-input function. Sampling the designated PRK before the adversary is justified over the complete evaluated continuation, including all source generators, tables and final state. An explicit private latch ensures that this sample is used by at most the first execution of the designated operation. Rust generates the KEM keypair before the Phase-1 one-time key, whereas this experiment samples those two in the opposite order. Rust also generates the Beacon identity before its prekey, reversing another adjacent pair in this experiment. The separate native-source stage must prove both interchanges over the complete evaluated continuation; this per-entry theorem does not itself close that production sampler boundary.

The factored interpreter omits the selected Extract-table value. It stores the selected input privately and uses a label for a matching honest derivation. Other table values retain their actual values even when their bytes alias the selected value. Marked pending tokens omit the selected root, while the mathematical source relation reconstructs it. Native Server and Beacon state, the shared CTX cache, consumed registrations, pending-token ownership, counters, seal history, accepted snapshot and public transcript remain related exactly.

Every marked session has a literal session touch in the same private ghost history with the same 192-byte input. This provenance is preserved through the complete source coupling. It does not infer distinct sessions from distinct key bytes or claim a global one-seal bound merely because a pending token is consumed once.

The logged Server builder and actual Beacon after-root continuation use the selected root only through the joint 108-byte factor. Their existing checked factor theorems preserve complete monadic effects, actual optional sealing/opening replies, writer failures, preparation and binding gates, full returned state, and cache updates. The irrelevant opposite-role callbacks are closed pure functions and are proved unread by these source paths. The continuation does not receive the selected PRK, root or first initial chain; its supplied factor does contain the selected message key, which is removed only by the later CTX reduction.

## Refusal and event scope

Two source situations refuse the omitted-entry comparison: a prior table hit at the designated operation, and a later public query at the selected input. Cache provenance proves that every prior hit comes from an actual chronological touch. The original `EntryEvent` and original source invariant exclude the resulting wrong-first-owner or public-query event. Refusal is therefore charged with coefficient one through event implication and adds no statistical or guessing term.

Both runs continue to execute their respective complete adaptive adversaries after refusal. In particular, a designated Beacon cache hit still runs the source's actual root continuation, raw opening and cache effects. The proof couples the complete outcomes on this excluded branch; it does not silently skip source work or place recovered plaintext in an adversary's target.

The final coupling covers every original query: coins, accept, build, finish, public HMAC, shared commitment hash and Server-kernel reveal. Rejected prefixes, invalid root input, changed candidates, missing or already consumed tokens, inactive Beacon phases, opening failure, writer failure and arbitrary adaptive stopping are retained. Sequence-one and registration-binding validation remain the actual source gates. This is the approved Server-authentication experiment's event; it makes no later assigned-ID equality, KCI, unrestricted secret-reveal, postregistration secrecy, snapshot or persistence claim.

## Concrete uniform-query ledger

Let `qCoin` bound the original adversary's direct uniform requests, `Q` its accept attempts, `qHash` its public commitment-hash requests, and `qH` its public zero-salt HMAC requests whose input is exactly 192 bytes. These predicates apply on every reply path and to every public input. Let `uGen`, `uEnc`, `uDec` and `bGen`, `bEnc`, `bDec` bound the actual KEM routines' direct uniform and base-oracle calls, and let `r` bound the uniform work of each base callback. The complete context-folded entry reduction has uniform-query cap

`U = 256 + qCoin + 160 Q + 64 (qHash + qH) + uGen + Q uEnc + uDec + r (bGen + Q bEnc + bDec)`.

The source context contributes four actual 32-byte samples plus complete KEM key generation. The adaptive continuation charges each attempted Server prefix and possible Extract-table sample, reserves one complete build for each allocated pending token, and reserves the Beacon's single active finish. Token consumption and phase exhaustion are proved from the actual handlers. The argument holds after refusal and under arbitrary factor replies; it assumes neither authentication success nor a good-state event. Real and selected builder/receive callbacks retain all source work and shared-cache effects.

The five explicit primitive games then have the following uniform-query caps, including challenger sampling. The two Extract games each sample their literal 32-byte input even when the random world's final output does not use it.

| Constructed reduction | HMAC challenge calls | Real game | Random game |
| --- | --- | --- | --- |
| Root Expand PRF | 1 | `64 + U` | `64 + U` |
| Extract of the root | Separate Extract endpoint | `32 + U` | `96 + U` |
| Initializer Expand PRF | 1 | `64 + U` | `64 + U` |
| Extract of the first chain | Separate Extract endpoint | `64 + U` | `128 + U` |
| Step Expand PRF | 2 | `96 + U` | `160 + U` |

The three PRF reductions themselves use at most `U`, `U` and `32 + U` local uniform requests. The last includes the independent opposite-direction half. The step random challenger pays for both complete 64-byte replies, including unused suffixes. These are uniform-oracle and challenge-interface counts, not a claim that deterministic public HMAC/HKDF evaluations, decoding, group operations or adversary computation take no time. Those operations remain the original explicit code and primitive interfaces; a total running-time statement must retain their costs and the adversary's own running time separately.

## Module map

- `PqxdhServerAuthEntrySimulation` defines the unchanged source-shaped services and generic complete-run sampling/coupling lemmas.
- `PqxdhServerAuthEntryFlat` proves exact interpretation of the original nested experiment and its literal context sampler.
- `PqxdhServerAuthEntryEager` proves complete eager sampling with a once-only selected operation.
- `PqxdhServerAuthEntryTable` proves omitted-table reconstruction, source cache/touch provenance and concrete refusal consequences.
- `PqxdhServerAuthEntryState` relates full native state, private pending roots, marks, cache and source history.
- `PqxdhServerAuthEntryPublic`, `PqxdhServerAuthEntryAccept` and `PqxdhServerAuthEntryFinish` discharge every original query's actual source coupling.
- `PqxdhServerAuthEntryServices` instantiates the complete logged Server/Beacon factors and defines the real and uniform entry games.
- `PqxdhServerAuthEntryBound` joins all query proofs across the complete adaptive adversary and applies the five explicit B8a reductions.
- `PqxdhServerAuthEntryResourceState` and `PqxdhServerAuthEntryResourcePotential` prove exact pending-token/phase reservations, the adaptive potential and the actual source-context bill.
- `PqxdhServerAuthEntryResourceServices` and `PqxdhServerAuthEntryResourceHandlers` discharge the literal real and selected callback costs through every original query.
- `PqxdhServerAuthEntryResourceGame` supplies the complete `entryReductionBudget` without a remaining observer-cost premise.
- `PqxdhServerAuthEntryReductionResources` supplies the five primitive-game ledgers, actual 64/108-byte game-sampler costs and the combined `entry_bound_with_resources` statement.

The concrete resource consumer uses these same frozen service definitions and keeps source-interface costs separate from primitive challenger sampling. The enclosing authentication theorem must additionally consume the actual CTX compiler, its original-entry stop exclusion and query bounds, the earlier source-collision/Gap-DH reductions, and the explicit sum over entry coordinates.
