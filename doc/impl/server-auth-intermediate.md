# Intermediate global Server-authentication bound

`PqxdhServerAuthIntermediate.authentication_intermediate_with_resources` assembles the original R1 authentication experiment's existing event partition, the actual B6 Gap-DH extractor and every B8b per-entry reduction. It proves

`P[Win] ≤ AdvGapDH(extractor(scanClient(A))) + P[CollB] + Σ(j : Fin(Q+1)) (P[uniformEntryGame(A,j)] + entryScheduleLoss(A,j))`.

`authentication_intermediate_scalar_with_resources` replaces that same original collision probability with `choose(Q,2) × 64 / 2^256` under the existing `X25519ScalarSpread` contract. Both statements also return the complete `ReductionBills` record for the exact reductions in the inequality. Both retain the original experiment's programmable zero-salt 192-byte Extract oracle and its existing shared CTX/BLAKE2b-512 random-oracle idealization; neither idealization is derived from collision resistance. The Gap-DH coefficient is one. The finite sum contains exactly `Q + 1` entry coordinates: each of the `Q` possible Server accept attempts and the Beacon coordinate. It introduces no further session guess and assumes no honest selected key or successful accept.

The original `Win` is the disjunction of the three existing acceptance events: no Server partner at the Beacon's accepted root input; a partner exists but no earlier partner seal has the accepted key ID, payload and associated data; or two distinct partners exist at acceptance. Partnering means equality of the actual 192-byte root input in the original transcript. It does not mean equality of an arbitrary public key, assigned ID, local installation label or byte-derived label. The accepted snapshot and the full original source invariants remain those of `PqxdhServerAuthExperiment`.

## Checked composition

`original_event_decomposition` directly consumes `Experiment.win_le_games`, including its proved ownership cases, actual reachable-state invariant and accept-attempt accounting. `original_event_decomposition_real` converts this finite probability bound to real numbers after proving every probability and finite sum is finite. Neither theorem takes a proposed event partition as a premise.

`disclosure_le_gapDh` uses the existing constructed `extractor (scanClient ...)` and the original no-seed-reveal disclosure event. `authentication_intermediate_with_resources` substitutes each actual `entry_bound_with_resources`, retaining that entry's exact five advantages: root Expand PRF, Extract of a uniform 32-byte root, initializer Expand PRF, Extract of a uniform 32-byte first chain and full step Expand PRF. Each term is still the reduction constructed from the same original adaptive adversary and its actual R1 context. The finite sum does not replace them with an unconstructed worst-case advantage or claim that independently sampled projections represent the same output.

`collision_le_scalar_spread` consumes the existing adaptive `collB_probability` theorem. Its `Q` counts every accept attempt, including rejections, and the collision event is the original event that two distinct Server attempts derive the target Beacon's input. The scalar-spread substitution adds only `choose(Q,2) × 64 / 2^256`.

## Exact reduction resources

`ReductionBills.gapInterface` retains zero signing-oracle calls and at most `2 qH (Q+1) + 2 (Q+1) (qH+Q+1) + qH` decision-oracle calls for the same Gap-DH extractor. Its uniform budget is the original complete `bodyCoinBudget` plus `64 (qH+Q+1)` for the retained Extract table. `gap_game_uniform` includes the Gap-DH challenger's additional 32-byte Server seed and 32-byte Beacon prekey scalar and identifies the resulting complete budget with B8b's

`U = 256 + qCoin + 160 Q + 64 (qHash+qH) + uGen + Q uEnc + uDec + r (bGen + Q bEnc + bDec)`.

Here the KEM routines' direct uniform counts `uGen/uEnc/uDec` and base-query counts `bGen/bEnc/bDec` remain separate, and each base callback has uniform bound `r`. `qCoin` is the additional original adversary coin-query cap; the other original interface caps are `Q`, `qH` and `qHash`. The proofs do not derive random-work bounds from those three interface caps alone.

`ReductionBills.entries` retains the same five primitive-game ledgers for every coordinate, including the PRF challenge counts one, one and two and every challenger sample. `ReductionBills.entryGames` additionally charges the original context-first factored game's 64-byte sample and the uniform game's joint 108-byte sample. These are uniform and explicit challenge-interface counts; deterministic public primitive evaluation and adversary computation remain original code and retain their separate running-time costs. No code is replaced by a free ambient callback.

## Scope and remaining obligation

Every main game is `serverAuthGame ... false A`. The result retains the approved no-KCI scope, one target Beacon, arbitrary adaptive network bytes, separate Server accept/build operations, public HMAC and commitment-hash requests, and post-registration Server-kernel reveals. It does not add Beacon secret reveals, pending-root reveals, record-session capabilities, snapshot or persistence claims, or later assigned-ID agreement. The only functional/security-interface premises beyond ordinary resource caps are the existing `X25519ClassLaw`, `SourceFullCorrect`, and, for the explicit collision term, `X25519ScalarSpread`. The approved programmable Extract ROM and joint Ed25519/X25519 interface remain those already fixed by R1 and the existing Gap-DH game; this module adds no primitive contract.

This theorem describes the original R1 experiment's generator order. Its eager context samples the Beacon prekey scalar before the Beacon identity seed and the one-time seed before ML-KEM generation. The production constructors generate the Beacon identity before its prekey and generate ML-KEM before the later Phase-1 one-time key. Production correspondence therefore consumes the separate native proof of both interchanges over the complete evaluated continuation, retaining the full interpreted KEM program; equality of marginal samples is insufficient. The intermediate bound itself does not assert that adapter correspondence.

The visible `uniformEntryGame` probabilities are the remaining B9b CTX obligations. Final authentication still requires the actual executable CTX compiler, original-entry stopping exclusion, accepted-plaintext/seal attribution and ordinary CTX security endpoints, followed by the native experiment correspondence. This intermediate bound makes no end-to-end security claim while those terms remain unbounded.
