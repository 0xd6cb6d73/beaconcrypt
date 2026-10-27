<!-- SPDX-License-Identifier: 0BSD -->

# Machine-checked collision witness and computational lifting for beaconcrypt's modified CTX commitment

The binding result, random-oracle integrity/privacy results, raw-input extensions and common classical deployment composition have different assumptions and interfaces. This reference describes each result at its current boundary. Full composition with the current mandatory ML-DSA native adapter remains separate from the delivered classical deployment headlines.

## Construction

For a ChaCha20-Poly1305-IETF key `K`, nonce `N`, 281-byte beaconcrypt associated data `A`, plaintext `M`, sequence `S`, and sender key identifier `I`, let `(C, T) = AEAD.Seal(K, N, A, M)`, where `C` is the ciphertext core and `T` is the 16-byte Poly1305 tag.
Production computes the 64-byte outer value and protected payload as follows:

```text
X = K || N || A || T || LE64(S) || LE64(I)
U = BLAKE2b-512(X)
R = C || T || U
```

The transcript `X` is exactly 357 bytes: 32 bytes of key, 12 bytes of nonce, 281 bytes of associated data, 16 bytes of AEAD tag, and two eight-byte integers. Current AD includes the ordered 64-byte hashes of the Server and Beacon ML-DSA public keys after the 153-byte classical identity/label prefix.
The fixed-width builder is [`build_commitment_transcript`](../beaconcrypt-core/src/commitment.rs#L55). Core record requests retain the selected fields, and the native [`execute_commitment_hash`](../beaconcrypt/src/ratchet.rs#L491) interpreter passes the transcript to unkeyed 64-byte `generichash` and clears its copied bytes after the hash attempt.
The native [`execute_record_send`](../beaconcrypt/src/ratchet.rs#L546) and [`execute_record_receive`](../beaconcrypt/src/ratchet.rs#L579) interpreters execute the core's seal/open requests and retain the `C || T || U` layout. The production crypto backend is RustCrypto/Dalek through `beaconcrypt-crypto`; the helper named `build_commitment` in `ratchet.rs` is test-only.
The checked Lean [`CommitmentSurface`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/CommitmentSurface.lean) module proves the exact per-byte layout, proves `encode_u64_le_is_injective`, and proves `production_commitment_input_is_injective`, so equality of two extracted production transcripts implies equality of all six semantic fields `(K, N, A, T, S, I)`.

This is a modification of Chan and Rogaway's [CTX transform](https://eprint.iacr.org/2022/1260.pdf).
CTX replaces the base tag `T` with `U`; beaconcrypt retains `T` for the base AEAD open interface, adds `S` and `I` to the hash transcript, and transmits `C || T || U`.
Retaining `T` does not weaken the commitment argument because two explanations of the same protected payload necessarily use the same transmitted `T`.

## Commitment game

An explanation of a protected payload `R = C || T || U` is a tuple `(K, N, A, S, I, M)` for which both checks performed by production succeed:

```text
U == BLAKE2b-512(K || N || A || T || LE64(S) || LE64(I))
AEAD.Open(K, N, A, C || T) == M
```

A misattribution is one protected payload with two successful, distinct explanations `(K, N, A, S, I, M)` and `(K', N', A', S', I', M')`.
The distinction covers a different key, nonce, associated data, sequence, sender key identifier, or plaintext.
Keys may be revealed or chosen by the adversary; the argument does not assume that either candidate key is honest or secret.

The direct one-shot full-commitment experiment is the equal-encryption form of that event. The adversary chooses two complete well-formed tuples, the game runs BeaconCrypt's modified `sealRecord` on both, and it wins exactly when the distinct tuples produce the same `C || T || U` payload. Both keys, nonces, associated-data values, sequence numbers, sender identifiers, and plaintexts are under adversarial control. This is the equal-seal corrupted/corrupted specialization of the CTX collision event, not the paper's complete adaptive CAE oracle/history game. The separately defined raw-payload misattribution game is stronger because its shared protected payload need not be produced by either sealing call.

The protected payload `R`, rather than the 64-byte value `U` by itself, is the committing ciphertext.
In particular, `U` does not hash the ciphertext core `C`.
This is sufficient for misattribution resistance because one fixed `R` fixes `C`, `T`, and `U`; ordinary ciphertext-integrity claims for modifications that change `C` still rely on ChaCha20-Poly1305 authentication.

## Machine-checked collision witness and computational lifting

The checked declarations below distinguish the extracted implementation from the ideal-model probability games. The implementation theorems are in `BeaconcryptCore.Refinement.CommitmentSurface`; the probability bounds are in `CtxReduction.lean`.

| Claim | Checked Lean evidence |
| --- | --- |
| The actual extracted builder returns the transcript whose bytes equal ideal `ctxPreimage` | [`productionInput_spec`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/CommitmentSurface.lean#L32) and [`productionInput_abs`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/CommitmentSurface.lean#L38) |
| Full-width little-endian encoding has a left inverse and is injective | [`decode_encode_u64_le`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/CommitmentSurface.lean#L124) and [`encode_u64_le_is_injective`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/CommitmentSurface.lean#L130) |
| Equal production transcript arrays imply equal six-field inputs | [`production_commitment_input_is_injective`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/CommitmentSurface.lean#L56) |
| Two distinct accepted explanations yield a collision on the actual production inputs | [`ctx_distinct_openings_imply_hash_collision`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/CommitmentSurface.lean#L90) |
| Ideal-model misattribution and one-shot full commitment reduce to collision finding with factor one | [`ctxMisattributionAdvantage_le_blake2b_cr`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxReduction.lean#L94) and [`ctxFullCommitmentAdvantage_le_blake2b_cr`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxReduction.lean#L201) |

The Lean extracted-code theorem `ctx_distinct_openings_imply_hash_collision` quantifies over arbitrary pure 357-to-64-byte `hash` and AEAD-open functions.
It fixes the same ciphertext core `C` and outer value `U` for both accepted openings, while each opening supplies its own 16-byte tag, used in that opening's AEAD check and hash transcript; the two tags `T` and `T'` may therefore differ, and one received production payload `C || T || U` is the special case `T = T'`.
It allows the base AEAD to open that ciphertext core under unequal keys or contexts, and treats semantic differences in `K`, `N`, `A`, `S`, `I`, or `M` as a distinct explanation.
For two such accepted explanations, let:

```text
X  = K  || N  || A  || T  || LE64(S)  || LE64(I)
X' = K' || N' || A' || T' || LE64(S') || LE64(I')
```

Both successful outer checks imply `hash(X) = U = hash(X')`.
If `X = X'`, `production_commitment_input_is_injective` gives equality of `K`, `N`, `A`, `T`, `S`, and `I` with their primed counterparts, while applying the same pure AEAD-open function to the same `K`, `N`, `A`, `C`, and `T` fixes its result and therefore gives `M = M'`.
That contradicts distinctness, so Lean constructs the explicit witness `X != X'` and `hash(X) = hash(X')` for every pair of accepted distinct explanations.

Lean checks both the direct scheme-level full-commitment game and the stronger raw-payload game for the handwritten ideal PQXDH record model.
[`CtxReduction.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxReduction.lean) defines `CtxFullCommitmentAttempt` as two complete explanations and `CtxFullCommitment` as equality of their actual `sealRecord` encodings plus semantic distinctness. `ctxFullCommitment_implies_misattribution` proves that any such encryption collision is a win in the raw-payload game: correctness opens the left seal under the left explanation, equality rewrites it to the right seal, and correctness opens that under the right explanation. The existing raw game lets an adversary return one arbitrary payload and two well-formed explanations, tests both with the model's real `openRecord` parser and verifier, and maps every winning attempt to the two exact `ctxPreimage` values built with the shared parsed tag.
The resulting scheme theorem is:

```text
ctxFullCommitmentAdvantage(c, A)
  <= crAdvantage(c.blake2b, ctxFullCommitmentCollisionReduction(c, A))
```

The displayed probability inequality and the analogous raw-misattribution inequality are machine-checked and have factor one.
VCVio's `CRAdversary` does not track PPT cost, so runtime preservation remains conventional complexity reasoning. The direct equal-seal reducer runs `A`, computes the left base-AEAD tag, and constructs two transcripts without evaluating BLAKE2b; the raw-payload reducer instead adds deterministic parsing and transcript construction.
The extracted-code theorem checks the pointwise implication for the fixed-width transcript; the ideal-model proof checks both a pointwise witness and the game-level inequality.

There is no additive ChaCha20-Poly1305 term in this binding reduction, and unequal-key or unequal-context multi-openings by the base AEAD remain allowed.
This is the same black-box collision-reduction pattern as Theorem 2 of the CTX paper, extended by an injective encoding of `S` and `I` and simplified by the fact that BeaconCrypt transmits the original `T`. It establishes the direct one-shot equal-seal full-commitment property of the modified scheme subject to BLAKE2b collision resistance; it is not merely a statement that the extracted builder has the intended layout. A complete adaptive CAE formulation would additionally need indexed keys, oracle histories, reveal/corruption status, and query accounting.

Collision resistance is the production assumption and does not provide a proved numerical advantage bound for BLAKE2b.
Under the additional ideal-random-function heuristic, `Q` distinct transcript evaluations have collision probability at most `Q(Q - 1) / 2^513`, corresponding to generic classical birthday work on the order of `2^256` for the 512-bit output.
This heuristic is not a proof about BLAKE2b and must not be reported as one.

## One-key integrity under a classical random oracle

### Games and final bounds

The direct game samples one hidden 32-byte key, permits adaptive public random-oracle queries and nonce-respecting seals, and retains the base tag in every record. It rejects repeated 12-byte seal nonces before sampling. One lazy byte-string random-oracle cache is shared by honest commitments, public queries and the final verifier. Let `qH` bound public hash queries and `qE` bound seal queries.

[`CtxComputationalSecurity.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxComputationalSecurity.lean) proves the bound for `CtxAcceptedTypedFullFreshAt`, a typed full-fresh forgery game in which the adversary also names the exact plaintext that the record opens to. The ciphertext-only game in [`CtxUnclaimedAcceptance.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxUnclaimedAcceptance.lean) instead takes only nonce, context and protected record; acceptance uses the challenger's actual optional opening, with no adversarial plaintext claim. The theorem `CtxUnclaimedAcceptance.canonicalGame_le_intctxt_add_booleanIndDollar_add_guesses` gives the same conventional bound for that game. Both targets are typed records; their raw-input extensions are described below.

For `qE < 2^96`, both games satisfy:

```text
Pr[full-fresh accepted forgery]
  ≤ Adv_INT-CTXT + ofReal(Adv_IND$) + qH / 2^128 + 2^-512
```

The advantages refer to the explicitly constructed modified nonce-AEAD reductions. The specialized key-probe alternative replaces the validation IND$ term and `qH / 2^128` with the key-probe IND$ advantage and `qH / 2^256`. These are distinct primitive endpoints; secrecy of the key prefix is not treated as information-theoretic for an arbitrary modeled AEAD.

The machine-checked accounting gives the validation reduction at most `qE + 1` primitive seals and `64qH + 65qE + 1` total primitive-interface calls. The complete direct game makes at most `96 + 64(qH + qE)` uniform-byte calls. These are explicit query bills, not an asymptotic PPT-cost proof.

### Freshness, cache separation and the single prefix charge

A full-fresh accepted authentication tuple has either a fresh retained-base `(K, N, A, C, T)` projection or a context alias: an earlier base output reused under different sequence or sender values. The fixed-width serialization excludes aliases caused by out-of-range `LE64` truncation. For arbitrary designated histories, the supporting classification theorem assumes extensional per-key nonce consistency and allows exact duplicate history entries; its history is supplied rather than generated by an oracle. Its factor-one split is:

```text
Pr[nonce-consistent CTX forge]
  ≤ Pr[nonce-consistent fresh base projection]
    + Pr[accepted alias at an honest-history-fresh outer input]
```

The direct game generates its own history and enforces nonce discipline. Cache provenance and transcript injectivity exclude an honest-seal source for a full context alias, giving:

```text
Pr[accepted full-fresh context alias]
  ≤ Pr[public query whose first 32 bytes equal the hidden key] + 2^-512
```

The checked reduction separates the two branches as follows:

| Proof component | Result and exact boundary |
| --- | --- |
| `CtxRetainedTagProjection.lean` | At fixed material and complete context, accepted fresh `C || T || U` projects with factor one to fresh retained-base `C || T` acceptance. This local history fact alone is not a hidden-key AEAD security theorem; changed sequence/sender values need the alias branch. |
| `CtxPrefixIsolation.lean` | A sticky flag is equivalent to the public hidden-prefix event; erasing the flag recovers the canonical pre-verification game. The isolated handlers agree until that event, bounding their transcript distance by its probability. |
| `CtxSplitCache.lean` and `CtxIndependentTags.lean` | The canonical cache projects exactly to a public complete-input cache and a key-free suffix cache indexed by `N || A || T || LE64(S) || LE64(I)`. Adaptive public queries use only the public cache; honest tags use the suffix cache. Their view distance costs the hidden-prefix event exactly once. |
| `CtxHonestTagSampling.lean` | Nonce uniqueness and suffix provenance make every fresh honest suffix a cache miss, so one independent uniform 512-bit tag per successful seal replaces lazy suffix sampling with zero loss. Reused nonces reject before sampling. |
| `CtxNonceAeadIntCtxt.lean` | A constructed retained-base forger preserves adaptive state/history and bounds the fresh-base branch by modified nonce-AEAD INT-CTXT advantage with factor one. A fresh CTX seal makes one primitive seal call; a rejected reused nonce makes none. |
| `CtxNonceAeadIndDollar.lean` and `CtxNonceAeadIndDollarValidation.lean` | `Pr[prefix] ≤ Adv_IND$-probe + qH / 2^256`; the conventional validation reduction uses one extra encryption at an unused nonce to give `Pr[prefix] ≤ Adv_IND$ + qH / 2^128` when `qE < 2^96`. |

The final integrity composition charges the public hidden-prefix event once. The standalone prefix-isolation result is not an additional loss charged again on top of cache separation.

## Separate random-oracle privacy hop

[`CtxComputationalPrivacy.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxComputationalPrivacy.lean) gives a one-key confidentiality bound for a bounded Boolean adversary with adaptive public-ROM queries and nonce-respecting chosen-plaintext seals. The real game returns actual `C || T || U`. The ideal game preserves length and repeated-nonce leakage while independently sampling every fresh body, 16-byte base tag and 64-byte commitment, with a consistent shared public ROM and its natural collisions.

The shared-ROM-to-independent-tag hop charges the hidden-prefix event once, honest-tag sampling is exact, and the modified nonce-AEAD view reduction has exact real/direct and random/ideal experiment equalities. The structural bound is:

```text
ofReal(Adv_CTX-privacy)
  ≤ ofReal(Adv_IND$(R_view)) + Pr[prefix]
```

The specialized form adds the distinct key-probe IND$ advantage and `qH / 2^256`; the conventional form, for `qE < 2^96`, adds the distinct validation IND$ advantage and `qH / 2^128`. There is no INT-CTXT, collision-resistance, birthday, `2^-512` or honest-commitment guessing term in these privacy bounds. Fixed query accounting covers source and reduction calls but excludes challenger-private length-matched bodies and 16-byte tags because there is no total plaintext-byte budget.

This confidentiality result assumes a classical random oracle. Collision resistance alone does not justify publishing a digest that hashes the secret key as ordinary data. The result is distinct from concrete BLAKE2b/ChaCha20-Poly1305 security, QROM security, native implementation correspondence and asymptotic PPT preservation. The retired SSProve finite-game pilot is not a dependency of the maintained Lean/VCVio reductions.

## Raw-input acceptance boundary

### Extracted receive endpoint

[`RawCtxReceive.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxReceive.lean) takes adversarial raw bytes through an explicit external decoder that returns sender, sequence and protected payload or rejects. Runtime predicates check the sender, nonempty encrypted body and AD width. The wrapper invokes the extracted receive driver with a fixed modeled CTX interpreter and request-owned material and sequence.

For a structurally valid entry kernel (`ValidRefined entry.refined`), success derives well-formedness and exact inner payload decoding, verifies the commitment and returns the actual base-AEAD plaintext. Replay after success rejects without changing the poststate under the same entry premise. Failure restores the complete entry kernel without a validity premise, and wrapper totality is unconditional. This endpoint requires neither a claimed plaintext nor an adversary-supplied well-formed target. Its decoder is an external parameter, not a proof of a concrete CBOR parser.

The native record receiver rejects trailing bytes and concatenated CBOR frames before taking ratchet ownership, and the executor checks the commitment and calls AEAD using the core's open request. The complete-input check applies to record receive, Server sender lookup and both registration records. Decoders check version/kind, primitive fields, required key widths, complete consumption and the inclusive 32 MiB encoded-message limit. Registration carries raw `C || T || U`, with implicit sequence 1 and the pinned Server ID. Focused malformed-input, cross-session, replay and rollback tests check native behavior; neither those tests nor the CTX binding theorem proves the codec or crypto-library implementation.

### Adaptive raw and independent-key extensions

The adaptive multi-query raw-decryption game with one hidden key routes bytes through a supplied public decoder and returns the actual optional plaintext. `AdaptiveCtxAliasCoupling.canonical_replay_distance_bound` provides the replay/alias coupling; its interface and loss accounting are detailed in [the adaptive coupling record](https://github.com/0xd6cb6d73/beaconcrypt/blob/e9f5048b8e27144ef3648aa06b09bd063baa38d7/doc/impl/adaptive-ctx-alias-coupling.md).

The [shared-cache integrity/replay hybrids](https://github.com/0xd6cb6d73/beaconcrypt/blob/e9f5048b8e27144ef3648aa06b09bd063baa38d7/doc/impl/adaptive-shared-ctx-hybrids.md) and [shared-cache privacy result](https://github.com/0xd6cb6d73/beaconcrypt/blob/e9f5048b8e27144ef3648aa06b09bd063baa38d7/doc/impl/adaptive-shared-ctx-privacy.md) cover families of independently sampled uniform keys with one shared random-oracle cache. These are component results with supplied decoders. They do not by themselves replace independent keys with correlated protocol-derived keys or prove native decoder/ratchet execution correspondence.

### Composed classical deployment

The common deployment experiment supplies the modeled key-schedule, CTX/AEAD, freshness, target-selection and record-execution composition under its listed contracts. It includes actual optional-plaintext observation and cache/replay/rollback behavior in the applicable mode. The record lifts `PqxdhRecordLift.ctx_lift`, `record_lift` and `PqxdhRecordLiftComposition.record_auth_lift`, and the classical/later production-boundary theorems, are delivered within that profile; see the composition ledger and the computational claim map.

These are separate computational theorems, not a computational-soundness transfer of every ProVerif verdict. Their production boundary retains abstract codec, primitive and source-transcription contracts. The classical logical projection does not include complete composition of the current mandatory ML-DSA authentication guards and actual ML-key fingerprints. Current AD281/CTX357 extraction and focused ML-authentication results do not supply that final native/global bridge.

## Supplementary symbolic negative control

The ProVerif [`aead-commitment-negative-control.pvl`](../beaconcrypt-core/proofs/pro-verif/aead-commitment-negative-control.pvl) theory deliberately permits the same ciphertext and tag to open to different plaintexts under distinct keys, nonces and associated-data contexts. The shared query is unreachable in [`aead-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-commitment.pv) and reachable when only the CTX checks are removed in [`aead-no-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-no-commitment.pv).

This differential control demonstrates the added ideal-hash CTX benefit without assuming that the base AEAD already has unique openings. It is supplementary symbolic evidence, not a computational proof or a proof of BLAKE2b. The independently reproducible [multi-opening fixture](multi-opening-fixture.md) supplies a concrete base-AEAD example with two distinct valid openings and different outer commitments.

## Scope and remaining assumptions

The binding result applies to the complete protected payload and its semantic parsed fields, not to one unique transport serialization or the external meaning of a numeric sender ID in a mutable database. The adapter must supply the intended associated data, sequence and sender ID, and deployment state must preserve their association with the intended principal. The outer value `U` is not a MAC: anyone knowing an opening key and context can compute it.

| Result | Assumptions and remaining boundary |
| --- | --- |
| Extracted collision witness and ideal-model factor-one binding reduction | Exact fixed-width transcript, deterministic opening and BLAKE2b-512 collision resistance. Concrete collision bounds, native hashing/library correctness and compiled correspondence are not proved. No AEAD security advantage is added to this binding reduction. |
| One-key integrity and privacy | The stated modified nonce-AEAD games and a shared classical random oracle, with explicit prefix/query costs. Collision resistance alone does not supply these privacy/integrity conclusions. |
| Raw receive and independent-key extensions | Their kernel-validity, decoder, observation, nonce/freshness and independent-key conditions. A supplied decoder is not its native-code realization, and independent keys are not automatically ratchet outputs. |
| Common classical deployment composition | The exact joint-identity, KEM, Extract/HMAC, CTX/AEAD, codec and budget contracts in the composition ledger, including its separate classical and later-disclosure profiles. Full mandatory-ML native/source composition remains outside those headlines. |

The trusted translation boundary includes the stated Hax/Charon/Aeneas and Rust/compiler assumptions. Identifying ideal `Crypto.blake2b` with the native BLAKE2b call requires the stated primitive/interpreter contracts; source refinements do not prove native primitive implementations or the whole adapter's compiled execution. None of these results proves physical erasure, whole-protocol side-channel resistance, post-compromise recovery, a QROM theorem or the paper's complete adaptive CAE formulation. Those limits coexist with the delivered component and classical composition theorems; they do not make those delivered results pending.
