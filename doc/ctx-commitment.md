<!-- SPDX-License-Identifier: 0BSD -->

# Machine-checked collision witness and computational lifting for beaconcrypt's modified CTX commitment

## Construction

For a ChaCha20-Poly1305-IETF key `K`, nonce `N`, 153-byte beaconcrypt associated data `A`, plaintext `M`, sequence `S`, and sender key identifier `I`, let `(C, T) = AEAD.Seal(K, N, A, M)`, where `C` is the ciphertext core and `T` is the 16-byte Poly1305 tag.
Production computes the 64-byte outer value and protected payload as follows:

```text
X = K || N || A || T || LE64(S) || LE64(I)
U = BLAKE2b-512(X)
R = C || T || U
```

The transcript `X` is exactly 229 bytes: 32 bytes of key, 12 bytes of nonce, 153 bytes of associated data, 16 bytes of AEAD tag, and two eight-byte integers.
The fixed-width builder is [`build_commitment_transcript`](../beaconcrypt-core/src/commitment.rs#L55-L75), and the production wrapper checks input lengths and passes those bytes to unkeyed 64-byte `generichash` in [`build_commitment`](../beaconcrypt/src/ratchet.rs#L466-L481).
The seal and open paths place and parse `C || T || U` in [`encrypt_message_with_ratchet`](../beaconcrypt/src/ratchet.rs#L350-L372) and [`decrypt_message_with_ratchet`](../beaconcrypt/src/ratchet.rs#L410-L449).
The checked F* [`Commitment.Lemmas`](../beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst) module proves the exact per-byte layout, proves `encode_u64_le_is_injective`, and proves `production_commitment_input_is_injective`, so equality of two extracted production transcripts implies equality of all six semantic fields `(K, N, A, T, S, I)`.

This is a modification of Chan and Rogaway's [CTX transform](https://eprint.iacr.org/2022/1260.pdf).
CTX replaces the base tag `T` with `U`; beaconcrypt retains `T` so that it can call libsodium's public AEAD open interface, adds `S` and `I` to the hash transcript, and transmits `C || T || U`.
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

The F* theorem `ctx_distinct_openings_imply_hash_collision` quantifies over arbitrary pure 229-to-64-byte `hash` and AEAD-open functions.
It fixes the same ciphertext core `C`, transmitted tag `T`, and outer value `U` for both accepted openings, allows the base AEAD to open that payload under unequal keys or contexts, and treats semantic differences in `K`, `N`, `A`, `S`, `I`, or `M` as a distinct explanation.
For two such accepted explanations, let:

```text
X  = K  || N  || A  || T || LE64(S)  || LE64(I)
X' = K' || N' || A' || T || LE64(S') || LE64(I')
```

Both successful outer checks imply `hash(X) = U = hash(X')`.
If `X = X'`, `production_commitment_input_is_injective` gives equality of `K`, `N`, `A`, `T`, `S`, and `I`, while applying the same pure AEAD-open function to the same `K`, `N`, `A`, `C`, and `T` fixes its result and therefore gives `M = M'`.
That contradicts distinctness, so F* constructs the explicit witness `X != X'` and `hash(X) = hash(X')` for every pair of accepted distinct explanations.

Lean now checks both the direct scheme-level full-commitment game and the stronger raw-payload game for the handwritten ideal PQXDH record model.
[`CtxReduction.lean`](../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxReduction.lean) defines `CtxFullCommitmentAttempt` as two complete explanations and `CtxFullCommitment` as equality of their actual `sealRecord` encodings plus semantic distinctness. `ctxFullCommitment_implies_misattribution` proves that any such encryption collision is a win in the raw-payload game: correctness opens the left seal under the left explanation, equality rewrites it to the right seal, and correctness opens that under the right explanation. The existing raw game lets an adversary return one arbitrary payload and two well-formed explanations, tests both with the model's real `openRecord` parser and verifier, and maps every winning attempt to the two exact `ctxPreimage` values built with the shared parsed tag.
The resulting scheme theorem is:

```text
ctxFullCommitmentAdvantage(c, A)
  <= crAdvantage(c.blake2b, ctxFullCommitmentCollisionReduction(c, A))
```

The displayed probability inequality and the analogous raw-misattribution inequality are machine-checked and have factor one.
VCVio's `CRAdversary` does not track PPT cost, so runtime preservation remains conventional complexity reasoning. The direct equal-seal reducer runs `A`, computes the left base-AEAD tag, and constructs two transcripts without evaluating BLAKE2b; the raw-payload reducer instead adds deterministic parsing and transcript construction.
The F* theorem separately checks the pointwise implication for the extracted fixed-width transcript, while the new Lean proof checks both a pointwise witness and the game-level inequality for the ideal record model.
There is no additive ChaCha20-Poly1305 term in this binding reduction, and unequal-key or unequal-context multi-openings by the base AEAD remain allowed.
This is the same black-box collision-reduction pattern as Theorem 2 of the CTX paper, extended by an injective encoding of `S` and `I` and simplified by the fact that BeaconCrypt transmits the original `T`. It establishes the direct one-shot equal-seal full-commitment property of the modified scheme subject to BLAKE2b collision resistance; it is not merely a statement that the extracted builder has the intended layout. A complete adaptive CAE formulation would additionally need indexed keys, oracle histories, reveal/corruption status, and query accounting.

Collision resistance is the production assumption and does not provide a proved numerical advantage bound for BLAKE2b.
Under the additional ideal-random-function heuristic, `Q` distinct transcript evaluations have collision probability at most `Q(Q - 1) / 2^513`, corresponding to generic classical birthday work on the order of `2^256` for the 512-bit output.
This heuristic is not a proof about BLAKE2b and must not be reported as one.

## Supplementary symbolic negative control

The ProVerif [`aead-commitment-negative-control.pvl`](../beaconcrypt-core/proofs/pro-verif/aead-commitment-negative-control.pvl) theory deliberately permits the same ciphertext and tag to open to different plaintexts under distinct keys, nonces, and associated-data contexts.
The shared query is unreachable in [`aead-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-commitment.pv) and reachable when only the CTX checks are removed in [`aead-no-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-no-commitment.pv).
This differential control supplements the F* theorem with an explicit ideal-hash counterfactual and demonstrates that the ordinary exact-opening AEAD rule is not being used as evidence for CTX's added benefit.
It is not a computational proof or a proof of BLAKE2b.

## Scope and remaining assumptions

The F* pointwise theorem and Lean computational reductions establish the corresponding full-commitment and misattribution-to-collision facts on their respective extracted and ideal-model surfaces, including key commitment and binding of the nonce, long-lived associated data, sequence, sender key identifier, and accepted plaintext.
Together they explain why a deliberately multi-opening base-AEAD example does not produce a multi-opening BeaconCrypt record unless the adversary finds a BLAKE2b collision. The maintained Lean refinement now equates the current generated transcript builder with ideal `ctxPreimage`, but an adapter theorem connecting the authenticated production fields and returned bytes to the actual BLAKE2b call and ideal `Crypto.blake2b` remains necessary for a composed production claim.
The concrete fixture is documented in [multi-opening-fixture.md](multi-opening-fixture.md).

The proofs do not establish BLAKE2b collision resistance, correctness of its implementation, or correspondence between the ideal model, current generated helper, Rust source, and compiled machine code beyond the stated Hax/compiler assumptions.
It does not prove that production supplies the intended fields to the helper, that libsodium hashes exactly the returned bytes, or that parsing and serialization preserve the modeled payload.
It does not make `U` a MAC: anyone who knows an opening key and context can compute it.
It also does not establish secrecy, AEAD authenticity, nonce discipline, side-channel resistance, memory erasure, or origin authentication; those properties require their separate protocol and primitive assumptions.

Collision resistance supplies the remaining primitive assumption for the binding result above.
A claim that publishing `U`, which hashes the secret key as data to an unkeyed hash, preserves all confidentiality and authenticity guarantees of the base AEAD needs additional assumptions such as the random-oracle treatment used for CTX's nAE-security analysis and the security of ChaCha20-Poly1305.
Lean now checks the first retained-tag freshness-projection step: relative to one designated honest seal under fixed material and complete context, every accepted fresh `C || T || U` opening projects with factor one to an accepted fresh retained base `C || T` opening in the same augmented view. This is not standard AEAD authenticity because no hidden-key oracle interaction is modeled. Fixing the complete context is essential because `S` and `I` are absent from the base AEAD associated data; the general changed-context case needs a separate context-alias/secret-prefix-hash argument.
Lean also checks the exhaustive general-history split for protocol-width entries and target. Every accepted forgery fresh as a complete `(K, N, A, S, I, C, T, U)` authentication tuple has either a fresh accepted base `(K, N, A, C, T)` projection or reuses an earlier base output under different `S` or `I`, and the probability of the full event is at most the sum of those two same-view event probabilities. A separate theorem proves that the alias branch uses distinct serialized outer-hash inputs, excluding aliases caused by out-of-range `LE64` truncation. Under an extensional per-key nonce-consistency condition on the designated honest history, Lean now proves that every accepted alias replay's target outer-hash input is absent from every actual honest seal input and composes this into `Pr[nonce-consistent CTX forge] ≤ Pr[nonce-consistent fresh base projection] + Pr[accepted alias at an honest-history-fresh outer input]` with factor one. Exact duplicate history entries remain allowed, and the history is asserted rather than produced by an oracle. The remaining authenticity proof must enforce hidden-key nonce-respecting interaction, reduce the base term to ChaCha20-Poly1305 authenticity, and bound adversarial queries or guesses for the fresh secret-prefixed outer-hash input.
The scheme-specific ROM layer now enforces part of that interaction directly. It samples one hidden 32-byte key, rejects repeated 12-byte seal nonces, runs the modeled base AEAD, retains `T`, and makes exact `ctxPreimage` calls through one lazy byte-string random-oracle cache shared with public adversary queries and the final verifier. Its multi-query theorem proves `Pr[accepted full-fresh context alias] ≤ Pr[full-alias exact target transcript already cached before verification] + 2^-512`; the alias gate excludes trivial cache hits from honest non-forgeries. The cache-hit term still contains honest internal queries as well as public adversary queries; the next log/nonce theorem must eliminate honest hits before the remaining secret-key-prefix event can be reduced through base-AEAD IND$ privacy. The adversary currently returns a typed well-formed record, so reverse normalization from every accepted raw payload and the fresh retained-base authenticity reduction also remain.
No complete privacy or standard authenticity preservation reduction for the concrete BLAKE2b instantiation is claimed here.

The bound fields are semantic parsed values, not a commitment to one unique Cap'n Proto byte serialization or to the external meaning of a numeric sender ID in a mutable database.
The adapter must supply the intended associated data, sequence, and sender ID, and deployment state must preserve the mapping from that ID to the intended principal.
