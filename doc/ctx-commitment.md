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

In parallel, the repository-owned SSProve development supplies a finite hidden-random-oracle formulation of the lifting.
The repository-owned [`CtxGame.v`](../beaconcrypt-core/proofs/ssprove/CtxGame.v) defines a finite hidden-random-oracle game for this lifting. A deterministic adaptive adversary receives at most `q` classical oracle queries and returns one payload with two candidate explanations. The game then makes exactly the two transcript queries needed to verify the candidates, uses an arbitrary deterministic AEAD-open function that may multi-open, and exposes only the attempt, returned digests, and chronological query trace rather than the hidden function table.

SSProve proves:

```text
Pr_bounded-hidden-ROM[CTX misattribution] <= Pr_same-run[unequal-input, equal-output collision]
```

`ctx_hidden_rom_extractor_reduction` proves this for every hidden-table distribution, and `ctx_uniform_hidden_rom_extractor_reduction` specializes it to a uniformly sampled finite random function. `ctx_hidden_binding_trace_size_bound` gives the `q + 2` upper bound, and `ctx_attach_verifier_completed_run` proves that any adversary completing within its budget is followed by exactly the two verifier query-answer pairs. `ctx_hidden_misattribution_challenge_reachable` supplies a concrete non-vacuity witness using a deliberately multi-opening AEAD and a colliding constant table.

The game uses an injective product of one-bit semantic fields, so its extractor fact is proved directly in Rocq. Connecting those fields to the 229-byte production transcript still requires the reviewed representation bridge to the F* injectivity and collision-witness theorems. Instantiating the abstract collision event as `Adv_commit_beaconcrypt(A) <= Adv_collision_BLAKE2b-512(B)` also requires the production-width game, the concrete primitive premise, and runtime accounting.

The checked assumption reports contain only the reviewed MathComp Boolean-predicate foundations and an abstract real-number carrier; they contain no repository admission, unaccepted SSProve interchange dependency, or unsafe hax prelude import.
There is no additive ChaCha20-Poly1305 term in this binding reduction, and unequal-key or unequal-context multi-openings by the base AEAD remain allowed.
This is the same black-box collision-reduction pattern as Theorem 2 of the CTX paper, extended by an injective encoding of `S` and `I` and simplified by the fact that BeaconCrypt transmits the original `T`. It establishes the direct one-shot equal-seal full-commitment property of the modified scheme subject to BLAKE2b collision resistance; it is not merely a statement that the extracted builder has the intended layout. A complete adaptive CAE formulation would additionally need indexed keys, oracle histories, reveal/corruption status, and query accounting.

Collision resistance is the production assumption and does not provide a proved numerical advantage bound for BLAKE2b.
Under the additional ideal-random-function heuristic, `Q` distinct transcript evaluations have collision probability at most `Q(Q - 1) / 2^513`, corresponding to generic classical birthday work on the order of `2^256` for the 512-bit output.
This heuristic is not a proof about BLAKE2b and must not be reported as one.

## Separate random-oracle privacy hop

[`CtxPrivacy.v`](../beaconcrypt-core/proofs/ssprove/CtxPrivacy.v) addresses the fact that the published digest hashes the secret key as ordinary data. It samples a jointly uniform hidden key, finite random-oracle table, and fresh digest; programs the table at the key-derived secret transcript; and couples that representation to an unprogrammed ideal table that publishes the same fresh digest. A key-preserving table-entry swap gives the uniform finite representation, and `ctx_hidden_uniform_key_true_real_privacy_bound` proves that the absolute true-real versus fresh-ideal decision-probability gap is at most the probability that the ideal trace queried the hidden key-containing transcript.

This is not a consequence of collision resistance and is intentionally separate from the binding result. It is conditional on an ideal AEAD supplying a hidden uniform record key, and a production theorem still needs the numerical probability of querying the production-width secret input plus composition with the base AEAD privacy game. The current classical one-bit model establishes the game hop and bad-event shape but neither a useful concrete bound nor a QROM result.

## Supplementary symbolic negative control

The ProVerif [`aead-commitment-negative-control.pvl`](../beaconcrypt-core/proofs/pro-verif/aead-commitment-negative-control.pvl) theory deliberately permits the same ciphertext and tag to open to different plaintexts under distinct keys, nonces, and associated-data contexts.
The shared query is unreachable in [`aead-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-commitment.pv) and reachable when only the CTX checks are removed in [`aead-no-commitment.pv`](../beaconcrypt-core/proofs/pro-verif/aead-no-commitment.pv).
This differential control supplements the F* theorem with an explicit ideal-hash counterfactual and demonstrates that the ordinary exact-opening AEAD rule is not being used as evidence for CTX's added benefit.
It is not a computational proof or a proof of BLAKE2b.

## Scope and remaining assumptions

The F* pointwise theorem, Lean computational reductions, and SSProve bounded hidden-ROM extractor establish complementary full-commitment and misattribution-to-collision facts on their respective extracted, ideal-model, and finite-game surfaces, including key commitment and binding of the nonce, long-lived associated data, sequence, sender key identifier, and accepted plaintext.
They explain why a deliberately multi-opening base-AEAD example does not produce a multi-opening beaconcrypt record unless the adversary finds a BLAKE2b collision.
The maintained Lean refinement now equates the current generated transcript builder with ideal `ctxPreimage`, but completing the production reduction remains conditional on an adapter and production-width representation bridge connecting authenticated production fields and returned bytes to the actual BLAKE2b call and ideal `Crypto.blake2b`, the concrete collision game and numerical bound, BLAKE2b-512 collision resistance, and exact production use of the proved encoding.
The concrete fixture is documented in [multi-opening-fixture.md](multi-opening-fixture.md).

The proofs do not establish BLAKE2b collision resistance, correctness of its implementation, or correspondence between the ideal model, current generated helper, Rust source, and compiled machine code beyond the stated Hax/compiler assumptions.
It does not prove that production supplies the intended fields to the helper, that libsodium hashes exactly the returned bytes, or that parsing and serialization preserve the modeled payload.
It does not make `U` a MAC: anyone who knows an opening key and context can compute it.
The separate programming hop identifies the precise secret-query event on which CTX can change a deterministic classical observer's view, but it does not by itself establish record secrecy, AEAD authenticity, nonce discipline, side-channel resistance, memory erasure, or origin authentication; those properties require their separate protocol and primitive assumptions.

Collision resistance supplies the remaining primitive assumption for the binding result above.
A claim that publishing `U`, which hashes the secret key as data to an unkeyed hash, preserves all confidentiality and authenticity guarantees of the base AEAD needs the production-width random-oracle and secret-query bounds, the appropriate integrity hop, and the security of ChaCha20-Poly1305.
Lean now checks the first retained-tag freshness-projection step: relative to one designated honest seal under fixed material and complete context, every accepted fresh `C || T || U` opening projects with factor one to an accepted fresh retained base `C || T` opening in the same augmented view. This is not standard AEAD authenticity because no hidden-key oracle interaction is modeled. Fixing the complete context is essential because `S` and `I` are absent from the base AEAD associated data; the general changed-context case needs a separate context-alias/secret-prefix-hash argument.
Lean also checks the exhaustive general-history split for protocol-width entries and target. Every accepted forgery fresh as a complete `(K, N, A, S, I, C, T, U)` authentication tuple has either a fresh accepted base `(K, N, A, C, T)` projection or reuses an earlier base output under different `S` or `I`, and the probability of the full event is at most the sum of those two same-view event probabilities. A separate theorem proves that the alias branch uses distinct serialized outer-hash inputs, excluding aliases caused by out-of-range `LE64` truncation. Under an extensional per-key nonce-consistency condition on the designated honest history, Lean now proves that every accepted alias replay's target outer-hash input is absent from every actual honest seal input and composes this into `Pr[nonce-consistent CTX forge] ≤ Pr[nonce-consistent fresh base projection] + Pr[accepted alias at an honest-history-fresh outer input]` with factor one. Exact duplicate history entries remain allowed, and the history is asserted rather than produced by an oracle. The later scheme-specific direct game enforces hidden-key nonce-respecting interaction and bounds both branches; the bridge from this arbitrary-history classification and the concrete ChaCha20-Poly1305 assumptions remain separate.
The scheme-specific ROM layer now enforces part of that interaction directly. It samples one hidden 32-byte key, rejects repeated 12-byte seal nonces, runs the modeled base AEAD, retains `T`, and makes exact `ctxPreimage` calls through one lazy byte-string random-oracle cache shared with public adversary queries and the final verifier. Its explicit handler state records successful seals and public inputs and preserves the invariant that every cached transcript came from one of those two sources. Nonce uniqueness and exact `ctxPreimage` injectivity exclude the honest source for a full context alias, yielding `Pr[accepted full-fresh context alias] ≤ Pr[public ROM query whose first 32 bytes equal the hidden key] + 2^-512`; the alias gate excludes trivial cache hits from honest non-forgeries. The secret-prefix probability is now bounded by a modified nonce-AEAD key-probe IND$ advantage plus `qH / 2^256`, rather than treated as information-theoretically small for an arbitrary modeled AEAD. The adversary currently returns a typed well-formed record, so reverse normalization from every accepted raw payload and the composition bridge from the earlier arbitrary-history classification into this direct game remain.

The next checked hop preserves that exact generated experiment while isolating public secret-prefix queries. A sticky flag is proved equivalent to the recorded event that some public input starts with the hidden key, and erasing the flag recovers the canonical pre-verification game exactly. A second handler independently resamples only after such a public prefix query fires; the handlers agree until bad, so their complete pre-verification transcript distributions have total-variation distance at most the existing secret-prefix-query probability. The isolated transcript retains the target, successful seals, used nonces, public inputs, and ROM cache for later verification. This standalone prefix-isolation theorem remains available, while the later split-cache game performs the operational key-free separation without charging the event again.

Lean now also proves the local honest-seal sampling premise. Before any public key-prefix query, an unused nonce makes the next honest outer input fresh from the complete shared cache: provenance excludes every public origin, and nonce rejection plus injective protocol-width serialization excludes every earlier seal origin. The corresponding lazy-ROM seal transition is exactly direct uniform 512-bit sampling followed by cache installation. The direct local transition still constructs the key-prefixed address, but `CtxSplitCache.lean` proves an exact canonical-cache projection into a non-prefix complete-input cache and a key-free suffix cache indexed by `N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(sid)`. `CtxIndependentTags.lean` lifts that projection through the full adaptive handler, routes every adversary ROM query only through the public cache and every honest tag only through the suffix cache, and proves `Δ(split canonical, key-free independent tags) ≤ Pr[public hidden-key-prefix query]` with exactly one bad-event charge. `CtxHonestTagSampling.lean` then maintains marked-nonce, pairwise-unique-nonce, and suffix-provenance invariants, proves that an unused nonce makes the next key-free suffix a cache miss, and replaces the full lazy-suffix execution exactly by one explicit independent uniform 512-bit draw per successful seal. Reused nonces reject before sampling, so the hop has zero loss. `CtxNonceAeadIntCtxt.lean` constructs the retained-base primitive forger, proves exact adaptive state/history projection, and bounds every fresh retained-base acceptance by modified nonce-AEAD INT-CTXT advantage with factor one; each fresh CTX seal makes exactly one primitive seal call and reused nonces make none. `CtxNonceAeadIndDollar.lean` identifies the canonical secret-prefix event exactly with a bounded key-probe experiment and proves `Pr[prefix] ≤ Adv_IND$-probe + qH / 2^256`, while preserving `qE` primitive seal calls and proving a source total bound of `qH + qE`. The remaining authenticity work is the final one-charge direct-game composition and byte-level uniform/PPT accounting.
No complete privacy or standard authenticity preservation reduction for the concrete BLAKE2b instantiation is claimed here.

The bound fields are semantic parsed values, not a commitment to one unique Cap'n Proto byte serialization or to the external meaning of a numeric sender ID in a mutable database.
The adapter must supply the intended associated data, sequence, and sender ID, and deployment state must preserve the mapping from that ID to the intended principal.
