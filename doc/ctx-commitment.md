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
The fixed-width builder is [`build_commitment_transcript`](../crates/protocol-core/src/commitment.rs#L55-L75), and the production wrapper checks input lengths and passes those bytes to unkeyed 64-byte `generichash` in [`build_commitment`](../src/ratchet.rs#L466-L481).
The seal and open paths place and parse `C || T || U` in [`encrypt_message_with_ratchet`](../src/ratchet.rs#L350-L372) and [`decrypt_message_with_ratchet`](../src/ratchet.rs#L410-L449).
The checked F* [`Commitment.Lemmas`](../crates/protocol-core/proofs/fstar/Beaconcrypt_protocol_core.Commitment.Lemmas.fst) module proves the exact per-byte layout, proves `encode_u64_le_is_injective`, and proves `production_commitment_input_is_injective`, so equality of two extracted production transcripts implies equality of all six semantic fields `(K, N, A, T, S, I)`.

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

Conventionally lifting this pointwise theorem to a probabilistic commitment game, a collision adversary `B` runs a commitment adversary `A` and returns the F*-proved witness from any successful misattribution.
Its running time is essentially that of `A` plus parsing and two transcript evaluations, and the usual advantage inequality is:

```text
Adv_commit_beaconcrypt(A) <= Adv_collision_BLAKE2b-512(B)
```

The displayed probability and runtime lifting is conventional cryptographic reasoning, not a mechanized probability or complexity theorem in F*.
The machine-checked result is the pointwise implication and explicit collision witness for arbitrary pure functions.
There is no additive ChaCha20-Poly1305 term in this binding reduction, and unequal-key or unequal-context multi-openings by the base AEAD remain allowed.
This is the same collision-reduction pattern as Theorem 2 of the CTX paper, extended by an injective encoding of `S` and `I` and simplified by the fact that beaconcrypt transmits the original `T`.

Collision resistance is the production assumption and does not provide a proved numerical advantage bound for BLAKE2b.
Under the additional ideal-random-function heuristic, `Q` distinct transcript evaluations have collision probability at most `Q(Q - 1) / 2^513`, corresponding to generic classical birthday work on the order of `2^256` for the 512-bit output.
This heuristic is not a proof about BLAKE2b and must not be reported as one.

## Supplementary symbolic negative control

The ProVerif [`aead-commitment-negative-control.pvl`](../crates/protocol-core/proofs/pro-verif/aead-commitment-negative-control.pvl) theory deliberately permits the same ciphertext and tag to open to different plaintexts under distinct keys, nonces, and associated-data contexts.
The shared query is unreachable in [`aead-commitment.pv`](../crates/protocol-core/proofs/pro-verif/aead-commitment.pv) and reachable when only the CTX checks are removed in [`aead-no-commitment.pv`](../crates/protocol-core/proofs/pro-verif/aead-no-commitment.pv).
This differential control supplements the F* theorem with an explicit ideal-hash counterfactual and demonstrates that the ordinary exact-opening AEAD rule is not being used as evidence for CTX's added benefit.
It is not a computational proof or a proof of BLAKE2b.

## Scope and remaining assumptions

The F* theorem and its conventional computational lifting establish full misattribution resistance for the parsed protected payload, including key commitment and binding of the nonce, long-lived associated data, sequence, sender key identifier, and accepted plaintext, conditional on BLAKE2b-512 collision resistance and exact production use of the proved encoding.
They explain why a deliberately multi-opening base-AEAD example does not produce a multi-opening beaconcrypt record unless the adversary finds a BLAKE2b collision.
The concrete fixture is documented in [multi-opening-fixture.md](multi-opening-fixture.md).

The proof does not establish BLAKE2b collision resistance, correctness of its implementation, or correspondence between the extracted helper and compiled machine code beyond the stated hax/compiler assumptions.
It does not prove that production supplies the intended fields to the helper, that libsodium hashes exactly the returned bytes, or that parsing and serialization preserve the modeled payload.
It does not make `U` a MAC: anyone who knows an opening key and context can compute it.
It also does not establish secrecy, AEAD authenticity, nonce discipline, side-channel resistance, memory erasure, or origin authentication; those properties require their separate protocol and primitive assumptions.

Collision resistance supplies the remaining primitive assumption for the binding result above.
A claim that publishing `U`, which hashes the secret key as data to an unkeyed hash, preserves all confidentiality and authenticity guarantees of the base AEAD needs additional assumptions such as the random-oracle treatment used for CTX's nAE-security analysis and the security of ChaCha20-Poly1305.
No such preservation reduction for the concrete BLAKE2b instantiation is claimed here.

The bound fields are semantic parsed values, not a commitment to one unique Cap'n Proto byte serialization or to the external meaning of a numeric sender ID in a mutable database.
The adapter must supply the intended associated data, sequence, and sender ID, and deployment state must preserve the mapping from that ID to the intended principal.
