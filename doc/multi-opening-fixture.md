<!-- SPDX-License-Identifier: 0BSD -->

# ChaCha20-Poly1305 multi-opening fixture

## Purpose

The test `commitment_separates_real_chacha20poly1305_multi_opening` uses one
`ciphertext || tag` pair that is valid under two distinct
`(key, nonce, associated data)` contexts and decrypts to two different
plaintexts. This demonstrates the non-committing behavior that the outer CTX
commitment is intended to remove.

This is not a ChaCha20-Poly1305 forgery under one key. The construction is
allowed to choose a second key and associated-data value. It also does not
construct a BLAKE2b collision: the two outer commitments are expected to be
different.

The construction follows the ChaCha20-Poly1305 definition in
[RFC 8439](https://www.rfc-editor.org/rfc/rfc8439.html), especially Sections
2.3, 2.5, and 2.8. The motivation for the outer commitment is described by the
[CTX construction](https://eprint.iacr.org/2022/1260).

## Fixed starting values

The construction begins with deterministic, non-secret values:

| Name | Value |
| --- | --- |
| `K1` | `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f` |
| `N` | `000102030405060708090a0b` |
| `A1` | `f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff` |
| `C` | `00112233445566778899aabbccddeeff` |

The nonce is shared across different keys, which does not violate
ChaCha20-Poly1305's requirement that a nonce be unique for each use of a
particular key.

`P1` is obtained by applying the ChaCha20 counter-1 stream for `(K1, N)` to
`C`. The Poly1305 tag `T` is then computed over `A1` and `C`.

## Poly1305 equation

Let:

```text
p = 2^130 - 5
OTK = first 32 bytes of ChaCha20_Block(K, counter=0, N)
r = clamp(LE128(OTK[0..15]))
s = LE128(OTK[16..31])
```

RFC 8439 appends a high `1` bit to each Poly1305 block. For a full 16-byte
block `B`, define:

```text
m(B) = LE128(B) + 2^128
```

Both associated data and ciphertext are exactly 16 bytes, so neither needs
padding. The third block is the RFC 8439 length block:

```text
L = LE64(len(A)) || LE64(len(C))
  = LE64(16)     || LE64(16)
```

The Poly1305 accumulator for these three blocks is therefore:

```text
acc = (m(A) * r^3 + m(C) * r^2 + m(L) * r) mod p
T   = LE128((acc + s) mod 2^128)
```

This form makes the associated-data block a single unknown in a linear
equation modulo `p`.

## Constructing the second opening

Candidate second keys are generated deterministically:

```text
K2(attempt) =
    SHA256("beaconcrypt-ctx-fixture-" || LE32(attempt))
```

Attempts start at 1. For each candidate `K2`, derive its `(r2, s2)` from
ChaCha20 block 0.

Because the final tag retains only the low 128 bits of `acc + s2`, the
accumulator that produces `T` can be one of:

```text
base = (LE128(T) - s2) mod 2^128
target_acc(carry) = base + carry * 2^128
```

Only candidates below `p` are possible, so checking `carry` values `0..3`
exhausts the accumulator representatives.

For each candidate accumulator, solve for the encoded associated-data block:

```text
m(A2) =
    (target_acc
     - m(C) * r2^2
     - m(L) * r2)
    * inverse(r2^3, p)
    mod p
```

A solution encodes one full 16-byte Poly1305 block exactly when:

```text
2^128 <= m(A2) < 2^129
```

In that case:

```text
A2 = LE128^-1(m(A2) - 2^128)
```

The first candidate key (`attempt = 1`) and first accumulator representative
(`carry = 0`) satisfy this condition. Finally:

```text
P2 = C XOR ChaCha20_Stream(K2, N, counter=1)
```

The relevant intermediate integers, written in mathematical hexadecimal
rather than their little-endian byte encoding, are:

| Name | Value |
| --- | --- |
| `r2` after clamping | `0x0dfd7a580bc3b19401df45ac0f2d360c` |
| `s2` | `0xc9bc67ea96e7232f597298455a365448` |
| `target_acc(0)` | `0x4b760f693e2a23eb331c7a4b262a1340` |
| `m(A2)` | `0x1036298f11d35130fa072f6dac3ee093a` |

## Derived fixture

| Name | Value |
| --- | --- |
| `attempt` | `1` |
| `carry` | `0` |
| `K1` | `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f` |
| `K2` | `967712731b5091e4e42b5fa6241e3b02108fedc55c561d80af04c2095d3edbe7` |
| `N` | `000102030405060708090a0b` |
| `A1` | `f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff` |
| `A2` | `3a09eec3daf672a00f13351df1986203` |
| `C` | `00112233445566778899aabbccddeeff` |
| `T` | `8867608090128f8c1a4711d553773215` |
| `P1` | `89ea2a336d42c3373f1a954854c0e09c` |
| `P2` | `3c6ab3eb035de373e2b5d4a81a3cd13f` |

Both of these statements hold:

```text
ChaCha20Poly1305.Open(K1, N, A1, C || T) = P1
ChaCha20Poly1305.Open(K2, N, A2, C || T) = P2
P1 != P2
```

For the sequence and key ID used by the Rust unit test (`seq = 1`, `kid = 7`),
the outer commitment transcript is:

```text
CTX = BLAKE2b-512(
    K || N || A || T || LE64(seq) || LE64(kid)
)
```

This produces:

```text
CTX1 = 0573b9e328176e47de0251b211aa5347c72a61abf8e095bc7ac854982711f135
       25c0741341ac59f7db41163fba77aadf8592df71b25a3b02099b6b4b00a3c403

CTX2 = 322268a07252f76c4e894cab1e124db622ecf299f5050ed23768dd79b9e804ad
       22c48e36ff3b0e3e1c6984ee81d96c9d2900672298c6350d8413dbb49b5dcdd1
```

This is the property under test: the base AEAD has two valid openings, while
the complete beaconcrypt commitment separates them.

## Reproduction and independent verification

The construction source uses only Python's standard library and derives every
field rather than accepting `A2`, `T`, or either plaintext as input:

```shell
python scripts/derive_multi_opening.py
```

Two library-backed generators independently verify both openings using
different implementations:

```shell
uv run python scripts/generate_kat_vectors.py
go run scripts/generate_kat_vectors.go
```

The Rust test performs a third verification through libsodium-rs and checks
that the two BLAKE2b commitments differ:

```shell
cargo test --all-features shared::tests::commitment_separates_real_chacha20poly1305_multi_opening -- --exact
```

The expected verification chain is:

1. `derive_multi_opening.py` independently constructs `K2`, `A2`, `T`, `P1`,
   and `P2` from the fixed starting values and equations above.
2. PyCryptodome accepts `C || T` under both contexts.
3. Go's `golang.org/x/crypto/chacha20poly1305` accepts it under both contexts.
4. libsodium-rs accepts it under both contexts.
5. The two independently computed beaconcrypt commitments are unequal.
