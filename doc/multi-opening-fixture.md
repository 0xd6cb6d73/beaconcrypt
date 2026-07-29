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
| `A1` | The 153-byte sequence `00 01 ... 98` |
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

The 153-byte associated data is padded with seven zero bytes and encoded as ten
Poly1305 blocks. The 16-byte ciphertext contributes one block, followed by the
RFC 8439 length block:

```text
L = LE64(len(A)) || LE64(len(C))
  = LE64(153)    || LE64(16)
```

Call these twelve blocks `B0 ... B11`, where `B0 ... B9` encode the padded
associated data, `B10` is the ciphertext, and `B11` is `L`. The accumulator is:

```text
acc = sum(m(Bi) * r^(12-i), i=0..11) mod p
T   = LE128((acc + s) mod 2^128)
```

The construction keeps `B1 ... B11` fixed and solves `B0`, leaving 137 of the
153 associated-data bytes unchanged.

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

For each candidate accumulator, let `F` be the fixed contribution from blocks
`B1 ... B11` and solve for the first associated-data block:

```text
m(B0) =
    (target_acc - F)
    * inverse(r2^12, p)
    mod p
```

A solution encodes one full 16-byte Poly1305 block exactly when:

```text
2^128 <= m(B0) < 2^129
```

In that case, the first 16 bytes of `A2` are:

```text
A2[0..16] = LE128^-1(m(B0) - 2^128)
```

The first candidate key (`attempt = 1`) and third accumulator representative
(`carry = 2`) satisfy this condition. Finally:

```text
P2 = C XOR ChaCha20_Stream(K2, N, counter=1)
```

The relevant intermediate integers, written in mathematical hexadecimal
rather than their little-endian byte encoding, are:

| Name | Value |
| --- | --- |
| `r2` after clamping | `0x0dfd7a580bc3b19401df45ac0f2d360c` |
| `s2` | `0xc9bc67ea96e7232f597298455a365448` |
| `target_acc(2)` | `0x24a4b9e9cc92bad92bd6360b1d13ac85a` |
| `m(B0)` | `0x1247bdf3560ca14b16e6e6f2fa48c2ed6` |

## Derived fixture

| Name | Value |
| --- | --- |
| `attempt` | `1` |
| `carry` | `2` |
| `K1` | `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f` |
| `K2` | `967712731b5091e4e42b5fa6241e3b02108fedc55c561d80af04c2095d3edbe7` |
| `N` | `000102030405060708090a0b` |
| `A1` | The 153-byte sequence `00 01 ... 98` |
| `A2` | `d62e8ca42f6f6e6eb114ca6035df7b24 || 10 11 ... 98` (153 bytes) |
| `C` | `00112233445566778899aabbccddeeff` |
| `T` | `a21c712bf7f8d516c2d0126087060814` |
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
CTX1 = 9cda090561a1140c1e7fdee457c9057be213b87a65e895078564be7fa13360df
       fb48bab92db64d3800fd90ba2fc4d8c174add55cbbf0b0bff98eb74b32c1e06e

CTX2 = f092a14b1da49bad4c64f3bacc67480d7dd367f5ba90fa3f79492aea29cd7707
       49b0aefdc03fa3736dd11ee3c79038a4a4d10a64959042dd97007690a7506bb2
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
