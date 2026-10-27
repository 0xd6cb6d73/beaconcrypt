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

The fixture was re-derived for 281-byte AD after adding both ML-DSA public-key hashes; the reviewed changes are independently validated by the generators below.

## Fixed starting values

The construction begins with deterministic, non-secret values:

| Name | Value |
| --- | --- |
| `K1` | `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f` |
| `N` | `000102030405060708090a0b` |
| `A1` | The 281-byte sequence `00 01 ... ff 00 01 ... 18` |
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

The 281-byte associated data is padded with seven zero bytes and encoded as eighteen
Poly1305 blocks. The 16-byte ciphertext contributes one block, followed by the
RFC 8439 length block:

```text
L = LE64(len(A)) || LE64(len(C))
  = LE64(281)    || LE64(16)
```

Call these twenty blocks `B0 ... B19`, where `B0 ... B17` encode the padded associated data, `B18` is the ciphertext, and `B19` is `L`. The accumulator is:

```text
acc = sum(m(Bi) * r^(20-i), i=0..19) mod p
T   = LE128((acc + s) mod 2^128)
```

The construction keeps `B1 ... B19` fixed and solves `B0`, leaving 265 of the 281 associated-data bytes unchanged.

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
`B1 ... B19` and solve for the first associated-data block:

```text
m(B0) =
    (target_acc - F)
    * inverse(r2^20, p)
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

The third candidate key (`attempt = 3`) and second accumulator representative (`carry = 1`) satisfy this condition. Finally:

```text
P2 = C XOR ChaCha20_Stream(K2, N, counter=1)
```

The relevant intermediate integers, written in mathematical hexadecimal
rather than their little-endian byte encoding, are:

| Name | Value |
| --- | --- |
| `r2` after clamping | `0xc7a2ee80751dc200bae53940fdfea15` |
| `s2` | `0x122a8dcf2e47fbec059471bf67f74f6c` |
| `target_acc(1)` | `0x13bc31c59a5e1c31ff669064f047549cd` |
| `m(B0)` | `0x160d162abef2bb815d7d90036fa0babd0` |

## Derived fixture

| Name | Value |
| --- | --- |
| `attempt` | `3` |
| `carry` | `1` |
| `K1` | `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f` |
| `K2` | `9ad90ef720e8fceffcc710361c3c760dbe50bf28bc0e21c67404e2c44399b3ef` |
| `N` | `000102030405060708090a0b` |
| `A1` | The 281-byte sequence `00 01 ... ff 00 01 ... 18` |
| `A2` | `d0ab0bfa3600d9d715b82befab62d160 || 10 11 ... ff 00 01 ... 18` (281 bytes) |
| `C` | `00112233445566778899aabbccddeeff` |
| `T` | `39996c6c0e78fdfb0bbf29d428aaed4d` |
| `P1` | `89ea2a336d42c3373f1a954854c0e09c` |
| `P2` | `d4de696c5b25e8438e777ca060a610b3` |

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
CTX1 = 22240e4b6a5dff2b3ffbb4a2ebb6119ce9af9607a6f36e8c15ec5a63c4c3f8d1
       115dff685176f902f0fdf0c789077981040634d35a69ff311efb56209a10a7e5

CTX2 = 1cf9be23057b32477e24a24931e86b136ecda0fcdcb0bf117247c1c0c72ccae2
       efb7500568150c94f151c138fa889d8c78a4573189fb5f3204c82ea1792c2dcf
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
