<!-- SPDX-License-Identifier: 0BSD -->

# ChaCha20-Poly1305 multi-opening fixture

## Purpose

The test `commitment_separates_real_chacha20poly1305_multi_opening` uses one `ciphertext || tag` pair that is valid under two distinct `(key, nonce, associated data)` contexts and decrypts to two different plaintexts. This demonstrates the non-committing behavior that the outer CTX commitment is intended to remove.

This is not a ChaCha20-Poly1305 forgery under one key. The construction is allowed to choose a second key and associated-data value. It also does not construct a BLAKE2b collision: the two outer commitments are expected to be different.

The construction follows the ChaCha20-Poly1305 definition in [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439.html), especially Sections 2.3, 2.5, and 2.8. The motivation for the outer commitment is described by the [CTX construction](https://eprint.iacr.org/2022/1260).

The current fixture uses synthetic 151-byte associated-data values, matching the protocol's AD width: an 87-byte context followed by a 64-byte session transcript hash. These synthetic values do not contain the protocol's fixed context prefix. They provide a base-AEAD negative control; separate runtime tests check authentication under valid session AD for a fixed key and nonce.

## Fixed starting values

The construction begins with deterministic, non-secret values:

| Name | Value |
| --- | --- |
| `K1` | `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f` |
| `N` | `000102030405060708090a0b` |
| `A1` | The 151-byte sequence `00 01 ... 96` |
| `C` | `00112233445566778899aabbccddeeff` |

The nonce is shared across different keys, which does not violate ChaCha20-Poly1305's requirement that a nonce be unique for each use of a particular key.

`P1` is obtained by applying the ChaCha20 counter-1 stream for `(K1, N)` to `C`. The Poly1305 tag `T` is then computed over `A1` and `C`.

## Poly1305 equation

Let:

```text
p = 2^130 - 5
OTK = first 32 bytes of ChaCha20_Block(K, counter=0, N)
r = clamp(LE128(OTK[0..15]))
s = LE128(OTK[16..31])
```

RFC 8439 appends a high `1` bit to each Poly1305 block. For a full 16-byte block `B`, define:

```text
m(B) = LE128(B) + 2^128
```

The 151-byte associated data is padded with nine zero bytes and encoded as ten Poly1305 blocks. The 16-byte ciphertext contributes one block, followed by the RFC 8439 length block:

```text
L = LE64(len(A)) || LE64(len(C))
  = LE64(151)    || LE64(16)
```

Call these twelve blocks `B0 ... B11`, where `B0 ... B9` encode the padded associated data, `B10` is the ciphertext, and `B11` is `L`. The accumulator is:

```text
acc = sum(m(Bi) * r^(12-i), i=0..11) mod p
T   = LE128((acc + s) mod 2^128)
```

The construction keeps `B1 ... B11` fixed and solves `B0`, leaving 135 of the 151 associated-data bytes unchanged.

## Constructing the second opening

Candidate second keys are generated deterministically:

```text
K2(attempt) =
    SHA256("beaconcrypt-ctx-fixture-" || LE32(attempt))
```

Attempts start at 1. For each candidate `K2`, derive its `(r2, s2)` from ChaCha20 block 0.

Because the final tag retains only the low 128 bits of `acc + s2`, the accumulator that produces `T` can be one of:

```text
base = (LE128(T) - s2) mod 2^128
target_acc(carry) = base + carry * 2^128
```

Only candidates below `p` are possible, so checking `carry` values `0..3` exhausts the accumulator representatives.

For each candidate accumulator, let `F` be the fixed contribution from blocks `B1 ... B11` and solve for the first associated-data block:

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

The second candidate key (`attempt = 2`) and first accumulator representative (`carry = 0`) satisfy this condition. Finally:

```text
P2 = C XOR ChaCha20_Stream(K2, N, counter=1)
```

The relevant intermediate integers, written in mathematical hexadecimal rather than their little-endian byte encoding, are:

| Name | Value |
| --- | --- |
| `r2` after clamping | `0x42ba4880a4fe68c0813510c0fc9f6fb` |
| `s2` | `0x956a74166391f482a0ba4e2114a45eb8` |
| `target_acc(0)` | `0x81209cb76740698e78f56645b628f9ce` |
| `m(B0)` | `0x1461e0180a2bef6f087d325080bd10f01` |

## Derived fixture

| Name | Value |
| --- | --- |
| `attempt` | `2` |
| `carry` | `0` |
| `K1` | `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f` |
| `K2` | `559586cbd11fe2d5b02eee85d19355dc28cdf19dd3a20530c9f30dbbad046e4b` |
| `N` | `000102030405060708090a0b` |
| `A1` | The 151-byte sequence `00 01 ... 96` |
| `A2` | `010fd10b0825d387f0f6bea280011e46 || 10 11 ... 96` (151 bytes) |
| `C` | `00112233445566778899aabbccddeeff` |
| `T` | `8658cdca66b4af19115ed2cacd108b16` |
| `P1` | `89ea2a336d42c3373f1a954854c0e09c` |
| `P2` | `e67265bb4291d1ec9582c8eabcdac109` |

Both of these statements hold:

```text
ChaCha20Poly1305.Open(K1, N, A1, C || T) = P1
ChaCha20Poly1305.Open(K2, N, A2, C || T) = P2
P1 != P2
```

For the sequence and key ID used by the Rust unit test (`seq = 1`, `kid = 7`), the outer commitment transcript has 227 bytes and is:

```text
CTX = BLAKE2b-512(
    K || N || A || T || LE64(seq) || LE64(kid)
)
```

This produces:

```text
CTX1 = 335d85c266d397fd4de866d696bae4f368549735d235361d4ba6ada7b7bae8b4b
       df608d9886de6742a727be65aaf8ff57e63243ed8ace2ae109cbeccb09f8384

CTX2 = 866da120fb65ba24573e9a202377109a8dc9a992aa27d61191676426d018d695d
       5cbd13246e54b2b5a0cd6544ddf13a133d39f5c068d64a39490071d3b1dca31
```

This is the property under test: the base AEAD has two valid openings, while the complete beaconcrypt commitment separates them.

## Reproduction and independent verification

The construction source uses only Python's standard library and derives every field rather than accepting `A2`, `T`, or either plaintext as input:

```shell
python scripts/derive_multi_opening.py
```

Two library-backed generators independently verify both openings using different implementations:

```shell
uv run python scripts/generate_kat_vectors.py
go run scripts/generate_kat_vectors.go
```

The Rust test performs a third verification through libsodium-rs and checks that the two BLAKE2b commitments differ:

```shell
cargo test -p beaconcrypt --all-features shared::tests::commitment_separates_real_chacha20poly1305_multi_opening -- --exact
```

The expected verification chain is:

1. `derive_multi_opening.py` independently constructs `K2`, `A2`, `T`, `P1`, and `P2` from the fixed starting values and equations above.
2. PyCryptodome accepts `C || T` under both contexts.
3. Go's `golang.org/x/crypto/chacha20poly1305` accepts it under both contexts.
4. libsodium-rs accepts it under both contexts.
5. The two independently computed beaconcrypt commitments are unequal.
