#!/usr/bin/env python3
"""Derive beaconcrypt's ChaCha20-Poly1305 multi-opening test fixture.

This is the construction source, not a production cryptographic
implementation.  It uses only Python's standard library and follows the
ChaCha20 and Poly1305 definitions in RFC 8439.  Independent implementations
then verify the resulting fixture in:

* scripts/generate_kat_vectors.py (PyCryptodome)
* scripts/generate_kat_vectors.go (golang.org/x/crypto)
* src/shared.rs (libsodium-rs)

The accompanying algebra and verification procedure are documented in
doc/multi-opening-fixture.md.
"""

from __future__ import annotations

import hashlib
import struct

POLY1305_P = (1 << 130) - 5
UINT128_MODULUS = 1 << 128
UINT32_MASK = (1 << 32) - 1
POLY1305_R_MASK = 0x0FFFFFFC0FFFFFFC0FFFFFFC0FFFFFFF


def rotate_left_32(value: int, shift: int) -> int:
    return ((value << shift) & UINT32_MASK) | (value >> (32 - shift))


def quarter_round(state: list[int], a: int, b: int, c: int, d: int) -> None:
    state[a] = (state[a] + state[b]) & UINT32_MASK
    state[d] = rotate_left_32(state[d] ^ state[a], 16)
    state[c] = (state[c] + state[d]) & UINT32_MASK
    state[b] = rotate_left_32(state[b] ^ state[c], 12)
    state[a] = (state[a] + state[b]) & UINT32_MASK
    state[d] = rotate_left_32(state[d] ^ state[a], 8)
    state[c] = (state[c] + state[d]) & UINT32_MASK
    state[b] = rotate_left_32(state[b] ^ state[c], 7)


def chacha20_block(key: bytes, counter: int, nonce: bytes) -> bytes:
    """RFC 8439 Section 2.3 ChaCha20 block function."""

    assert len(key) == 32
    assert len(nonce) == 12
    assert 0 <= counter <= UINT32_MASK
    initial = list(
        struct.unpack(
            "<16I",
            b"expand 32-byte k" + key + counter.to_bytes(4, "little") + nonce,
        )
    )
    working = initial.copy()

    for _ in range(10):
        quarter_round(working, 0, 4, 8, 12)
        quarter_round(working, 1, 5, 9, 13)
        quarter_round(working, 2, 6, 10, 14)
        quarter_round(working, 3, 7, 11, 15)
        quarter_round(working, 0, 5, 10, 15)
        quarter_round(working, 1, 6, 11, 12)
        quarter_round(working, 2, 7, 8, 13)
        quarter_round(working, 3, 4, 9, 14)

    return struct.pack(
        "<16I",
        *((working[index] + initial[index]) & UINT32_MASK for index in range(16)),
    )


def chacha20_xor(data: bytes, key: bytes, nonce: bytes) -> bytes:
    """Encrypt or decrypt the one-block fixture with counter 1."""

    assert len(data) <= 64
    keystream = chacha20_block(key, 1, nonce)
    return bytes(left ^ right for left, right in zip(data, keystream))


def poly1305_parameters(key: bytes, nonce: bytes) -> tuple[int, int]:
    """Derive and clamp Poly1305's r and obtain s from ChaCha20 block 0."""

    one_time_key = chacha20_block(key, 0, nonce)[:32]
    r = int.from_bytes(one_time_key[:16], "little") & POLY1305_R_MASK
    s = int.from_bytes(one_time_key[16:], "little")
    return r, s


def poly1305_block(block: bytes) -> int:
    """Encode a full 16-byte Poly1305 block including its high 1 bit."""

    assert len(block) == 16
    return int.from_bytes(block, "little") + UINT128_MODULUS


def aead_tag(
    key: bytes, nonce: bytes, associated_data: bytes, ciphertext: bytes
) -> bytes:
    """Compute the RFC 8439 tag for the fixture's two full data blocks."""

    assert len(associated_data) == 16
    assert len(ciphertext) == 16
    r, s = poly1305_parameters(key, nonce)
    lengths = len(associated_data).to_bytes(8, "little") + len(ciphertext).to_bytes(
        8, "little"
    )
    accumulator = (
        poly1305_block(associated_data) * pow(r, 3, POLY1305_P)
        + poly1305_block(ciphertext) * pow(r, 2, POLY1305_P)
        + poly1305_block(lengths) * r
    ) % POLY1305_P
    return ((accumulator + s) % UINT128_MODULUS).to_bytes(16, "little")


def solve_associated_data(
    key: bytes, nonce: bytes, ciphertext: bytes, desired_tag: bytes
) -> tuple[int, bytes] | None:
    """Solve the first Poly1305 block for a second valid AEAD opening."""

    r, s = poly1305_parameters(key, nonce)
    lengths = (16).to_bytes(8, "little") + len(ciphertext).to_bytes(8, "little")
    fixed_terms = (
        poly1305_block(ciphertext) * pow(r, 2, POLY1305_P) + poly1305_block(lengths) * r
    )
    inverse_r_cubed = pow(pow(r, 3, POLY1305_P), -1, POLY1305_P)
    tag_value = int.from_bytes(desired_tag, "little")

    # The final 128-bit tag discards the high bits of accumulator + s.
    # Enumerate the at most four accumulator representatives below p.
    for carry in range(4):
        target_accumulator = (
            (tag_value - s) % UINT128_MODULUS
        ) + carry * UINT128_MODULUS
        if target_accumulator >= POLY1305_P:
            continue
        associated_data_block = (
            (target_accumulator - fixed_terms) * inverse_r_cubed
        ) % POLY1305_P
        if UINT128_MODULUS <= associated_data_block < 2 * UINT128_MODULUS:
            associated_data = (associated_data_block - UINT128_MODULUS).to_bytes(
                16, "little"
            )
            if aead_tag(key, nonce, associated_data, ciphertext) == desired_tag:
                return carry, associated_data
    return None


def commitment(
    key: bytes,
    nonce: bytes,
    associated_data: bytes,
    tag: bytes,
    sequence: int,
    key_id: int,
) -> bytes:
    transcript = (
        key
        + nonce
        + associated_data
        + tag
        + sequence.to_bytes(8, "little")
        + key_id.to_bytes(8, "little")
    )
    return hashlib.blake2b(transcript, digest_size=64).digest()


def print_value(name: str, value: bytes | int) -> None:
    if isinstance(value, bytes):
        print(f"{name}={value.hex()}")
    else:
        print(f"{name}={value}")


def print_integer(name: str, value: int) -> None:
    print(f"{name}=0x{value:x}")


def main() -> None:
    key_one = bytes(range(32))
    nonce = bytes(range(12))
    associated_data_one = bytes(range(0xF0, 0x100))
    ciphertext = bytes.fromhex("00112233445566778899aabbccddeeff")
    plaintext_one = chacha20_xor(ciphertext, key_one, nonce)
    tag = aead_tag(key_one, nonce, associated_data_one, ciphertext)

    # Deterministically enumerate unrelated second keys until the Poly1305
    # equation has a solution that encodes as one full 16-byte AD block.
    attempt = 0
    while True:
        attempt += 1
        key_two = hashlib.sha256(
            b"beaconcrypt-ctx-fixture-" + attempt.to_bytes(4, "little")
        ).digest()
        solution = solve_associated_data(key_two, nonce, ciphertext, tag)
        if solution is not None:
            carry, associated_data_two = solution
            break

    plaintext_two = chacha20_xor(ciphertext, key_two, nonce)
    assert plaintext_one != plaintext_two
    assert aead_tag(key_two, nonce, associated_data_two, ciphertext) == tag
    r_two, s_two = poly1305_parameters(key_two, nonce)
    target_accumulator = (
        (int.from_bytes(tag, "little") - s_two) % UINT128_MODULUS
    ) + carry * UINT128_MODULUS
    encoded_associated_data_two = poly1305_block(associated_data_two)
    commitment_one = commitment(
        key_one, nonce, associated_data_one, tag, sequence=1, key_id=7
    )
    commitment_two = commitment(
        key_two, nonce, associated_data_two, tag, sequence=1, key_id=7
    )
    assert commitment_one != commitment_two

    # Detect accidental drift from the checked-in Rust fixture.
    assert attempt == 1
    assert carry == 0
    assert associated_data_two.hex() == "3a09eec3daf672a00f13351df1986203"
    assert plaintext_one.hex() == "89ea2a336d42c3373f1a954854c0e09c"
    assert plaintext_two.hex() == "3c6ab3eb035de373e2b5d4a81a3cd13f"
    assert tag.hex() == "8867608090128f8c1a4711d553773215"

    print("[chacha20poly1305-multi-opening-derivation]")
    print_value("attempt", attempt)
    print_value("carry", carry)
    print_integer("r2", r_two)
    print_integer("s2", s_two)
    print_integer("target_accumulator", target_accumulator)
    print_integer("encoded_ad2", encoded_associated_data_two)
    print_value("key1", key_one)
    print_value("key2", key_two)
    print_value("nonce", nonce)
    print_value("ad1", associated_data_one)
    print_value("ad2", associated_data_two)
    print_value("ciphertext", ciphertext)
    print_value("tag", tag)
    print_value("plaintext1", plaintext_one)
    print_value("plaintext2", plaintext_two)
    print_value("commitment1", commitment_one)
    print_value("commitment2", commitment_two)


if __name__ == "__main__":
    main()
