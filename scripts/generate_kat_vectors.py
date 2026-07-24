#!/usr/bin/env python3
"""Reproduce the fixed cryptographic vectors used by the Rust tests.

All cryptographic operations are delegated to PyCryptodome. The
ChaCha20-Poly1305 multi-opening fixture is derived by
scripts/derive_multi_opening.py, documented in doc/multi-opening-fixture.md,
and validated here through PyCryptodome under both keys.
"""

from __future__ import annotations

from Crypto.Cipher import ChaCha20_Poly1305
from Crypto.Hash import BLAKE2b, SHA256, SHA512
from Crypto.Protocol.KDF import HKDF

AEAD_KEY_LEN = 32
AEAD_NONCE_LEN = 12
AEAD_TAG_LEN = 16
KDF_STATE_LEN = 32
KDF_OUTPUT_LEN = AEAD_KEY_LEN + KDF_STATE_LEN + AEAD_NONCE_LEN

SYM_RATCHET_INFO = b"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305"
PQXDH_INFO = b"BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768"


def hkdf_sha512(ikm: bytes, info: bytes, length: int) -> bytes:
    """Derive key material with PyCryptodome's RFC 5869 HKDF-SHA512."""

    return HKDF(
        master=ikm,
        key_len=length,
        salt=b"",
        hashmod=SHA512,
        context=info,
    )


def commitment(
    key: bytes,
    nonce: bytes,
    associated_data: bytes,
    tag: bytes,
    sequence: int,
    key_id: int,
) -> bytes:
    """Beaconcrypt's BLAKE2b-512 CTX commitment transcript."""

    assert len(key) == AEAD_KEY_LEN
    assert len(nonce) == AEAD_NONCE_LEN
    assert len(tag) == AEAD_TAG_LEN
    transcript = (
        key
        + nonce
        + associated_data
        + tag
        + sequence.to_bytes(8, "little")
        + key_id.to_bytes(8, "little")
    )
    digest = BLAKE2b.new(digest_bits=512)
    digest.update(transcript)
    return digest.digest()


def chacha20poly1305_encrypt(
    key: bytes, nonce: bytes, associated_data: bytes, plaintext: bytes
) -> tuple[bytes, bytes]:
    cipher = ChaCha20_Poly1305.new(key=key, nonce=nonce)
    cipher.update(associated_data)
    return cipher.encrypt_and_digest(plaintext)


def chacha20poly1305_decrypt(
    key: bytes,
    nonce: bytes,
    associated_data: bytes,
    ciphertext: bytes,
    tag: bytes,
) -> bytes:
    cipher = ChaCha20_Poly1305.new(key=key, nonce=nonce)
    cipher.update(associated_data)
    return cipher.decrypt_and_verify(ciphertext, tag)


def print_value(name: str, value: bytes | int) -> None:
    if isinstance(value, bytes):
        print(f"{name}={value.hex()}")
    else:
        print(f"{name}={value}")


def commitment_known_answer() -> None:
    key = bytes([0x11]) * AEAD_KEY_LEN
    nonce = bytes([0x22]) * AEAD_NONCE_LEN
    associated_data = b"beaconcrypt-test-associated-data"
    tag = bytes([0x33]) * AEAD_TAG_LEN
    result = commitment(key, nonce, associated_data, tag, 0x44, 0x55)

    print("[commitment]")
    print_value("digest", result)


def ratchet_known_answer() -> None:
    state = bytes([0x24]) * KDF_STATE_LEN

    print("[ratchet]")
    for step in range(1, 3):
        output = hkdf_sha512(state, SYM_RATCHET_INFO, KDF_OUTPUT_LEN)
        key = output[:AEAD_KEY_LEN]
        state = output[AEAD_KEY_LEN : AEAD_KEY_LEN + KDF_STATE_LEN]
        nonce = output[-AEAD_NONCE_LEN:]
        print_value(f"step{step}.key", key)
        print_value(f"step{step}.state", state)
        print_value(f"step{step}.nonce", nonce)


def pqxdh_root_key_known_answer() -> None:
    ikm = (
        bytes([0xFF]) * 32
        + bytes([0x11]) * 32
        + bytes([0x22]) * 32
        + bytes([0x33]) * 32
        + bytes([0x44]) * 32
        + bytes([0x55]) * 32
    )
    result = hkdf_sha512(ikm, PQXDH_INFO, KDF_STATE_LEN)

    print("[pqxdh-root-key]")
    print_value("derived-secret", result)


def rfc8439_and_commitment_known_answer() -> None:
    """RFC 8439 Section 2.8.2 plus beaconcrypt's outer commitment."""

    key = bytes.fromhex(
        "808182838485868788898a8b8c8d8e8f" "909192939495969798999a9b9c9d9e9f"
    )
    nonce = bytes.fromhex("070000004041424344454647")
    associated_data = bytes.fromhex("50515253c0c1c2c3c4c5c6c7")
    plaintext = (
        b"Ladies and Gentlemen of the class of '99: If I could offer you only "
        b"one tip for the future, sunscreen would be it."
    )
    expected_ciphertext = bytes.fromhex(
        "d31a8d34648e60db7b86afbc53ef7ec2"
        "a4aded51296e08fea9e2b5a736ee62d6"
        "3dbea45e8ca9671282fafb69da92728b"
        "1a71de0a9e060b2905d6a5b67ecd3b36"
        "92ddbd7f2d778b8c9803aee328091b58"
        "fab324e4fad675945585808b4831d7bc"
        "3ff4def08e4b7a9de576d26586cec64b"
        "6116"
    )
    expected_tag = bytes.fromhex("1ae10b594f09e26a7e902ecbd0600691")
    ciphertext, tag = chacha20poly1305_encrypt(key, nonce, associated_data, plaintext)
    assert ciphertext == expected_ciphertext
    assert tag == expected_tag
    outer_commitment = commitment(
        key,
        nonce,
        associated_data,
        tag,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
    )

    print("[rfc8439-and-commitment]")
    print_value("ciphertext", ciphertext)
    print_value("tag", tag)
    print_value("commitment", outer_commitment)


def chacha20poly1305_multi_opening_fixture() -> None:
    """Validate two fixed, distinct openings of one ciphertext and tag."""

    # Retain the construction metadata emitted with the original fixture.
    attempt = 1
    carry = 0
    key_one = bytes(range(AEAD_KEY_LEN))
    key_two = SHA256.new(
        b"beaconcrypt-ctx-fixture-" + attempt.to_bytes(4, "little")
    ).digest()
    nonce = bytes(range(AEAD_NONCE_LEN))
    associated_data_one = bytes(range(0xF0, 0x100))
    associated_data_two = bytes.fromhex("3a09eec3daf672a00f13351df1986203")
    plaintext_one = bytes.fromhex("89ea2a336d42c3373f1a954854c0e09c")
    expected_ciphertext = bytes.fromhex("00112233445566778899aabbccddeeff")
    expected_tag = bytes.fromhex("8867608090128f8c1a4711d553773215")

    ciphertext, tag = chacha20poly1305_encrypt(
        key_one, nonce, associated_data_one, plaintext_one
    )
    assert ciphertext == expected_ciphertext
    assert tag == expected_tag
    opened_plaintext_one = chacha20poly1305_decrypt(
        key_one, nonce, associated_data_one, ciphertext, tag
    )
    assert opened_plaintext_one == plaintext_one
    plaintext_two = chacha20poly1305_decrypt(
        key_two, nonce, associated_data_two, ciphertext, tag
    )
    assert plaintext_one != plaintext_two
    assert chacha20poly1305_encrypt(
        key_two, nonce, associated_data_two, plaintext_two
    ) == (ciphertext, tag)
    commitment_one = commitment(
        key_one, nonce, associated_data_one, tag, sequence=1, key_id=7
    )
    commitment_two = commitment(
        key_two, nonce, associated_data_two, tag, sequence=1, key_id=7
    )
    assert commitment_one != commitment_two

    print("[chacha20poly1305-multi-opening]")
    print_value("attempt", attempt)
    print_value("carry", carry)
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


def main() -> None:
    commitment_known_answer()
    ratchet_known_answer()
    pqxdh_root_key_known_answer()
    rfc8439_and_commitment_known_answer()
    chacha20poly1305_multi_opening_fixture()


if __name__ == "__main__":
    main()
