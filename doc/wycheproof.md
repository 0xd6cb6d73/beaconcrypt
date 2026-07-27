# Wycheproof tests

Beaconcrypt runs the upstream [C2SP Wycheproof](https://github.com/C2SP/wycheproof)
vectors against the `libsodium-rs` APIs used by the protocol. Wycheproof is
included as a pinned Git submodule so test results are reproducible and vector
updates are explicit.

## Coverage

| Protocol primitive | Wycheproof vector | What is checked |
| --- | --- | --- |
| X25519 | `x25519_test.json` | Valid shared secrets, edge cases, twists, non-canonical and low-order public keys |
| Ed25519 | `ed25519_test.json` | Valid signatures and rejection of malformed, non-canonical and forged signatures |
| ChaCha20-Poly1305-IETF | `chacha20_poly1305_test.json` | Encryption KATs, decryption, AAD authentication, invalid tags and invalid nonce sizes |
| HKDF-SHA-512 | `hkdf_sha512_test.json` | Extract-and-expand KATs and rejection of oversized output |
| ML-KEM-768 | `mlkem_768_test.json`, `mlkem_768_encaps_test.json` | Deterministic key generation, encapsulation, decapsulation and malformed key/ciphertext rejection |

Wycheproof labels an X25519 case `acceptable` when an implementation may either
produce the specified secret or reject the input. The test harness accepts only
those two outcomes. A successful operation that produces any other secret
fails the test.

BLAKE2b is used by the commitment construction, but Wycheproof does not
currently publish BLAKE2b vectors. It remains covered by the independent
known-answer, context-binding and multi-opening tests in `src/shared.rs`.
The protocol-specific use of all primitives is additionally covered by the
registration, tampering, ratchet and end-to-end tests.

## Running the tests

Initialize the submodule after cloning:

```sh
git submodule update --init --recursive
cargo test --test wycheproof
```

The normal `cargo test` command also runs the suite when the `pqxdh` feature is
enabled.

## Updating vectors

Update the pinned revision deliberately, then run the vector and protocol
suites:

```sh
git -C wycheproof fetch origin
git -C wycheproof checkout <reviewed-revision>
cargo test --test wycheproof
cargo test
```

Review upstream schema and result-semantics changes before accepting an update.
The harness validates the algorithm name, schema name and declared test count
so an incompatible vector change fails visibly.
