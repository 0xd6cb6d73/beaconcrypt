# Rooterberg tests

Beaconcrypt runs the upstream
[Rooterberg](https://github.com/bleichenbacher-daniel/Rooterberg) vectors
against the `libsodium-rs` APIs used by the protocol. Rooterberg is included as
a pinned Git submodule so test results are reproducible and vector updates are
explicit.

Rooterberg describes itself as experimental: its vectors extend Wycheproof,
and its format may change. The harness therefore validates the format version,
test type, algorithm metadata and declared test count before running cases.

## Coverage

| Protocol primitive | Rooterberg vector | What is checked |
| --- | --- | --- |
| X25519 | `xdh/x25519.json` | Valid shared secrets, twists, non-canonical inputs, arithmetic edge cases and rejection of low-order public keys |
| Ed25519 | `eddsa/ed25519.json`, `eddsa/ed25519_sign.json` | Deterministic signing KATs, valid signatures and rejection of malformed, non-canonical and forged signatures |
| ChaCha20-Poly1305-IETF | `aead/chacha20_poly1305.json` | Encryption KATs, decryption, AAD authentication and rejection of invalid tags |
| HKDF-SHA-512 | `kdf/hkdf_sha512.json` | Extract-and-expand KATs across empty, boundary and pseudorandom inputs |
| BLAKE2b-512 | `message_digest/blake2b.json` | Unkeyed digest KATs across boundary and pseudorandom message lengths |

Rooterberg uses a boolean `valid` result rather than Wycheproof's
`valid`/`invalid`/`acceptable` result model. The harness follows Rooterberg's
strict result for every vector. Rooterberg does not currently publish ML-KEM
vectors, so ML-KEM-768 remains covered by Wycheproof and the protocol tests.

Rooterberg does not provide a license at the pinned revision. Its vector files
therefore remain in the external submodule and are excluded from Beaconcrypt's
published crate archives. Consequently, this external-vector test target can
only be run from a repository checkout with initialized submodules.

## Running the tests

Initialize the submodules after cloning:

```sh
git submodule update --init --recursive
cargo test --test rooterberg
```

The normal `cargo test` command also runs the suite when the `pqxdh` feature is
enabled.

## Updating vectors

Update the pinned revision deliberately, then run both external-vector and
protocol suites:

```sh
git -C rooterberg fetch origin
git -C rooterberg checkout <reviewed-revision>
cargo test --test rooterberg
cargo test --test wycheproof
cargo test
```

Review upstream format, algorithm metadata, result semantics and licensing
changes before accepting an update.
