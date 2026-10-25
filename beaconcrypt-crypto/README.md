# beaconcrypt-crypto

The `no_std + alloc` primitive adapter for beaconcrypt uses RustCrypto and Dalek implementations. Its modules preserve the protocol's existing byte encodings and fixed algorithm suite: Ed25519, X25519, ML-KEM-768, HKDF-SHA-512, configured-length BLAKE2b, and IETF ChaCha20-Poly1305. The development-only libsodium oracle is exercised by the adapter integration tests in `beaconcrypt/tests/backend_compat.rs`.

Disable default features to build without operating-system entropy support. Every key-generation operation and ML-KEM encapsulation has a fallible `*_with_rng` entry point accepting `rand_core::TryCryptoRng`. The default `std` feature enables the `getrandom`-backed `OsRng` convenience API; the primitive crate itself remains `#![no_std]` in both configurations. No global initialization is required.

Encoded public-key wrappers check their width. Cryptographic operations perform the relevant point, subgroup, coefficient and authentication checks. Ed25519-to-X25519 conversion rejects small-order and non-prime-subgroup points; X25519 rejects all-zero shared results; ML-KEM decapsulation retains implicit rejection. Secret wrappers wipe on drop and redact debug output. The enabled RustCrypto zeroize features also clear hash and stream-cipher state on drop; these best-effort operations do not establish physical erasure of every compiler-generated copy.

The API intentionally implements only the primitive operations required by beaconcrypt and its vector/compatibility tests. It is not a general libsodium replacement. In particular, signing an imported Ed25519 secret key whose embedded public half does not match its seed returns an error.
