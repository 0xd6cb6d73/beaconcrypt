# Portable Rust builds

The `beaconcrypt` Rust adapter supports `no_std + alloc` with RustCrypto and Dalek primitives. `beaconcrypt-core`, `beaconcrypt-parse` and `beaconcrypt-crypto` also support `no_std`. Production dependencies do not include libsodium or a native C crypto library; pinned libsodium is used only by development compatibility tests.

## Features and runtime requirements

| Feature | Behavior |
| --- | --- |
| `std` | Enabled by default; provides operating-system entropy and hosted convenience constructors through `getrandom`. |
| `beacon` | Enables the beacon role and its required `pqxdh` support. |
| `server` | Enables the server role, allocation-backed collections, JSON state and caller-supplied persistence. |
| `cbinds`, `gobinds`, `pybinds` | Enable hosted bindings and select `std` automatically. |

Disable default features and enable the required roles when using this checkout as a Cargo dependency. Cargo builds an `rlib` for a Rust dependency. The final application supplies its allocator, panic/runtime policy and a cryptographic entropy source appropriate for its target.

```toml
beaconcrypt = { path = "../beaconcrypt/beaconcrypt", default-features = false, features = ["beacon", "server"] }
```

Vectors, strings, JSON and crypto working storage still allocate. This is `no_std + alloc`; it does not provide allocator-free operation or a fixed memory-use bound. The complete-message limit is 32 MiB, including framing, authentication tags, commitments and registration signatures. An application can impose a smaller local limit without changing the wire format. ML-DSA keys, signatures and working storage and the 50-entry receive cache also need an appropriate memory budget.

## Target builds

The `beaconcrypt` package builds only an `rlib`, including when used as a downstream dependency. The separate `beaconcrypt-ffi` package compiles the same source into hosted `staticlib` and `cdylib` artifacts. This separation lets ordinary Cargo dependencies compile without requiring a standalone native-library runtime:

```bash
rustup target add thumbv7em-none-eabihf
cargo build -p beaconcrypt --no-default-features --features beacon --target thumbv7em-none-eabihf --locked
cargo build -p beaconcrypt --no-default-features --features server --target thumbv7em-none-eabihf --locked
cargo build -p beaconcrypt --no-default-features --features beacon,server --target thumbv7em-none-eabihf --locked
```

`scripts/check-no-std.sh` also builds an independent downstream `no_std` consumer through normal Cargo dependency selection. These commands compile the actual portable dependency graph on a target without `std`. A final application must separately link and validate its target-specific allocator, startup, entropy and storage implementation. The existing WASI guest remains a hosted integration with `std` and its own memory budget.

Build hosted native ABI libraries with the native package; the output names remain `libbeaconcrypt.a` and `libbeaconcrypt.so` (or their platform equivalents):

```bash
cargo build -p beaconcrypt-ffi --release --features gobinds --locked
```

The beacon-only release workflow builds a hosted static library with `--no-default-features --features std,beacon`. The former `--features beacon` command obtained `std` implicitly through the native backend; portable beacon builds now leave it disabled. [Release measurements](impl/no-std-rustcrypto.md) record the before/after commands and artifact sizes.

## Caller-provided entropy

Entropy-taking methods accept `R: beaconcrypt::crypto::TryCryptoRng + ?Sized`, using `rand_core` 0.10. Pass a generator that is securely initialized for the target and reports entropy failures through its `TryRng` implementation. The RNG is borrowed for each operation rather than retained in a role object.

| Operation | Portable API |
| --- | --- |
| Create a beacon | `Beacon::try_new_with_rng` |
| Publish its registration request | `Beacon::get_registration_bundle_with_rng` |
| Generate a one-time key explicitly | `Beacon::new_onetime_keypair_with_rng` |
| Create a server | `Server::try_new_with_rng` |
| Accept a registration request | `Server::get_shared_secret_with_rng` |
| Generate an ML-DSA identity | `MldsaIdentity::generate_with_rng` |
| Create a persistent server | `PersistentServer::create_with_rng` or `create_with_lineage_and_rng` |
| Accept a persistent registration | `PersistentServer::get_shared_secret_with_rng` |
| Generate a snapshot lineage | `SnapshotLineage::generate_with_rng` |

Completion of registration, record encryption/decryption and snapshot restoration use existing methods without additional randomness. Hosted `new`, `try_new`, generation and registration convenience methods use the operating-system RNG and require `std`. Server identity seeds remain optional secret, uniformly generated 32-byte values; supplying both seeds does not remove the entropy needed for subsequent registrations. ML-DSA registration signatures remain deterministic under their existing domain and context.

Reported RNG failures return through the fallible construction or registration result. An operation may advance the caller's RNG before returning an error; callers retain that advanced RNG state. Panicking convenience wrappers, allocation failure and application runtime termination retain their documented behavior. Predictable test RNGs and published fixture seeds are reproducibility fixtures and must not be used for deployment. Application and VM snapshots must not duplicate live role state or RNG state.

## Rust API and protocol compatibility

The portable primitive types are exported through `beaconcrypt::crypto`. Rust getters that formerly returned `libsodium_rs` key types now return corresponding `beaconcrypt::crypto::crypto_sign`, `crypto_kx` or `crypto_kem::mlkem768` types. Callers that explicitly name those types must update their imports; encoded key bytes remain compatible. Backend secret wrappers redact `Debug` and support best-effort zeroization.

Malformed local secret-key material is checked more strictly: Ed25519 signing rejects a 64-byte keypair whose public half disagrees with its seed, and ML-KEM decapsulation rejects invalid expanded public-key coefficients or a mismatched stored public-key hash. These checks affect inconsistent imported local keys. Generated keys interoperate with the development oracle in both directions. Invalid ML-KEM ciphertexts still produce implicit-rejection shared secrets; protocol authentication decides acceptance.

Registration retains mandatory ML-DSA-65 authentication, both server pins, exact domain/context/transcript bytes and version-two CBOR. Established records retain version-one CBOR, AD281, CTX357, IETF ChaCha20-Poly1305 and the same HKDF domains. Snapshot bytes, canonical JSON, replay consumption, rejected-receive rollback, send-key consumption and durable compare-and-swap requirements are preserved. The server's portable hash tables retain fallible reservation and use identity-secret-derived SipHash keys; their iteration order does not enter canonical snapshots.

The [compatibility tests](../beaconcrypt/tests/backend_compat.rs) use libsodium only as a development oracle, including independent legacy registration and record composition in both directions. Wycheproof and Rooterberg tests exercise the production backend. Existing proof artifacts remain unchanged; this backend migration has not been re-extracted or reverified. The native runtime-test command in the [README](../README.md#building) explicitly lists the 22 deferred proof-source guards recorded in the [core-lifecycle merge](impl/no-std-core-lifecycle-deferred.json), without weakening their assertions.
