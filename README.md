<!-- SPDX-License-Identifier: 0BSD -->

## **!! I am not a cryptographer and this has received no review. Assume this is irreparably broken !!**

# Overview
Generic C2 PQ-safe cryptographic transport protocol intended to protect against powerful wire attackers, with a rust reference implementation. This repo contains two things:
- a protocol specification, with an associated threat model
- a reference implementation

See the `doc` folder for the specification, threat model and rationale.

## What this is not
A C2 transport protocol. This protocol is only concerned with cryptographically protecting the data transmitted between a beacon and its server. It does not know anything about how data should be transported or where. Therefore, the intent is for this protocol to be used in a way that ryhmes with this:
```c++
class transport {
    // ...
    std::vector<uint8_t> network_send(const uint8_t* ptr, size_t len);
    // ...
};

bool transport::send(const std::span<const uint8_t> data) {
    uint8_t* encrypted_ptr = nullptr;
    size_t encrypted_len = 0;
    size_t encrypted_capa = 0;
    if (encrypt_to_server(data.data(), data.size(), encrypted_ptr, encrypted_len, encrypted_capa) == 0) {
        auto response = this->network_send(encrypted_ptr, encrypted_len);
        free_vec(encrypted_ptr, encrypted_len, encrypted_capa);
        // ...
    }
    return false;
}
```

In essence, this **only** handles crypto, you still get to do whatever you want on the transport side.

## Limitations
In short: PQ algorithms take a lot more space than classical ones.
This is unfortunately unavoidable. Therfore, the initial registration handshake will be somewhat large.
The ML-KEM public key and ciphertext combined take up ~2.2kb by themselves.
This overhead will grow larger when hybrid signatures are implemented.
Thankfully, this only affects the registration handshake.
No subsequent messages are affected, as they only use symmetric cryptography.
Follow-on messages use symmetric cryptography with CBOR framing.

Earlier builds measured ~6.5MB for the static lib, or ~2MB when building the stdlib with a nightly toolchain. This is largely due to the fact that we need to bring a bunch of rust stuff with us. Unfortunately, most crypto libraries aren't really meant to run in 40KB images, so there's always going to be some floor there. It should however be easy to cut the rust-related stuff by implementing this protocol in C or C++, though you'll still have to pay for the libsodium library.

It is very likely that neither the rust nor C interfaces are thread-safe.

# TODOs
Test the C interface.

See about adding proofs.

Make the server interface thread-safe in rust.

# Reference implementation
I don't use rust a lot, so the code is probably fairly naive. It provides both a beacon and server implementation with C bindings through `cbindgen`. Ideally more bindings would be built on top of that so it can be used in the mythic server-side.

The reference implementation expects that all beacons are compiled with the server's public key, and that beaconcrypt is initialized with it.

Transport uses deterministic CBOR with an inclusive 32 MiB limit on complete encoded messages, including framing, authentication tags, and commitments; plaintext snapshots and JSON state are unaffected. The former Cap'n Proto wire format and public generated Rust modules are removed, so peers and queued messages must use the new [wire format](doc/protocol.md#wire-encoding).

Rust, C, Go, and Python support durable full-server state through a caller-supplied snapshot store. Snapshots contain plaintext secrets and are not self-authenticating; the store must protect their integrity and provenance, maintain one rollback-resistant authoritative head, and implement linearizable durable compare-and-swap. Store-backed servers commit accepted receives and other state-changing results before release, while a normally rejected receive preserves the complete state and performs no snapshot encoding or compare-and-swap. The bindings also retain checkpoint-only export and restoration for single-owner applications; those constructors require manual saving after every state-changing operation, and standalone checkpoint files cannot detect rollback. See [server-state persistence](doc/persistence.md) and the runnable examples for [Rust](beaconcrypt/examples/rust/main.rs), [Python](examples/python/main.py), [C](examples/c/main.c), and [Go](examples/go/main.go).

## Building
You will need a recent version of Rust; checked-in generated parsers require no schema compiler for normal builds.

The Cargo workspace contains the public `beaconcrypt` adapter, `no_std` `beaconcrypt-core` state machines, and [`beaconcrypt-parse`](beaconcrypt-parse/README.md) transport codecs.

For windows, I prefer building with stable-gnu for normal usage, and nightly-gnu for release builds. You can find the exact arguments I use to the the static library as small as possible in [release.yml](/.github\workflows\release.yml). The MSVC toolchain is expected to work just as well, I just like mingw.

Build and run all tests:
```bash
cargo test --workspace
cargo build -p beaconcrypt --features gobinds --release --target x86_64-pc-windows-gnu
go test -a -count=1 .
uv run maturin develop --uv
uv run pytest tests
```

The `-a` flag is required after rebuilding the Rust static library because Go's build cache does not detect changes to libraries linked through cgo. `-count=1` also prevents reuse of a cached successful test result.

### Mutation testing

Install `cargo-mutants` 27.1.0 and run the complete workspace mutation suite:

```bash
cargo install --locked cargo-mutants@27.1.0
cargo mutants --workspace --jobs 8
```

The [configuration](.cargo/mutants.toml) exercises all three crates through workspace tests and excludes imported generated parser sources, equivalent private-state mutations, and adapters covered by the Go and Python suites. After substantial code additions, every viable mutant must be caught; `mutants.out/missed.txt` and `mutants.out/timeout.txt` must be empty. Finish validation with a complete run without `--iterate`.

### Reproducing known-answer test vectors

The fixed cryptographic values used by the Rust known-answer tests can be
reproduced independently with Python and Go. Run both generators from the
repository root:

```bash
uv run python scripts/generate_kat_vectors.py
go run scripts/generate_kat_vectors.go
```

The Python generator uses PyCryptodome. The Go generator uses the Go team's
crypto packages from `golang.org/x/crypto`. Their output should be identical;
any difference indicates that the vectors or one of the generators has
diverged.

### Wycheproof

The test suite includes pinned [C2SP Wycheproof](https://github.com/C2SP/wycheproof)
vectors for X25519, Ed25519, ChaCha20-Poly1305-IETF, HKDF-SHA-512 and
ML-KEM-768. After cloning, initialize the vector submodule before running the
normal test suite:

```bash
git submodule update --init --recursive
cargo test
```

See [the Wycheproof test documentation](doc/wycheproof.md) for the coverage
matrix, result semantics and update procedure.

### Rooterberg

The test suite also runs pinned
[Rooterberg](https://github.com/bleichenbacher-daniel/Rooterberg) vectors for
X25519, Ed25519 signing and verification, ChaCha20-Poly1305-IETF,
HKDF-SHA-512 and BLAKE2b-512. Rooterberg is included as a Git submodule and is
initialized by the same command used for Wycheproof:

```bash
git submodule update --init --recursive
cargo test
```

See [the Rooterberg test documentation](doc/rooterberg.md) for the coverage
matrix, upstream format caveats and update procedure.

## Usage
The reference implementation is a library that can currently be used either from rust, through C FFI, go and python bindings. The C interface is tested directly and through the Go bindings. Note that 0-length messages are explicitly disallowed by the reference implementation, as my feeling is that such messages have no purpose except testing parser edge cases. The library also doesn't handle chnking of any kind and will try to process entire messages at once in memory. It is expected that the caller should handle chunking itself if that is required.

From Rust, usage is mostly just constructing role-specific `Server` and `Beacon` objects. See the [example](beaconcrypt/examples/rust/main.rs) for usage.

Existing Rust callers must replace `BeaconCryptPqxdh` with the appropriate `Server` or `Beacon` type. C callers must use the matching `beaconcrypt_server_free` or `beaconcrypt_beacon_free` and role-specific identity functions; `beaconcrypt_export_state` is now `beaconcrypt_server_export_state`. Server checkpoints are binary snapshots: Go's `NewServerFromState` accepts `[]byte`, and Python's state export and restoration use `bytes` instead of JSON strings. See the persistence documentation for format compatibility and storage requirements.

From python, you can just use the wheels published to pypi, see the [example](examples/python/main.py) for usage.

The [C interface](beaconcrypt/src/cbinds.rs) uses opaque role-specific handles; the caller is responsible for their lifetimes and for freeing returned buffers. See the [example](examples/c/main.c) for usage.

Go is unfortunately the worst off as the bindings use cgo and therefore building your binary requires being able to link to a version of the library built with the `gobinds` feature. See the [example](examples/go/main.go) for usage.

# Copyright
This work is dedicated to the public domain.

Imported generated parsers retain their [Apache-2.0 license](beaconcrypt-parse/generated/LICENSE).

The C and go bindings, as well as most tests and the GH action code were generated by an LLM. This includes the KAT generation scripts, the ChaCha20-Poly1305 invisible salamanders implementation and its associated documentation.
