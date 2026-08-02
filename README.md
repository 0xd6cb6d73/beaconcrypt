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
In short: PQ algorithms take a lot more space than classical ones. This is unfortunately unavoidable. Therfore, the initial registration handshake will be somewhat large (~2.2kb for ML-KEM). However, this does not impact any follow on messages, for which the only overhead is the captn' proto framing.

The reference implementation is large, ~6.5MB for the static lib. It goes down to ~3.5MB if building the stdlib ourselves with a nightly toolchain. This is largely due to the fact that we need to bring a bunch of rust stuff with us. Unfortunately, most crypto libraries aren't really meant to run in 40KB images, so there's always going to be some floor there. It should however be easy to cut the rust-related stuff by implementing this protocol in C or C++, though you'll still have to pay for the libsodium + captn proto libraries.

The C interfaces are probably not thread safe.

## Formal verification

The proof suite includes an explicit failed-active-receive scenario. A correctly parsed, correctly sized future frame can be admitted before authentication, advance the receive chain, and retain every derived key when authentication fails. The finite server-to-beacon ProVerif trace fills the exact 50-key cache, confirms that the next future receive is rejected without another state change, retries the retained target, accepts its later honest ciphertext, rejects replay, and admits another future key after the successful receive frees a slot. General, direction-independent receive-gap, capacity, retry, and replay facts are proved separately over the extracted Rust control state in F*.

This result is deliberately conditional. The private-state run concurrently allows attacker-owned beacon registration and confirms the attacker can read that beacon's routed canary, while the independently rooted legitimate failed-receive canaries remain secret. Compromise after the failed receive exposes the skipped and target key material plus the live future chain, permits attacker forgery, and still leaves a trace in which the later honest target ciphertext is delivered successfully; it does not guarantee that the attacker will allow that delivery. Cap'n Proto parsing, serialized byte lengths, end-to-end linkage of the standalone record root to registration, concrete cryptographic implementations, and arbitrary receive schedules remain outside the finite ProVerif trace. See [the formal-verification analysis](doc/formal-verification-analysis.md#failed-active-receive-state-and-compromise) for the exact claim and limitations.

# TODOs
Test the C interface

# Reference implementation
I don't use rust a lot, so the code is probably fairly naive. It provides both a beacon and server implementation with C bindings through `cbindgen`. Ideally more bindings would be built on top of that so it can be used in the mythic server-side.

The reference implementation expects that all beacons are compiled with the server's public key, and that beaconcrypt is initialized with it.

The server is currently not very usable as it doesn't support saving the state of any individual beacon. This means that if your server goes down, you will not be able to communicate with any previously-registered beacons anymore. The server does support being initialized with an Ed25519 seed (32 random bytes). Users wishing to use the server in practical cases should use this interface to ensure their server keeps its identity across reboots.

## Building
You will need [Capn'Proto](https://capnproto.org/install.html) (just the binaries) and a recent version of rust for every build.

For windows, I prefer building with stable-gnu for normal usage, and nightly-gnu for release builds. You can find the exact arguments I use to the the static library as small as possible in [release.yml](/.github\workflows\release.yml). The MSVC toolchain is expected to work just as well, I just like mingw.

Build and run all tests:
```bash
cargo test
cargo build --features gobinds --release --target x86_64-pc-windows-gnu
go test -a -count=1 .
uv run maturin develop --uv
uv run pytest tests
```

The `-a` flag is required after rebuilding the Rust static library because Go's build cache does not detect changes to libraries linked through cgo. `-count=1` also prevents reuse of a cached successful test result.

### Mutation testing

Mutation testing uses [cargo-mutants](https://mutants.rs/) 27.1.0. Install the pinned version and run the complete workspace mutation suite from the repository root:

```bash
cargo install --locked cargo-mutants@27.1.0
cargo mutants --workspace --jobs 2
```

The checked-in [configuration](.cargo/mutants.toml) runs the top-level integration and vector tests for mutations in both `beaconcrypt` and `beaconcrypt-protocol-core`. It excludes the feature-gated C and Python adapters because those are exercised by their language-specific test suites, and it documents narrowly scoped equivalent mutations that cannot occur through valid public state.

A successful run exits with status zero and reports every viable mutant as caught. Detailed outcomes are written to `mutants.out/`; `missed.txt` and `timeout.txt` must both be empty. Mutants classified as unviable failed to compile and do not indicate a test gap.

After adding tests for missed mutants, rerun only the previous misses and any newly discovered mutants with:

```bash
cargo mutants --workspace --jobs 2 --iterate
```

Do not use `--iterate` for the final verification pass; finish with the complete non-iterative command so stale results cannot hide a regression. Mutation testing covers the Rust implementation and complements, but does not replace, `make -C crates/protocol-core verify` or the Go and Python binding tests.

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
The reference implementation is a library that can currently be used either from rust, through C FFI, go and python bindings. The C interface is currently only tested through the go bindings. Note that 0-length messages are explicitly disallowed by the reference implementation, as my feeling is that such messages have no purpose except testing parser edge cases. The library also doesn't handle chnking of any kind and will try to process entire messages at once in memory. It is expected that the caller should handle chunking itself if that is required.

From Rust, usage is mostly just instantiating `CryptoProvider` objects. See the [example](examples/rust/main.rs) for usage.

From python, you can just use the wheels published to pypi, see the [example](examples/python/main.py) for usage.

The [C interface](src/cbinds.rs) emulates the class interface, the caller is responsible for providing a valid state object to every function. See the [example](examples/c/main.c) for usage.

Go is unfortunately the worst off as the bindings use cgo and therefore building your binary requires being able to link to a version of the library built with the `gobinds` feature. See the [example](examples/go/main.go) for usage.

# Copyright
This work is dedicated to the public domain.

The C and go bindings, as well as most tests and the GH action code were generated by an LLM. This includes the KAT generation scripts, the ChaCha20-Poly1305 invisible salamanders implementation and its associated documentation.
