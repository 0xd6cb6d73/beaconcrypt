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

# TODOs
Test the C interface

# Reference implementation
I don't use rust a lot, so the code is probably fairly naive. It provides both a beacon and server implementation with C bindings through `cbindgen`. Ideally more bindings would be built on top of that so it can be used in the mythic server-side.

The reference implementation expects that all beacons are compiled with the server's public key, and that beaconcrypt is initialized with it.

The server is currently not very usable as it doesn't support saving the state of any individual beacon. This means that if your server goes down, you will not be able to communicate with any previously-registered beacons anymore. The server doesn't support being initialized with an Ed25519 seed (32 random bytes). Users wishing to use the server in practical cases should use this interface to ensure their server keeps its identity across reboots.

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

## Usage
The reference implementation is a library that can currently be used either from rust, through C FFI, go and python bindings. The C interface is currently not tested.

From Rust, usage is mostly just instantiating `CryptoProvider` objects. See the [example](examples/rust/main.rs) for usage.

From python, you can just use the wheels published to pypi, see the [example](examples/python/main.py) for usage.

There are two C interfaces at the moment. When using the legacy interface (without the `beaconcrypt` prefix) the library creates a global `CryptoProvider` object, whose methods are wrapped by the various functions in the interface. When using this interace, the caller is responsible for the buffers passed into the library. Assume the library does not do any copies, except for initialization functions, and never frees the buffers it is passed.

Using the [newer](src/cbinds.rs) C interface which emulate the class interface, the caller is responsible for providing a valid state object to every function. See the [example](examples/c/main.c) for usage.

Go is unfortunately the worst off as the bindings use cgo and therefore building your binary requires being able to link to a version of the library built with the `gobinds` feature. See the [example](examples/go/main.go) for usage.

# Copyright
This work is dedicated to the public domain.
