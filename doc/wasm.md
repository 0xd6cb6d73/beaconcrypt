<!-- SPDX-License-Identifier: 0BSD -->

# Go consumers with an embedded Wasm backend

The Go import path and public API remain
`github.com/0xd6cb6d73/beaconcrypt`. With CGO enabled, the package uses its native
Rust bindings. `CGO_ENABLED=0` selects wazero; the build tag
`beaconcrypt_wazero` selects wazero even when CGO is enabled. The dependency
embeds its Wasm module into the final Go executable. Applications use the same
constructors and methods, without an initialization call or runtime Wasm file.
The root Go module requires Go 1.25 or newer for both native CGO and wazero
consumers.

The generated `.wasm` is not committed to Git. A Git checkout or ordinary Go
module proxy download therefore needs build preparation before selecting
wazero. Maintainers can build the guest from source; consumers can use the
release Go bundle, which already contains it. A build tag alone cannot supply
the missing artifact.

## Build the guest from source

Install the versions in [wasm-toolchain.json](../scripts/wasm-toolchain.json):
Rust 1.97.1, its `wasm32-wasip1` target, and Zig 0.16.0 on `PATH`. Then run:

```sh
rustup toolchain install 1.97.1 --profile minimal --target wasm32-wasip1
RUSTUP_TOOLCHAIN=1.97.1 bash scripts/build-wasm.sh
CGO_ENABLED=0 go test ./...
CGO_ENABLED=1 go test -tags=beaconcrypt_wazero ./...
```

The script checks the installed Rust/Cargo/Zig versions, builds the
`beaconcrypt-wasm` workspace member with `--locked --release`, and writes
`internal/wasm/beaconcrypt.wasm` and `internal/wasm/beaconcrypt.build.json`.
Both files are ignored by Git. `CARGO_TARGET_DIR` is honored; a relative value
is interpreted from the repository root. Zig's global cache defaults to
`.build/zig-cache` and honors `ZIG_GLOBAL_CACHE_DIR`. The generated module requires no
Wasmtime, Wasmi, JavaScript or Emscripten dependency.

The guest uses the existing Rust protocol, codecs, libsodium and persistence
implementation. Go supplies secure randomness before guest initialization and
implements snapshot-store callbacks. Compilation is shared; each server or
beacon retains its own guest memory and serialized operations. Server state
still requires the storage guarantees described in [persistence.md](persistence.md).

## Create a release bundle

After building the guest, run:

```sh
python3 scripts/package-wasm.py --version v0.6.0 --output-dir dist/wasm
```

Release CI adds `--require-clean`. The command rejects a changed Wasm artifact,
revision or Rust/build inputs since generation. Its outputs are:

- `beaconcrypt-go-v0.6.0-wasm.tar.gz`, containing the complete root Go package,
  internal Go packages, C shim/header sources, `go.mod`, `go.sum`, licenses,
  embedded Wasm and a manifest under `beaconcrypt-go-v0.6.0/`.
- `beaconcrypt.wasm`, the standalone guest module.
- `beaconcrypt-wasm-manifest.json`, with ABI version 1, exact source revision,
  dirty-source marker, tool versions, build inputs, import/export inventory and
  SHA-256 hashes for the Wasm and bundled files.
- `SHA256SUMS`, covering the archive and standalone release assets.

Archive ordering, permissions and timestamps are deterministic for identical
inputs. The pinned recipe and provenance support rebuilding the module; this
does not claim byte-identical Rust/Zig output across arbitrary build hosts.
The current import allowlist excludes filesystem, clock and network access.
The Go loader validates the ABI and function signatures when using the module.

## Build an existing application from the release bundle

The builder downloads a pinned release bundle, verifies its expected checksum,
and extracts it into a writable per-build directory outside `GOMODCACHE`.
The bundle's module path stays unchanged. For an existing application such as
Poseidon, use an alternate modfile and a local replacement; application Go files
and its checked-in dependency files remain unchanged.

From the application's module directory, with absolute paths in `build_dir`
and `beaconcrypt_dir`:

```sh
cp go.mod "$build_dir/consumer.mod"
cp go.sum "$build_dir/consumer.sum"
GOWORK=off go mod edit -modfile="$build_dir/consumer.mod" \
  -replace="github.com/0xd6cb6d73/beaconcrypt=$beaconcrypt_dir"
GOWORK=off CGO_ENABLED=0 go build -mod=mod \
  -modfile="$build_dir/consumer.mod" -tags=beaconcrypt_wazero ./...
```

Use the application's normal package arguments, output flags and target
`GOOS`/`GOARCH`. `-mod=mod` permits updates only to the alternate mod/sum files
and avoids an existing vendor directory selecting stale dependencies.
`GOWORK=off` is needed because `-modfile` cannot be used in workspace mode.
Release bundle hashes provide provenance for the local replacement, which is
outside the ordinary Go module checksum mechanism.

The source Git tag remains usable for native CGO builds. The release bundle
provides the extra generated artifact for wazero builds; it is not a different
module zip republished under the Git tag's existing proxy checksum.

## Validation and resource limits

CI builds the guest once per workflow and shares that artifact across the Go
platform matrix. It tests native CGO, CGO disabled and forced wazero selections,
then cross-builds the existing consumer for Linux amd64/arm64, macOS amd64/arm64 and
Windows amd64. A separate job extracts and tests the release bundle outside the
checkout. Packaging tests run without downloading tools:

```sh
python3 -m unittest discover -s scripts -p 'test_package_wasm.py' -v
```

The complete encoded-message limit remains 32 MiB, including framing and
authentication. It is not a plaintext, snapshot or JSON-state limit. Each guest
instance has a 256 MiB memory cap. The one-peer test fixture measured about
193 MiB sender and 97 MiB receiver guest memory at that boundary; these are
separate instances and exclude host memory. Those measurements do not bound
memory use for other peer counts or snapshot sizes. Resource exhaustion
invalidates the affected handle. The Wasm backend's memory and
throughput costs should be measured with the application's peer counts and
message sizes. Functional interoperability does not establish constant-time
behavior of generated native code.
