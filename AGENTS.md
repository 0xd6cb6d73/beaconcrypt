# Repository Guidelines

## Project Structure & Module Organization

The repository root is a virtual Cargo workspace. The public adapter crate lives in `beaconcrypt/`; `beaconcrypt/src/beacon.rs` and `beaconcrypt/src/server.rs` implement the protocol roles, while `beaconcrypt/src/cbinds.rs`, `beaconcrypt/src/pybinds.rs`, and the top-level Go files expose language bindings. Cap'n Proto schemas are under `beaconcrypt/src/schema/`. The dependency-free, `no_std` state-machine boundary is the workspace crate in `beaconcrypt-core/`, with F* and ProVerif material in its `proofs/` directory. Rust integration tests live in `beaconcrypt/tests/`, while root `tests/` contains only Python tests. The Rust example lives in `beaconcrypt/examples/rust/`; C, Go, and Python examples remain under root `examples/`. Read and write implementation plans, completion guides, and historical implementation records in `doc/impl/`. Protocol specifications, threat analysis, persistence notes, verification analysis, and other maintained reference documentation belong directly in `doc/`. `wycheproof/` and `rooterberg/` are pinned test-vector submodules; do not edit them as source trees.

## Build, Test, and Development Commands

Install a Rust toolchain (the crate declares Rust 1.96), Cap'n Proto binaries, and initialize submodules:

```bash
git submodule update --init --recursive
cargo build
cargo test
cargo check -p beaconcrypt --no-default-features --features pqxdh,beacon --lib
cargo check -p beaconcrypt --no-default-features --features pqxdh,server --lib
```

For bindings, run `cargo build -p beaconcrypt --release --features gobinds` before `go test -race ./...`. Build the Python extension with `uv run maturin develop --uv`, then run `uv run pytest tests`. Before spawning agents that may run proofs, the coordinator must run `make -C beaconcrypt-core prepare-proof-shell` once; the normal proof targets then reuse the shared profile instead of realizing separate environments. Core changes require `make -C beaconcrypt-core verify`; this uses the locked Nix proof environment and checks generated proofs. Run `make -C beaconcrypt-core check-inventory` separately for the trust-boundary inventory. Shared content-keyed profiles are intentional garbage-collection roots. Retire an obsolete profile only after every agent and coordinator using it has stopped, then run `nix-collect-garbage`; never retire a profile or run garbage collection while another agent or process is still using Nix.

## Coding Style & Naming Conventions

Use Rust 2024 idioms and run `cargo fmt --all` plus `cargo clippy --workspace --all-targets --all-features` before review. Rust formatting uses hard tabs and a 100-column limit (`rustfmt.toml`). Follow Rust naming: `snake_case` for modules, functions, and tests; `CamelCase` for types; `SCREAMING_SNAKE_CASE` for constants. Format Python with Black and Go with `gofmt`. Keep FFI behavior synchronized across Rust, `beaconcrypt/bindings.h`, Go, Python stubs, and examples when public APIs change.

Mid-sentence line breaks MUST NOT be added in Markdown or other text files.

## Testing Guidelines

Add Rust integration coverage as `beaconcrypt/tests/<area>.rs` and Python tests as `tests/test_<area>.py`. Exercise success, authentication failure, replay, malformed input, and state-rollback behavior for cryptographic changes. New behavior and regressions should receive focused tests. After every substantial code addition, run the complete mutation suite and fix every missed or timed-out viable mutant before considering the work complete. Never silently regenerate known-answer or proof artifacts—review their diffs and document why they changed. New proofs and substantial changes to existing proofs MUST include a plain-English explanation in `doc/formal-verification-analysis.md`.

## Commit & Pull Request Guidelines

History favors short, imperative, sentence-case subjects such as `Add rooterberg tests` or `Protect go interface with mutex`. Keep commits focused; isolate version bumps and generated artifacts when practical. Pull requests should explain protocol/security impact, list commands run, link relevant issues or design documents, and call out wire-format, binding, persistence, test-vector, or trust-boundary changes.
