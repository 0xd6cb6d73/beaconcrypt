# Repository Guidelines

## Project Structure & Module Organization

The main Rust crate lives in `src/`; `beacon.rs` and `server.rs` implement the protocol roles, while `cbinds.rs`, `pybinds.rs`, and the top-level Go files expose language bindings. Cap'n Proto schemas are under `src/schema/`. The dependency-free, `no_std` state-machine boundary is the workspace crate in `crates/protocol-core/`, with F* and ProVerif material in its `proofs/` directory. Integration tests live in `tests/`; examples are grouped by language in `examples/`. Read and write implementation plans, completion guides, and historical implementation records in `doc/impl/`. Protocol specifications, threat analysis, persistence notes, verification analysis, and other maintained reference documentation belong directly in `doc/`. `wycheproof/` and `rooterberg/` are pinned test-vector submodules; do not edit them as source trees.

## Build, Test, and Development Commands

Install a Rust toolchain (the crate declares Rust 1.96), Cap'n Proto binaries, and initialize submodules:

```bash
git submodule update --init --recursive
cargo build
cargo test
cargo check --no-default-features --features pqxdh,beacon --lib
cargo check --no-default-features --features pqxdh,server --lib
```

For bindings, run `cargo build --release --features gobinds` before `go test -race ./...`. Build the Python extension with `uv run maturin develop --uv`, then run `uv run pytest tests`. Protocol-core changes require `make -C crates/protocol-core verify`; this uses the locked Nix proof environment and checks generated proofs and the trust-boundary inventory.

## Coding Style & Naming Conventions

Use Rust 2024 idioms and run `cargo fmt --all` plus `cargo clippy --all-targets --all-features` before review. Rust formatting uses hard tabs and a 100-column limit (`rustfmt.toml`). Follow Rust naming: `snake_case` for modules, functions, and tests; `CamelCase` for types; `SCREAMING_SNAKE_CASE` for constants. Format Python with Black and Go with `gofmt`. Keep FFI behavior synchronized across Rust, `bindings.h`, Go, Python stubs, and examples when public APIs change.

Mid-sentence line breaks MUST NOT be added in Markdown or other text files.

## Testing Guidelines

Add Rust integration coverage as `tests/<area>.rs` and Python tests as `tests/test_<area>.py`. Exercise success, authentication failure, replay, malformed input, and state-rollback behavior for cryptographic changes. New behavior and regressions should receive focused tests. Never silently regenerate known-answer or proof artifacts—review their diffs and document why they changed. New proofs and substantial changes to existing proofs MUST include a plain-English explanation in `doc/formal-verification-analysis.md`.

## Commit & Pull Request Guidelines

History favors short, imperative, sentence-case subjects such as `Add rooterberg tests` or `Protect go interface with mutex`. Keep commits focused; isolate version bumps and generated artifacts when practical. Pull requests should explain protocol/security impact, list commands run, link relevant issues or design documents, and call out wire-format, binding, persistence, test-vector, or trust-boundary changes.
