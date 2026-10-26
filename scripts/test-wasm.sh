#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd -- "$script_dir/.." && pwd)"
cd -- "$repo_dir"

read -r expected_rust wasm_target < <(
  python3 -c 'import json; p=json.load(open("scripts/wasm-toolchain.json")); print(p["rust"], p["target"])'
)
if [[ "$(rustc --version)" != "rustc $expected_rust "* ]]; then
  printf 'Wasm tests require Rust %s\n' "$expected_rust" >&2
  exit 1
fi

runner_dir="$(mktemp -d "${TMPDIR:-/tmp}/beaconcrypt-wasm-tests.XXXXXX")"
trap 'rm -rf -- "$runner_dir"' EXIT
go build -mod=readonly -buildvcs=false -o "$runner_dir/runner" ./scripts/wasm-test-runner
export CARGO_TARGET_WASM32_WASIP1_RUNNER="$runner_dir/runner"

if [[ "${1:-}" == --mutants ]]; then
  shift
  # A WASI runner must read its own worker's artifact after Cargo launches it.
  unset CARGO_TARGET_DIR
  cargo mutants -p beaconcrypt-wasm --config .cargo/mutants-wasm.toml --test-workspace false --copy-target true --cargo-arg "--target=$wasm_target" "$@"
else
  cargo test --locked -p beaconcrypt-wasm --target "$wasm_target" "$@"
fi
