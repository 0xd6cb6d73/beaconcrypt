#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd -- "$script_dir/.." && pwd)"
cd -- "$repo_dir"

read -r expected_rust expected_zig wasm_target < <(
  python3 -c 'import json; p=json.load(open("scripts/wasm-toolchain.json")); print(p["rust"], p["zig"], p["target"])'
)
actual_rust="$(rustc --version)"
actual_zig="$(zig version)"
if [[ "$actual_rust" != "rustc $expected_rust "* ]]; then
  printf 'Wasm builds require Rust %s; found %s\n' "$expected_rust" "$actual_rust" >&2
  exit 1
fi
if [[ "$actual_zig" != "$expected_zig" ]]; then
  printf 'Wasm builds require Zig %s; found %s\n' "$expected_zig" "$actual_zig" >&2
  exit 1
fi

# A caller's relative CARGO_TARGET_DIR is interpreted relative to this repository.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$repo_dir/target}"
export ZIG_GLOBAL_CACHE_DIR="${ZIG_GLOBAL_CACHE_DIR:-$repo_dir/.build/zig-cache}"
cargo build --locked --release -p beaconcrypt-wasm --target "$wasm_target"
mkdir -p -- "$repo_dir/internal/wasm"
cp -- "$CARGO_TARGET_DIR/$wasm_target/release/beaconcrypt_wasm.wasm" \
  "$repo_dir/internal/wasm/beaconcrypt.wasm"
python3 "$script_dir/package-wasm.py" --record-build
