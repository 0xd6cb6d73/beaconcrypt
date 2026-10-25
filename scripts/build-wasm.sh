#!/usr/bin/env bash
# SPDX-License-Identifier: 0BSD
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd -- "$script_dir/.." && pwd)"
cd -- "$repo_dir"

read -r expected_rust wasm_target < <(
  python3 -c 'import json; p=json.load(open("scripts/wasm-toolchain.json")); print(p["rust"], p["target"])'
)
actual_rust="$(rustc --version)"
if [[ "$actual_rust" != "rustc $expected_rust "* ]]; then
  printf 'Wasm builds require Rust %s; found %s\n' "$expected_rust" "$actual_rust" >&2
  exit 1
fi

# A caller's relative CARGO_TARGET_DIR is interpreted relative to this repository.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$repo_dir/target}"
cargo build --locked --release -p beaconcrypt-wasm --target "$wasm_target"
mkdir -p -- "$repo_dir/internal/wasm"
cp -- "$CARGO_TARGET_DIR/$wasm_target/release/beaconcrypt_wasm.wasm" \
  "$repo_dir/internal/wasm/beaconcrypt.wasm"
python3 "$script_dir/package-wasm.py" --record-build
