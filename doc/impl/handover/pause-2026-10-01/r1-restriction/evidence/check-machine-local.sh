#!/usr/bin/env bash
set -euo pipefail
bc_r1_module="$1"
bc_r1_root=/tmp/beaconcrypt-registration-r1-common-restriction/beaconcrypt-core/proofs/lean
bc_r1_out=/tmp/beaconcrypt-registration-r1-restriction-check/olean/BeaconcryptCore/Computational/$bc_r1_module.olean
if test -L "$bc_r1_out"; then
  printf '%s\n' 'Refusing to overwrite linked dependency artifact' >&2
  exit 2
fi
export LEAN_PATH="$(cat /tmp/beaconcrypt-registration-r1-restriction-check/leanpath)"
exec flock /tmp/bc-arc-scratch/lean.lock timeout 180 /home/user/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean -j1 -M8000 --root="$bc_r1_root" -o "$bc_r1_out" "$bc_r1_root/BeaconcryptCore/Computational/$bc_r1_module.lean"
