#!/usr/bin/env bash
set -euo pipefail
module="$1"
root=/tmp/beaconcrypt-registration-joint-service-composition/beaconcrypt-core/proofs/lean
out=/tmp/beaconcrypt-registration-joint-service-check/olean/BeaconcryptCore/Computational/$module.olean
if test -L "$out"; then
  printf '%s\n' 'Refusing to overwrite linked dependency artifact' >&2
  exit 2
fi
export LEAN_PATH="$(cat /tmp/beaconcrypt-registration-joint-service-check/leanpath)"
exec flock /tmp/bc-arc-scratch/lean.lock timeout 240 /home/user/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean -j1 -M8000 --root="$root" -o "$out" "$root/BeaconcryptCore/Computational/$module.lean"
