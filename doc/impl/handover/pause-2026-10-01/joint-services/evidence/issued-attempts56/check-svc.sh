#!/usr/bin/env bash
# Service-composition focused Lean check after the pin-width merge, copied from
# /tmp/beaconcrypt-registration-joint-service-check/check.sh (plan section 7.1). The proof root is
# unchanged; the output and first LEAN_PATH entry is the fresh prefix
# /tmp/beaconcrypt-pin-width-olean/svc, which mirror-svc.sh populates as a full symlink mirror of
# the lane's olean tree without the modules downstream of PqxdhRegistrationScheduleSurface. The
# rest of LEAN_PATH is the lane's leanpath file, unchanged. A module's own olean/ilean symlinks are
# removed before Lean writes, so nothing is written through a link into another environment.
# Usage: bash check-svc.sh <ModuleName> (short name under BeaconcryptCore/Computational).
set -euo pipefail
module="$1"
root=/tmp/beaconcrypt-registration-joint-service-composition/beaconcrypt-core/proofs/lean
private_prefix=/tmp/beaconcrypt-pin-width-olean/svc
out="$private_prefix/BeaconcryptCore/Computational/$module.olean"
mkdir -p "$(dirname "$out")"
for extension in olean ilean; do
  if [[ -L "$private_prefix/BeaconcryptCore/Computational/$module.$extension" ]]; then rm "$private_prefix/BeaconcryptCore/Computational/$module.$extension"; fi
done
export LEAN_PATH="$private_prefix:$(cat /tmp/beaconcrypt-registration-joint-service-check/leanpath)"
exec flock /tmp/bc-arc-scratch/lean.lock timeout 900 /home/user/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean -j1 -M8000 --root="$root" -o "$out" "$root/BeaconcryptCore/Computational/$module.lean"
