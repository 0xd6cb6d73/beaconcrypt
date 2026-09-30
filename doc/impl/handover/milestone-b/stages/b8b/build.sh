#!/usr/bin/env bash
# Usage: build.sh <ModuleName> (e.g. TestA): compiles src/B8bScratch/<ModuleName>.lean to olean/B8bScratch/<ModuleName>.olean through the shared lock.
# Usage: build.sh --check <file>: elaborates a file (no olean) with the scratch olean path.
set -o pipefail
O=/tmp/bc-arc-scratch/c-work/b8b/olean
S=/tmp/bc-arc-scratch/c-work/b8b/src
cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean
if [ "$1" = "--check" ]; then
  flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env bash -c "LEAN_PATH=$O:\$LEAN_PATH lean $2" 2>&1 | grep -v "has local changes"
else
  mkdir -p $O/B8bScratch
  flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env bash -c "LEAN_PATH=$O:\$LEAN_PATH lean --root=$S -o $O/B8bScratch/$1.olean -i $O/B8bScratch/$1.ilean $S/B8bScratch/$1.lean" 2>&1 | grep -v "has local changes"
fi
