#!/usr/bin/env python3
"""Refresh sha256 entries in reviewed-inventory.txt for the given paths (relative to beaconcrypt-core); print old/new."""
import hashlib, sys
from pathlib import Path
core = Path('/tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core')
manifest = core / 'proofs/reviewed-inventory.txt'
lines = manifest.read_text().split('\n')
targets = set(sys.argv[1:])
seen = set()
for i, line in enumerate(lines):
    parts = line.split('\t')
    if len(parts) == 3 and parts[2] in targets:
        new = hashlib.sha256((core / parts[2]).read_bytes()).hexdigest()
        if new != parts[1]:
            print(f'{parts[2]}: {parts[1][:12]} -> {new[:12]}')
            lines[i] = '\t'.join((parts[0], new, parts[2]))
        else:
            print(f'{parts[2]}: unchanged')
        seen.add(parts[2])
missing = targets - seen
if missing:
    print('NOT IN MANIFEST:', sorted(missing)); sys.exit(1)
manifest.write_text('\n'.join(lines))
