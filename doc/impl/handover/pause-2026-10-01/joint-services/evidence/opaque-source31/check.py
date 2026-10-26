# Single-module Lean 4.34 direct check for the opaque-kem-source lane (topic worktree /tmp/beaconcrypt-native-accept-cut).
from pathlib import Path
import sys, os, subprocess, datetime, json, hashlib
s = Path(__file__).parent
w = Path('/tmp/beaconcrypt-opaque-kem-source/beaconcrypt-core/proofs/lean')
module = sys.argv[1]
tag = sys.argv[2] if len(sys.argv) > 2 else ''
rel = module.replace('.', '/')
src = w / (rel + '.lean')
art = s / 'olean' / (rel + '.olean')
art.parent.mkdir(parents=True, exist_ok=True)
(s / 'logs').mkdir(exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = (s / 'leanpath').read_text().strip()
cmd = ['flock', '/tmp/bc-arc-scratch/lean.lock', 'timeout', '180',
       '/home/user/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean',
       '-j1', '-M8000', '--root=' + str(w), '-o', str(art), str(src)]
name = module.rsplit('.', 1)[-1] + (('-' + tag) if tag else '')
log = s / 'logs' / (name + '.log')
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
if art.exists() and not art.is_symlink():
    art.unlink()
with log.open('wb') as out:
    r = subprocess.run(cmd, cwd=w, env=env, stdout=out, stderr=subprocess.STDOUT)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
row = {'module': module, 'start': start, 'end': datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'exit': r.returncode, 'source_sha256': sha(src), 'log_sha256': sha(log), 'command': cmd,
       'leanpath_sha256': sha(s / 'leanpath')}
if r.returncode == 0:
    row['artifact_sha256'] = sha(art)
(s / 'logs' / (name + '.json')).write_text(json.dumps(row, indent=2) + '\n')
print(log.read_text())
print('exit', r.returncode)
sys.exit(r.returncode)
