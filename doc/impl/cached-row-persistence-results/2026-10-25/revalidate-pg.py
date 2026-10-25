import json
import os
from pathlib import Path
import subprocess

root = Path('/tmp/bc-arc-scratch/row-persistence-20261025/hybrid')
os.chdir('/home/user/worktrees/beaconcrypt-row-persistence')
os.environ['PATH'] = ':'.join(['/tmp/bc-arc-scratch/row-persistence-20261025', '/home/user/.rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin', '/home/user/.cargo/bin', '/nix/store/9wyldz5qids294k9h5qcg1f72i52jidi-gnumake-4.4.1/bin', os.environ['PATH']])
os.environ.update(RUSTFLAGS='-C linker-features=-lld', CARGO_PROFILE_TEST_OPT_LEVEL='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='1', RUST_TEST_THREADS='1')
cluster = json.loads((root / 'postgres-cluster.json').read_text())
data = Path(cluster['data_directory'])
pgctl = str(Path(cluster['binary_directory']) / 'pg_ctl')
os.environ.update(BC_PERSISTENCE_PG_DSN=cluster['dsn'], BEACONCRYPT_BENCH_POSTGRES=cluster['dsn'], BC_PG_TEST_OWNED_DATA=str(data), BC_PG_TEST_PG_CTL=pgctl)
started = False
with (root / 'pg-revalidation.log').open('w') as log:
    def run(cmd):
        print('RUN:', cmd, flush=True)
        print('RUN:', cmd, file=log, flush=True)
        status = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT).returncode
        print('EXIT:', status, flush=True)
        print('EXIT:', status, file=log, flush=True)
        if status:
            raise SystemExit(status)
    try:
        run([pgctl, 'start', '-D', str(data), '-w', '-t', '30', '-l', str(root / 'postgres-validation.log')])
        started = True
        run([str(Path(cluster['binary_directory']) / 'psql'), cluster['dsn'], '-At', '-c', 'SELECT inet_server_addr()::text,host(inet_server_addr())'])
        run(['cargo', 'test', '--locked', '-p', 'beaconcrypt', '--example', 'persistence_bench', '--config=profile.test.package."*".opt-level=1', '--', '--include-ignored'])
    finally:
        if started:
            subprocess.run([pgctl, 'stop', '-D', str(data), '-m', 'fast', '-w', '-t', '30'], stdout=log, stderr=subprocess.STDOUT)
        log.flush()
        print((root / 'pg-revalidation.log').read_text()[-18000:])
