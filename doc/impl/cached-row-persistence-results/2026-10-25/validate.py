import os,subprocess
from pathlib import Path
os.chdir('/home/user/worktrees/beaconcrypt-row-persistence')
os.environ['PATH']=':'.join(['/tmp/bc-arc-scratch/row-persistence-20261025','/home/user/.rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin','/home/user/.cargo/bin','/nix/store/9wyldz5qids294k9h5qcg1f72i52jidi-gnumake-4.4.1/bin',os.environ['PATH']])
os.environ.update(RUSTFLAGS='-C linker-features=-lld', CARGO_PROFILE_TEST_OPT_LEVEL='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='1', RUST_TEST_THREADS='1')
import json
os.environ.update(NEXTEST_TEST_THREADS='1',NEXTEST_RETRIES='0')
commands=[['cargo', 'fmt', '--all'], ['cargo', 'clippy', '--workspace', '--all-targets', '--all-features', '--locked'], ['cargo', 'nextest', 'run', '--workspace', '--locked', '--lib', '--config=profile.test.package."*".opt-level=1', '--test=authentication', '--test=beacon', '--test=cached_row_persistence', '--test=codec', '--test=construction', '--test=general_registration_admission', '--test=message_size', '--test=mldsa', '--test=persistence_properties', '--test=properties', '--test=protocol', '--test=ratchet_properties', '--test=raw_receive', '--test=record_opening', '--test=registration_completion', '--test=registration_properties', '--test=registration_response_alias', '--test=rooterberg', '--test=row_persistence', '--test=server', '--test=wycheproof', '--config-file=/tmp/bc-arc-scratch/row-persistence-20261025/nextest.toml', '--fail-fast'], ['env', 'PROPTEST_CASES=128', 'cargo', 'test', '--locked', '-p', 'beaconcrypt', '--test', 'cached_row_persistence', '--config=profile.test.package."*".opt-level=1'], ['cargo', 'check', '--locked', '-p', 'beaconcrypt', '--no-default-features', '--features', 'pqxdh,beacon', '--lib'], ['cargo', 'check', '--locked', '-p', 'beaconcrypt', '--no-default-features', '--features', 'pqxdh,server', '--lib'], ['cargo', 'test', '--locked', '--workspace', '--doc']]
cluster=json.loads(Path('/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/postgres-cluster.json').read_text())
data=Path(cluster['data_directory']);pgctl=str(Path(cluster['binary_directory'])/'pg_ctl')
(data/'BC_TEST_CLUSTER_ONLY').write_text('Owned ephemeral cached-row validation and benchmark cluster.\n')
os.environ.update(BC_PERSISTENCE_PG_DSN=cluster['dsn'],BEACONCRYPT_BENCH_POSTGRES=cluster['dsn'],BC_PG_TEST_OWNED_DATA=str(data),BC_PG_TEST_PG_CTL=pgctl)
started=False
with open('/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/validation.log','w') as log:
 def run(cmd):
  print('RUN:',cmd,flush=True);print('RUN:',cmd,file=log,flush=True)
  status=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT).returncode
  print('EXIT:',status,flush=True);print('EXIT:',status,file=log,flush=True)
  if status:
   print(Path(log.name).read_text()[-12000:]);raise SystemExit(status)
 try:
  for command in commands: run(command)
  run([pgctl,'start','-D',str(data),'-w','-t','30','-l',str(data.parent/'postgres-validation.log')]);started=True
  run(['cargo','test','--locked','-p','beaconcrypt','--example','persistence_bench','--config=profile.test.package."*".opt-level=1','--','--include-ignored'])
 finally:
  if started: subprocess.run([pgctl,'stop','-D',str(data),'-m','fast','-w','-t','30'],stdout=log,stderr=subprocess.STDOUT)
