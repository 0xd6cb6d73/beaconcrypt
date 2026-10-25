import os,subprocess
from pathlib import Path
os.chdir('/home/user/worktrees/beaconcrypt-row-persistence')
os.environ['PATH']=':'.join(['/tmp/bc-arc-scratch/row-persistence-20261025','/home/user/.rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin','/home/user/.cargo/bin','/nix/store/9wyldz5qids294k9h5qcg1f72i52jidi-gnumake-4.4.1/bin',os.environ['PATH']])
os.environ.update(RUSTFLAGS='-C linker-features=-lld', CARGO_PROFILE_TEST_OPT_LEVEL='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='1', RUST_TEST_THREADS='1')
os.environ['GOMAXPROCS']='1'
commands=[['cargo', 'check', '--locked', '-p', 'beaconcrypt', '--all-features', '--lib'], ['cargo', 'test', '--locked', '-p', 'beaconcrypt', '--features', 'gobinds', '--lib', 'row_cbinds::composition_tests', '--config=profile.test.package."*".opt-level=1'], ['cargo', 'build', '--locked', '-p', 'beaconcrypt', '--release', '--features', 'gobinds'], ['go', 'test', '-race', '-p', '1', './...'], ['env', 'CGO_ENABLED=0', 'go', 'test', '-p', '1', './...', '-run', 'TestRowPersistenceExplicitlyUnsupportedOnWasm'], ['uv', 'run', 'maturin', 'develop', '--uv'], ['uv', 'run', 'pytest', 'tests']]
with open('/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/bindings.log','w') as log:
 for cmd in commands:
  print('RUN:',cmd,flush=True); print('RUN:',cmd,file=log,flush=True)
  result=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
  print('EXIT:',result.returncode,flush=True)
  if result.returncode:
   print(Path(log.name).read_text()[-10000:]);raise SystemExit(result.returncode)
