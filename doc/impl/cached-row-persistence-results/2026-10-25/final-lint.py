import os,subprocess
from pathlib import Path
os.chdir('/home/user/worktrees/beaconcrypt-row-persistence')
os.environ['PATH']=':'.join(['/tmp/bc-arc-scratch/row-persistence-20261025','/home/user/.rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin','/home/user/.cargo/bin','/nix/store/9wyldz5qids294k9h5qcg1f72i52jidi-gnumake-4.4.1/bin',os.environ['PATH']])
os.environ.update(RUSTFLAGS='-C linker-features=-lld', CARGO_PROFILE_TEST_OPT_LEVEL='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='1', RUST_TEST_THREADS='1')
commands=[['cargo','fmt','--all','--check'],['cargo','clippy','--workspace','--all-targets','--all-features','--locked']]
with open('/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/final-lint.log','w') as log:
 for cmd in commands:
  print('RUN',cmd,flush=True);print('RUN',cmd,file=log,flush=True)
  status=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT).returncode
  print('EXIT',status,flush=True);print('EXIT',status,file=log,flush=True)
  if status:raise SystemExit(status)
