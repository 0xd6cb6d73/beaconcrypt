import os,subprocess
from pathlib import Path
os.chdir('/home/user/worktrees/beaconcrypt-row-persistence')
os.environ['PATH']=':'.join(['/tmp/bc-arc-scratch/row-persistence-20261025','/home/user/.rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin','/home/user/.cargo/bin','/nix/store/9wyldz5qids294k9h5qcg1f72i52jidi-gnumake-4.4.1/bin',os.environ['PATH']])
os.environ.update(RUSTFLAGS='-C linker-features=-lld', CARGO_PROFILE_TEST_OPT_LEVEL='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_BUILD_JOBS='1', RUST_TEST_THREADS='1')
import hashlib,json,datetime
root=Path.cwd()
paths=[p for folder in [root/'beaconcrypt/src',root/'beaconcrypt-core/src',root/'beaconcrypt-parse/src',root/'beaconcrypt/examples/persistence_bench'] for p in folder.rglob('*') if p.is_file()]
paths += [root/'Cargo.toml',root/'Cargo.lock',root/'beaconcrypt/Cargo.toml',root/'beaconcrypt/build.rs',root/'beaconcrypt-core/Cargo.toml',root/'beaconcrypt-parse/Cargo.toml',root/'beaconcrypt-wasm/Cargo.toml']
hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
command=['cargo','build','--locked','--release','-p','beaconcrypt','--example','persistence_bench']
started=datetime.datetime.now(datetime.UTC).isoformat()
logpath=Path('/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/release-build.log')
with logpath.open('w') as log:
 print('RUN',command,flush=True)
 code=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT).returncode
 print('EXIT',code,flush=True)
if code:print(logpath.read_text()[-10000:]);raise SystemExit(code)
for name,digest in hashes.items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
binary=root/'target/release/examples/persistence_bench'
receipt={'started':started,'finished':datetime.datetime.now(datetime.UTC).isoformat(),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'source_dirty_at_build':subprocess.check_output(['git','status','--short'],text=True),'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'source_sha256':hashes,'command':command,'rustc':subprocess.check_output(['rustc','-vV'],text=True),'environment':{k:os.environ.get(k) for k in ['PATH','RUSTFLAGS','CARGO_BUILD_JOBS']},'log_sha256':hashlib.sha256(logpath.read_bytes()).hexdigest()}
Path('/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/release-build-provisional.json').write_text(json.dumps(receipt,indent=2)+'\n')
