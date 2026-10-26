import gzip,json,shutil,tarfile
from pathlib import Path
R=Path('/tmp/bc-arc-scratch/row-persistence-20261025/concurrent')
O=Path('/home/user/worktrees/beaconcrypt-concurrent-persistence/doc/impl/concurrent-row-persistence-results/2026-10-25')
O.mkdir(parents=True,exist_ok=False)
(O/'collections').mkdir()

def pack(destination,base,files):
    with destination.open('xb') as raw, gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=6) as gz, tarfile.open(fileobj=gz,mode='w|') as tar:
        for p in sorted(set(files)):
            if p.is_file() and not p.is_symlink():
                tar.add(p,arcname=str(p.relative_to(base)),recursive=False)
    print(destination.name,destination.stat().st_size,flush=True)

for name in ('collection-20261025','collection-sqlite-wait-v2','collection-postgres-final'):
    c=R/name
    pack(O/'collections'/f'{name}-metadata.tar.gz',R,[p for p in c.iterdir() if p.is_file()])
    for axis in sorted(c.glob('axis-*')):
        if axis.is_dir():
            files=[p for p in axis.rglob('*') if 'fixtures' not in p.parts and '__pycache__' not in p.parts]
            pack(O/'collections'/f'{name}-{axis.name}.tar.gz',R,files)

shutil.copytree(R/'completed-audit-archives',O/'correctness')
patterns=['validation-receipt-*','build-receipt-final-v1.json','build-receipt-sqlite-wait-v2.json','build-release-final-v1.py','build-release-sqlite-wait-v2.py','release-build-final-v1.log','release-build-sqlite-wait-v2.log','validation-freeze-v1-*','validation-owner-label-*','validation-pinned-restart-*','pinned-restart-receipt.json','sqlite-wait-validation.log','final-library-source-comparison.json','analysis-helper-final-receipt.json','analysis-helper-independent-review.json','analysis-helper-synthetic-final.log','final-collection-review.json','source_hashes.py']
files=[p for pattern in patterns for p in R.glob(pattern) if p.is_file()]
files.append(R/'wasm-audit/validation-receipt.json')
pack(O/'correctness/validation.tar.gz',R,files)
A=Path('/tmp/bc-arc-scratch/concurrent-persistence-example-audit-20261025')
files=[]
for name in ('final-01','final-02'):
    d=A/name
    files.extend(p for p in d.iterdir() if p.is_file())
    files.extend((d/'results').rglob('*'))
pack(O/'correctness/benchmark-mutation-diagnostic-and-stopped-run.tar.gz',A,files)
shutil.copy2(R/'analyze-results.py',O/'analyze-results.py')
shutil.copy2(Path(__file__),O/'archive-final-evidence.py')
(O.parent/'.gitattributes').write_text('** -text whitespace=cr-at-eol,-blank-at-eof\n')
(O/'archive-exclusions.json').write_text(json.dumps({'excluded':['generated database fixture directories','Python bytecode caches','database data directories','compiled executables and build targets','audit source checkouts (Git revisions and source manifests are preserved)'],'note':'All materialized collection attempts, including failures and discarded attempts, are archived. SQLite1000 is excluded from primary analysis at the user request. Supplementary harness mutation work was stopped, not passed.'},indent=2)+'\n')
