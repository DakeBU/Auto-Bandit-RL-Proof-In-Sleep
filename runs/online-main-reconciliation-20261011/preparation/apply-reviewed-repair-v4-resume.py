from pathlib import Path
import json,subprocess,hashlib,datetime
r=Path.cwd();prep=r/'tmp/online-main-reconciliation-20261011';out=r/'runs/online-main-reconciliation-20261011';old='a5ec0ba8198d6b93505b953d1f63d6d5cb63f065'
assert subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()==old
dirty=subprocess.check_output(['git','diff','--name-only']).decode().splitlines()
assert set(dirty)=={'tools/check_contributor_contract.py','tools/test_contributor_contract.py'}
for rel,sha in [('tools/check_contributor_contract.py','35f98edff8c77d3c9ecf365d14fe12f5a4851f36a4331c28a6c00b65526198a7'),('tools/test_contributor_contract.py','4a592338a2ee90d77845991329e85ee7bda96c6bd5ad6c2d4e8ca3a29bb5f5fe')]: assert hashlib.sha256((r/rel).read_bytes()).hexdigest()==sha
for label in ['production-root-v1','shared-Tests-v1']:
    gate=json.loads((r/'tmp/online-main-reconciliation-gates-20261011'/label/'receipt.json').read_bytes());assert gate['actual_exit']==0 and gate['capture_integrity_ok']
checks=[(r/'tmp/online-main-reconciliation-checker-review-20261011/independent-review-v1.json','97d2e2d943f841def923da1cbadad4dfdeb813d5e42a0af682a4aa9f72c688ac'),(r/'tmp/online-main-reconciliation-audit-20261011/book-scope-wording-review-v2.json','a3e2a2471de5eee6225d1ab221866ef9c2404ef2434a719b2b4a3142ffc86598')]
for p,sha in checks:assert hashlib.sha256(p.read_bytes()).hexdigest()==sha
applied=[]
for rel,sha in [('tools/check_contributor_contract.py','35f98edff8c77d3c9ecf365d14fe12f5a4851f36a4331c28a6c00b65526198a7'),('tools/test_contributor_contract.py','4a592338a2ee90d77845991329e85ee7bda96c6bd5ad6c2d4e8ca3a29bb5f5fe'),('docs/contributor-codex-contract.md','48dd398da87a267bd82b2f20b3ab6db99909f3ebfbccd75502ecfb65aa49b993')]:
    b=(prep/'contributor-checker-candidate-v1'/rel).read_bytes();assert hashlib.sha256(b).hexdigest()==sha
    (r/rel).write_bytes(b);applied.append({'path':rel,'sha256':sha})
b=(prep/'book-scope-wording-repair-v2/chapters.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='84742df6b2a44b1d1bd58c46a42de2be28fd8e4b9f3e8c5704d31b8cb40f25d3';(r/'website/content/chapters.json').write_bytes(b);applied.append({'path':'website/content/chapters.json','sha256':hashlib.sha256(b).hexdigest()})
p=r/'research-wiki/contribution-contracts/CONTRIBUTOR-HISTORICAL-ROWS-20261011.json';assert not p.exists();p.write_bytes((prep/'metadata/CONTRIBUTOR-HISTORICAL-ROWS-20261011.draft-v2.json').read_bytes())
doc=r/'docs/contracts/online-main-reconciliation-v1';assert not doc.exists();doc.mkdir()
for p in (prep/'maintenance-doc-proposal-v1').iterdir():doc.joinpath(p.name).write_bytes(p.read_bytes())
rows=[]
for srcroot,sub in [(prep,'preparation'),(r/'tmp/online-main-reconciliation-audit-20261011','independent-preparation-audit'),(r/'tmp/online-main-reconciliation-checker-review-20261011','independent-checker-audit'),(r/'tmp/online-main-reconciliation-commit-20261011','first-candidate-commit')]:
    for src in sorted(srcroot.rglob('*')):
        if not src.is_file():continue
        b=src.read_bytes();dst=out/sub/src.relative_to(srcroot)
        if dst.exists():assert dst.read_bytes()==b,str(dst);continue
        dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b);rows.append({'from':src.relative_to(r).as_posix(),'to':dst.relative_to(r).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'old_head':old,'scope':'Reviewed wording and fail-closed tooling repair only; fresh gates pending; no new mathematics or chapter closure','applied':applied,'new_archival_rows':rows,'old_records_byte_unchanged':True};out.joinpath('reviewed-repair-application-v2.json').write_bytes((json.dumps(row,indent=2)+'\n').encode())
print(json.dumps({'applied':applied,'new_archival_rows':len(rows),'new_archival_bytes':sum(x['bytes'] for x in rows),'status':'applied not committed/gated'},indent=2))
