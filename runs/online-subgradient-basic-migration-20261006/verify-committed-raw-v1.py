"""Check exact current-run committed bytes separately from local semantic receipt checks."""
from pathlib import Path
import hashlib,json,subprocess
run=Path(__file__).parent
rows=[]
for p in sorted(run.rglob('*')):
 if not p.is_file():continue
 rel=p.as_posix()
 child=subprocess.run(['git','show','HEAD:'+rel],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if child.returncode:raise AssertionError('Owned evidence not committed: '+rel)
 raw=p.read_bytes();assert child.stdout==raw,rel
 rows.append(dict(path=rel,sha256=hashlib.sha256(raw).hexdigest(),committed_equals_local_raw=True))
out=run/'committed-raw-audit-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='passed',commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip(),checked_files=len(rows),rows=rows,current_run_raw_bytes_retained_by='run-local .gitattributes * -text',boundary='Only this run committed raw bytes checked. Earlier directories unchanged; earlier receipts resolved against actual local raw snapshots. No blanket cross-platform recertification or clean rebuild claim.'),f,indent=2);f.write('\n')
print('Exact current-run committed raw bytes match',len(rows),'evidence files.')
