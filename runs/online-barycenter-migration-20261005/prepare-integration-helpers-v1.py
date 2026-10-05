"""Version bounded auxiliary helpers; preserve every previous package input."""
from pathlib import Path
import ast,hashlib,json
run=Path(__file__).parent;prior=Path('runs/online-expectation-migration-20261005')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]
for source,name in [('verify-history-bindings-v3.py','verify-history-bindings-v1.py'),('verify-registry-v1.py','verify-registry-v1.py'),('browser-v1.py','browser-v1.py'),('check-scoped-diff-v3.py','check-scoped-diff-v1.py'),('commit-owned-v1.py','commit-owned-v1.py')]:
 src=prior/source;dest=run/name;assert not dest.exists()
 text=src.read_text(encoding='utf-8').replace('online-expectation','online-barycenter').replace('ONLINE-EXPECTATION','ONLINE-BARYCENTER').replace('OnlineExpectation','OnlineConvexBarycenter').replace('7c3b241a13b1b43d1efcd08429f33c93b890a981','b2b70fa8cf10095ba681eb1ff3e635c98ca2bc56')
 if name=='verify-history-bindings-v1.py':
  text=text.replace("str(run/'historical-raw-supersession-v1.json')", "'runs/online-expectation-migration-20261005/historical-raw-supersession-v1.json',str(run/'historical-raw-supersession-v1.json')")
  text=text.replace("receipts=[Path(", "receipts=[Path('runs/online-expectation-migration-20261005/final-reader-receipt-v1.json'),Path(",1)
  text=text.replace('history-binding-audit-v2.json','history-binding-audit-v1.json').replace('only_online_expectation_subtree_changed','only_online_barycenter_subtree_changed').replace('selected expectation subtree','selected barycenter subtree')
 if name=='verify-registry-v1.py':text=text.replace('tmp/online-optimality-migration-site-v1','tmp/online-expectation-migration-site-v1').replace('Matched10','Matched3')
 ast.parse(text)
 with dest.open('w',encoding='utf-8',newline='\n') as f:f.write(text)
 rows.append(dict(path=dest.as_posix(),source=src.as_posix(),source_sha256=sha(src),prepared_sha256=sha(dest)))
out=run/'auxiliary-integration-preparation-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(rows=rows,captured_before_execution=True,boundary='New barycenter helpers adapted from exact existing expectation helpers. Prior helpers/receipts untouched; labels/current base/prior snapshot and registry baseline explicitly updated before execution.'),f,indent=2);f.write('\n')
print('Five bounded helpers prepared/hash-bound before execution; no public edits.')
