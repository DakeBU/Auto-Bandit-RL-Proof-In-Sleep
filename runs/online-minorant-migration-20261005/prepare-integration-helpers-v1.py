"""Version auxiliary workflow helpers for this bounded dependency package."""
from pathlib import Path
import ast,hashlib,json
run=Path(__file__).parent;prior=Path('runs/online-barycenter-migration-20261005')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]
for name in ['verify-history-bindings-v1.py','verify-registry-v1.py','browser-v1.py','check-scoped-diff-v1.py','commit-owned-v1.py']:
 src=prior/name;dest=run/name;assert not dest.exists()
 text=src.read_text(encoding='utf-8').replace('online-barycenter','online-minorant').replace('ONLINE-BARYCENTER','ONLINE-MINORANT').replace('OnlineConvexBarycenter','OnlineConvexMinorant').replace('b2b70fa8cf10095ba681eb1ff3e635c98ca2bc56','f68646457a12de93ee6cb8d585a4162f9f0a112c')
 if name=='verify-history-bindings-v1.py':
  text=text.replace("str(run/'historical-raw-supersession-v1.json')", "'runs/online-barycenter-migration-20261005/historical-raw-supersession-v1.json',str(run/'historical-raw-supersession-v1.json')")
  text=text.replace("receipts=[Path(", "receipts=[Path('runs/online-barycenter-migration-20261005/final-reader-receipt-v1.json'),Path(",1)
  text=text.replace('only_online_barycenter_subtree_changed','only_online_minorant_subtree_changed').replace('selected barycenter subtree','selected minorant subtree')
 if name=='verify-registry-v1.py':text=text.replace('tmp/online-expectation-migration-site-v1','tmp/online-barycenter-migration-site-v1').replace('Matched3','Matched4')
 ast.parse(text)
 with dest.open('w',encoding='utf-8',newline='\n') as f:f.write(text)
 rows.append(dict(path=dest.as_posix(),source=src.as_posix(),source_sha256=sha(src),prepared_sha256=sha(dest)))
out=run/'auxiliary-integration-preparation-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(rows=rows,captured_before_execution=True,boundary='New/versioned minorant helpers; explicit new exact base, selected route, prior snapshot/receipt chain and registry baseline before execution. All old helpers/receipts unchanged.'),f,indent=2);f.write('\n')
print('Five minorant workflow helpers prepared/hash-bound before use; no public reader edits.')
