"""Prepare narrowly versioned workflow helpers without changing production or old evidence."""
from pathlib import Path
import ast,hashlib,json
run=Path(__file__).parent;prior=Path('runs/online-minorant-migration-20261005')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rows=[]
for name in ['verify-history-bindings-v1.py','verify-registry-v1.py','browser-v1.py','check-scoped-diff-v1.py','commit-owned-v1.py']:
 src=prior/name;dest=run/name;assert not dest.exists()
 text=src.read_text(encoding='utf-8').replace('online-minorant','online-jensen').replace('ONLINE-MINORANT','ONLINE-JENSEN').replace('OnlineConvexMinorant','OnlineJensen').replace('f68646457a12de93ee6cb8d585a4162f9f0a112c','2b4586db952b0e4ed0b7630f2d471c75a9af0f74')
 if name=='verify-history-bindings-v1.py':
  text=text.replace("str(run/'historical-raw-supersession-v1.json')", "'runs/online-minorant-migration-20261005/historical-raw-supersession-v1.json',str(run/'historical-raw-supersession-v1.json')")
  text=text.replace('receipts=[Path(',"receipts=[Path('runs/online-minorant-migration-20261005/final-reader-receipt-v1.json'),Path(",1)
  text=text.replace('only_online_minorant_subtree_changed','only_online_jensen_subtree_changed').replace('selected minorant subtree','selected Jensen subtree')
 if name=='verify-registry-v1.py':text=text.replace('tmp/online-barycenter-migration-site-v1','tmp/online-minorant-migration-site-v1').replace('Matched4','Matched2')
 ast.parse(text)
 with dest.open('w',encoding='utf-8',newline='\n') as f:f.write(text)
 rows.append(dict(path=dest.as_posix(),source=src.as_posix(),source_sha256=sha(src),prepared_sha256=sha(dest)))
out=run/'auxiliary-integration-preparation-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(rows=rows,captured_before_execution=True,boundary='New Jensen task helpers with exact PR162 base, selected online-jensen route, extended raw snapshot/final receipt chain and prior minorant registry baseline. Old helpers/receipts unchanged.'),f,indent=2);f.write('\n')
print('Five Jensen workflow helpers prepared/hash-bound before use; no reader edits.')
