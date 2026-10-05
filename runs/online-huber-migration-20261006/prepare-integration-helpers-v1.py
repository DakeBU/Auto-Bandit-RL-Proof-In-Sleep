"""Prepare bounded Huber workflow helpers; no production or historical edits."""
from pathlib import Path
import ast,hashlib,json
run=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rows=[]
specs=[('runs/online-guessing-migration-20261006/verify-history-bindings-v1.py','verify-history-bindings-v1.py'),('runs/online-jensen-migration-20261005/browser-v1.py','browser-v1.py'),('runs/online-guessing-migration-20261006/check-scoped-diff-v3.py','check-scoped-diff-v1.py'),('runs/online-jensen-migration-20261005/commit-owned-v1.py','commit-owned-v1.py')]
for source,name in specs:
 src=Path(source);dest=run/name;assert not dest.exists(),dest
 text=src.read_text(encoding='utf-8')
 if name=='verify-history-bindings-v1.py':
  needle="str(run/'historical-raw-supersession-v1.json')"
  assert text.count(needle)==1
  text=text.replace(needle,"'runs/online-guessing-migration-20261006/historical-raw-supersession-v1.json',"+needle)
  text=text.replace('receipts=[Path(',"receipts=[Path('runs/online-guessing-migration-20261006/final-reader-receipt-v1.json'),Path(",1)
  text=text.replace("!='online-guessing-ogd'","!='online-huber'").replace('only_online_guessing_subtree_changed','only_online_huber_subtree_changed').replace('selected guessing subtree','selected Huber subtree')
 elif name=='check-scoped-diff-v1.py':
  text=text.replace('25c77a837c849eb78832673063483db5f663a73a','52f628a7ae699887069c5a621d301901718ed772')
  text=text.replace("elif p.endswith('/source-printed15-pdf27.txt') or p.endswith('/source-chapter1-pdf13-19.txt')", "elif p.endswith('/source-printed15-16-pdf27-28.txt')")
 else:
  text=text.replace('online-jensen','online-huber').replace('ONLINE-JENSEN','ONLINE-HUBER').replace('20261005','20261006').replace('OnlineJensen','OnlineHuber')
 ast.parse(text)
 with dest.open('w',encoding='utf-8',newline='\n') as f:f.write(text)
 rows.append(dict(path=dest.as_posix(),source=source,source_sha256=sha(src),prepared_sha256=sha(dest)))
out=run/'auxiliary-integration-preparation-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(rows=rows,captured_before_execution=True,boundary='Current Huber helpers with exact PR164base, selected route, immutable rawhistory chains, CRLF-aware command-scoped whitespace; old helpers unchanged.'),f,indent=2);f.write('\n')
print('Four Huber integration helpers prepared and bound before execution; production unchanged.')
