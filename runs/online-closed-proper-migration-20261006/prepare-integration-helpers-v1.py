"""Prepare exact stacked/history/browser/registry tools before execution."""
from pathlib import Path
import ast,hashlib,json
run=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rows=[]
for name in ['verify-history-bindings-v1.py','browser-v1.py','check-scoped-diff-v1.py','commit-owned-v1.py','verify-registry-v1.py','verify-committed-raw-v1.py']:
 src=Path('runs/online-huber-migration-20261006')/name;text=src.read_text(encoding='utf-8')
 if name=='verify-history-bindings-v1.py':
  needle="str(run/'historical-raw-supersession-v1.json')";assert text.count(needle)==1
  text=text.replace(needle,"'runs/online-huber-migration-20261006/historical-raw-supersession-v1.json',"+needle)
  text=text.replace('receipts=[Path(',"receipts=[Path('runs/online-huber-migration-20261006/final-reader-receipt-v1.json'),Path(",1)
 text=text.replace('online-huber','online-closed-proper').replace('ONLINE-HUBER','ONLINE-CLOSED-PROPER').replace('OnlineHuber','OnlineClosedProper') if name!='verify-history-bindings-v1.py' else text.replace("!='online-huber'","!='online-closed-proper'").replace('only_online_huber_subtree_changed','only_online_closed_proper_subtree_changed').replace('selected Huber subtree','selected closed/proper subtree')
 text=text.replace('52f628a7ae699887069c5a621d301901718ed772','f989706461cb466bc290261f4845f113621e807d').replace('/source-printed15-16-pdf27-28.txt','/source-printed16-pdf28.txt')
 if name=='verify-registry-v1.py':
  text=text.replace('BanditRL.OnlineClosedProper.','BanditRL.OnlineConvex.').replace('tmp/online-guessing-migration-site-v1','tmp/online-huber-migration-site-v1').replace('len(checks)==22','len(checks)==5').replace('nineteen native theorem headers and all three','three native theorem headers and both').replace('Matched19frozen theorem headers/3retained full definitions','Matched3frozen theorem headers/2retained full definitions')
 ast.parse(text);dest=run/name;assert not dest.exists();dest.write_bytes(text.encode('utf-8'))
 rows.append(dict(path=dest.as_posix(),source=src.as_posix(),source_sha256=sha(src),prepared_sha256=sha(dest)))
p=run/'integrate-reader-v1.py';ast.parse(p.read_text(encoding='utf-8'));rows.append(dict(path=p.as_posix(),prepared_sha256=sha(p)))
out=run/'auxiliary-integration-preparation-v1.json';assert not out.exists();out.write_bytes((json.dumps(dict(rows=rows,before_first_use=True,exact_stacked_base='f989706461cb466bc290261f4845f113621e807d',boundary='Current helpers only; old helpers/reports/raw snapshots immutable; command-scoped CRLF-aware whitespace.'),indent=2)+'\n').encode())
print('Seven scoped integration helpers hash-bound before use; production unchanged.')
