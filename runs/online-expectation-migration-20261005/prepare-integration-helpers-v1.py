"""Version auxiliary helpers without altering any already bound input."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;prior=Path('runs/online-optimality-migration-20261005')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]
for original,name in [('verify-history-bindings-v1.py','verify-history-bindings-v1.py'),('verify-registry-v1.py','verify-registry-v1.py'),('browser-v1.py','browser-v1.py'),('check-scoped-diff-v1.py','check-scoped-diff-v2.py')]:
 src=prior/original;dest=run/name;assert not dest.exists()
 text=src.read_text(encoding='utf-8').replace('online-optimality','online-expectation').replace('c9b47c8ba79a234d0dfa6e8ef5643a43677dd33a','7c3b241a13b1b43d1efcd08429f33c93b890a981')
 if name=='verify-history-bindings-v1.py':
  text=text.replace("str(run/'historical-raw-supersession-v1.json')", "'runs/online-optimality-migration-20261005/historical-raw-supersession-v1.json',str(run/'historical-raw-supersession-v1.json')")
  text=text.replace("receipts=[run/'source-contract-receipt-v1.json'", "receipts=[Path('runs/online-optimality-migration-20261005/final-reader-receipt-v1.json'),run/'source-contract-receipt-v1.json'")
 if name=='verify-registry-v1.py':
  text=text.replace('tmp/online-first-order-migration-site-v1','tmp/online-optimality-migration-site-v1').replace('Matched4','Matched10')
 if name=='check-scoped-diff-v2.py':text=text.replace('source-printed10-11-pdf22-23.txt','source-printed11-pdf23.txt')
 with dest.open('w',encoding='utf-8',newline='\n') as handle:handle.write(text)
 rows.append(dict(path=dest.as_posix(),source=src.as_posix(),source_sha256=sha(src),prepared_sha256=sha(dest)))
out=run/'auxiliary-integration-preparation-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as handle:
 json.dump(dict(rows=rows,boundary='New/versioned workflow helpers only, before execution. Existing frozen helpers untouched. Scoped diff v2 corrects actual PDF-extraction filename; v1 was not executed or overwritten.'),handle,indent=2);handle.write('\n')
print('Prepared four auxiliary helpers with immutable source/prepared raw hashes.')
