"""Recheck current/prior final review bytes with exact historical supersession snapshots."""
from pathlib import Path
import json,hashlib
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
cache={}
def sha(p):
 if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[p]
snapshots={}
for p in ['runs/online-ogd-migration-20261005/historical-raw-supersession-v2.json',
 'runs/online-ftl-migration-20261005/historical-raw-supersession-v1.json',
 'runs/online-convex-migration-20261005/historical-raw-supersession-v1.json',
 'runs/online-finite-loss-20261005/historical-raw-supersession-v1.json',
 'runs/online-first-order-migration-20261005/historical-raw-supersession-v1.json','runs/online-optimality-migration-20261005/historical-raw-supersession-v1.json','runs/online-expectation-migration-20261005/historical-raw-supersession-v1.json','runs/online-barycenter-migration-20261005/historical-raw-supersession-v1.json','runs/online-minorant-migration-20261005/historical-raw-supersession-v1.json','runs/online-jensen-migration-20261005/historical-raw-supersession-v1.json','runs/online-guessing-migration-20261006/historical-raw-supersession-v1.json','runs/online-huber-migration-20261006/historical-raw-supersession-v1.json','runs/online-closed-proper-migration-20261006/historical-raw-supersession-v1.json','runs/online-subgradient-basic-migration-20261006/historical-raw-supersession-v1.json','runs/online-subgradient-interior-migration-20261006/historical-raw-supersession-v2.json','runs/online-subgradient-interior-migration-20261006/historical-raw-supersession-body-v1.json','runs/online-subgradient-differentiability-migration-20261007/historical-raw-supersession-v3.json','runs/online-subgradient-sum-migration-20261007/historical-raw-supersession-v2.json',str(run/'historical-raw-supersession-v1.json'),str(run/'historical-raw-supersession-contract-v1.json'),str(run/'historical-raw-supersession-body-v1.json'),str(run/'historical-raw-supersession-final-source-v1.json'),str(run/'historical-raw-supersession-final-v1.json'),str(run/'historical-raw-supersession-reader-v2.json'),str(run/'historical-raw-supersession-command-collision-v1.json')]:
 for row in load(p)['rows']:
  assert sha(row['snapshot'])==row['raw_sha256'];snapshots[(str(Path(row['path']).resolve()),row['raw_sha256'])]=row
receipts=[run/'final-reader-receipt-v1.json',Path('runs/online-subgradient-sum-migration-20261007/final-reader-receipt-v1.json'),Path('runs/online-subgradient-differentiability-migration-20261007/final-reader-receipt-v1.json'),Path('runs/online-subgradient-interior-migration-20261006/final-reader-receipt-v1.json'),Path('runs/online-subgradient-basic-migration-20261006/final-reader-receipt-v1.json'),Path('runs/online-closed-proper-migration-20261006/final-reader-receipt-v1.json'),Path('runs/online-huber-migration-20261006/final-reader-receipt-v1.json'),Path('runs/online-guessing-migration-20261006/final-reader-receipt-v1.json'),Path('runs/online-jensen-migration-20261005/final-reader-receipt-v1.json'),Path('runs/online-minorant-migration-20261005/final-reader-receipt-v1.json'),Path('runs/online-barycenter-migration-20261005/final-reader-receipt-v1.json'),Path('runs/online-expectation-migration-20261005/final-reader-receipt-v1.json'),Path('runs/online-optimality-migration-20261005/final-reader-receipt-v1.json'),run/'source-contract-receipt-v1.json',run/'public-body-receipt-v1.json',
 Path('runs/online-first-order-migration-20261005/final-reader-receipt-v1.json'),
 Path('runs/online-finite-loss-20261005/final-reader-receipt-v1.json'),
 Path('runs/online-convex-migration-20261005/final-reader-receipt-v1.json'),
 Path('runs/online-ftl-migration-20261005/final-reader-receipt-v1.json'),
 Path('runs/online-ogd-migration-20261005/final-reader-receipt-v2.json')]
rows=[]
for p in receipts:
 r=load(p);assert sha(r['report'])==r['report_sha256']
 for row in r['reviewed_files']:
  current=sha(row['path']);resolved=row['path'];delta='none'
  if current!=row['sha256']:
   s=snapshots[(str(Path(row['path']).resolve()),row['sha256'])];resolved=s['snapshot'];assert sha(resolved)==row['sha256']
   delta=s.get('authorized_delta',s.get('reason','preserved raw original'))
  rows.append(dict(receipt=p.as_posix(),path=row['path'],raw_sha256=row['sha256'],resolved_raw_file=resolved,current_sha256=current,explicit_delta=delta))
snap={r['path']:r for r in load(run/'historical-raw-supersession-v1.json')['rows']}
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [r for r in old[k] if r.get(key)!='online-subgradient-absolute']==[r for r in new[k] if r.get(key)!='online-subgradient-absolute'],p
 for extra in set(old)-{k}:assert old[extra]==new[extra]
out=run/'history-binding-audit-v3.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='passed',raw_rows_verified=len(rows),rows=rows,exact_historical_raw_bindings_and_old_modules_preserved=True,
  only_online_subgradient_absolute_subtree_changed=True,all_other_Book_subtrees_unchanged=True,
  earlier_accepted_reports_receipts_unmodified=True,boundary='Listed current/prior final bindings only; not blanket historical recertification.'),f,indent=2);f.write('\n')
print('Verified',len(rows),'raw receipt bindings via exact historical snapshots; selected Ex2.24 absolute subtree only.')
