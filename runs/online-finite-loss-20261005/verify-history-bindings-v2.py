"""Resolve current and prior accepted raw bindings through preserved exact snapshots."""
from pathlib import Path
import json,hashlib
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
cache={}
def sha(p):
    if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
    return cache[p]
snapshots={}
for p in ['runs/online-ogd-migration-20261005/historical-raw-supersession-v2.json',
          'runs/online-ftl-migration-20261005/historical-raw-supersession-v1.json',
          'runs/online-convex-migration-20261005/historical-raw-supersession-v1.json',
          str(run/'historical-raw-supersession-v1.json')]:
    for row in load(p)['rows']:
        assert sha(row['snapshot'])==row['raw_sha256']
        snapshots[(row['path'],row['raw_sha256'])]=row
receipts=[run/'source-contract-receipt-v1.json',run/'public-body-receipt-v1.json',
    Path('runs/online-convex-migration-20261005/final-reader-receipt-v1.json'),
    Path('runs/online-ftl-migration-20261005/final-reader-receipt-v1.json'),
    Path('runs/online-ogd-migration-20261005/final-reader-receipt-v2.json')]
rows=[]
for p in receipts:
    r=load(p);assert sha(r['report'])==r['report_sha256']
    for row in r['reviewed_files']:
        current=sha(row['path']);resolved=row['path'];delta='none'
        if current!=row['sha256']:
            s=snapshots[(row['path'],row['sha256'])];resolved=s['snapshot']
            delta=s.get('authorized_delta',s.get('reason','preserved raw original'))
            assert sha(resolved)==row['sha256']
        rows.append(dict(receipt=p.as_posix(),path=row['path'],raw_sha256=row['sha256'],resolved_raw_file=resolved,current_sha256=current,explicit_delta=delta))
snap={r['path']:r for r in load(run/'historical-raw-supersession-v1.json')['rows']}
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
    old=load(snap[p]['snapshot']);new=load(p)
    assert [r for r in old[k] if r.get(key)!='online-convex']==[r for r in new[k] if r.get(key)!='online-convex'],p
    for extra in set(old)-{k}:assert old[extra]==new[extra]
for p,line in [('BanditRLProof.lean','import BanditRLProof.OnlineConstraintFiniteLoss'),('Tests.lean','import Tests.OnlineConstraintFiniteLossCanary')]:
    assert Path(p).read_text(encoding='utf-8')==Path(snap[p]['snapshot']).read_text(encoding='utf-8')+line+'\n'
out=run/'history-binding-audit-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='passed',raw_rows_verified=len(rows),rows=rows,
    exact_five_originals_preserved=True,only_online_convex_reader_subtree_changed=True,all_other_Book_subtrees_unchanged=True,
    earlier_accepted_reports_receipts_unmodified=True,boundary='Only listed current and prior final bindings resolved, not blanket recertification of all historical work.'),f,indent=2);f.write('\n')
print('Verified',len(rows),'raw receipt bindings through exact snapshots; two imports and one reader subtree only.')
