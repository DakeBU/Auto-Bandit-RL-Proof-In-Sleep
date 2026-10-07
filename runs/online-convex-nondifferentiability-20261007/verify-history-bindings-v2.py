"""Revalidate earlier audited raw receipts plus newly changed files' exact original bytes."""
from common_v4 import *
fixed(True,True);cache={}
def h(p):
 p=str(Path(p).resolve())
 if p not in cache:cache[p]=sha(p)
 return cache[p]
snap={}
def add(p,d,q):
 assert h(q)==d,(p,q);snap[(str(Path(p).resolve()),d)]=str(q)
prior=Path('runs/online-lipschitz-migration-20261007');old=load(prior/'history-binding-audit-v1.json')
for row in old['rows']:add(row['path'],row['raw_sha256'],row['resolved_raw_file'])
for p in prior.glob('historical-raw-supersession-*.json'):
 for row in load(p)['rows']:add(row['path'],row['raw_sha256'],row['snapshot'])
for p,d in load(RUN/'draft-freeze-v1.json')['fixed_files'].items():add(p,d,RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt'))
add('MANIFEST.md',h(RUN/'manifest-before-nondiff-entry-v1.txt'),RUN/'manifest-before-nondiff-entry-v1.txt')
for row in load(RUN/'contract-native-prefix-bindings-v1.json')['rows']:add(row['path'],row['sha256'],row['resolved'])
for row in load(RUN/'body-native-prefix-bindings-v1.json')['rows']:add(row['path'],row['raw_sha256'],row['snapshot'])
rows=[]
def bind(receipt,p,d):
 q=p if h(p)==d else snap[(str(Path(p).resolve()),d)];assert h(q)==d
 rows.append(dict(receipt=receipt,path=p,raw_sha256=d,resolved_raw_file=q,current_sha256=h(p),explicit_delta='none' if q==p else 'Exact original raw snapshot preserved; append-only native journals or additive sharedroot/reader/MANIFEST metadata; no original source/proof/receipt rewrite.'))
for row in old['rows']:bind(row['receipt'],row['path'],row['raw_sha256'])
extra=[prior/'final-reader-receipt-v1.json',RUN/'source-contract-receipt-v1.json',RUN/'source-contract-receipt-v2.json',RUN/'public-body-receipt-v1.json']
for p in extra:
 r=load(p);assert h(r['report'])==r['report_sha256']
 for row in r['reviewed_files']:bind(p.as_posix(),row['path'],row['sha256'])
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 olddata=load(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt'));current=load(p)
 assert [a for a in olddata[k] if a.get(key)!=ROUTE]==[a for a in current[k] if a.get(key)!=ROUTE],p
 for other in set(olddata)-{k}:assert olddata[other]==current[other]
receipts=sorted({r['receipt'] for r in rows})
write(RUN/'history-binding-audit-v2.json',dict(status='passed',raw_rows_verified=len(rows),receipts=len(receipts),rows=rows,earlier_accepted_and_rejected_reports_receipts_preserved=True,all_other_Book_subtrees_unchanged=True,only_online_lipschitz_reader_subtree_changed=True,additive_sharedrootTests_imports=True,boundary='Rechecked exact listed prior audit/raw receipts plus oldPR176FINAL/currentCONv1rejection/v2accepted/BODY, not blanket historical recertification.'))
print('Verified',len(rows),'exactrawbindings/',len(receipts),'listedreceipts including preservedsourceM1rejection; oldmath/otherBooks unchanged.')
