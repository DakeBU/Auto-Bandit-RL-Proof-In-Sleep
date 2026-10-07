from common_integrated_v1 import *

def review_resolve(p,h):
 path=Path(p)
 if sha(path)==h:return path
 local=path.resolve().relative_to(ROOT).as_posix()
 assert local in ALLOWED_INTEGRATION,local
 snapshot=RUN/'snapshots'/(local.replace('/','--')+'.raw')
 assert sha(snapshot)==h,p
 return snapshot
def validate_reviews():
 audits=[]
 for receipt,inputs in [('source-contract-receipt-v1.json','source-contract-inputs-v2.json'),('public-body-receipt-v1.json','body-review-inputs-v1.json'),('final-reader-receipt-v1.json','final-reader-inputs-v1.json')]:
  r=load(RUN/receipt);assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
  assert sha(r['report'])==r['report_sha256']
  reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
  for row in load(RUN/inputs)['rows']:
   p=review_resolve(row['path'],row['sha256']);assert sha(p)==row['sha256']==reviewed[row['path']],row['path']
  for p,h in reviewed.items():assert sha(review_resolve(p,h))==h,p
  audits.append(dict(receipt=receipt,receipt_sha256=sha(RUN/receipt),fixed_rows=len(load(RUN/inputs)['rows']),all_raw_bindings_match=True))
 return audits
def accepted_fixed():
 fixed_integrated();validate_reviews()
 for p in ['BanditRLProof.lean','Tests.lean',PUBLIC.as_posix(),CANARY.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
  rows=load(RUN/'final-reader-inputs-v1.json')['rows'];expected=next(x['sha256'] for x in rows if Path(x['path']).resolve()==Path(p).resolve())
  assert sha(p)==expected,p
