from common_reviewed_v1 import *
ROUTE='online-foundations';PRE='BanditRL.OnlineLearning.';TEST='NoRegretSemanticsProbe.'
MANIFEST=Path('research-wiki/contribution-contracts/online-no-regret-20261008.json')
ALLOWED_INTEGRATION={'BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json'}
OWN_METADATA={folder+'/'+TASK+'.md' for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']}
def original(p):return load(RUN/'snapshots'/(p.replace('/','--')+'.raw'))
def body_fixed():
 reviewed_fixed()
 b=load(RUN/'body-bindings-v1.json');assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
 r=load(RUN/'public-body-receipt-v1.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta'
 assert sha(r['report'])==r['report_sha256']
 assert r['required_reader_corrections']==load(RUN/'stabilized-contract-v1.json')['original_reader_requirements']
 assert all(not r[k] for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs'])
 reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
 inputs=load(RUN/'body-review-inputs-v1.json');assert r['fixed_input_count']==inputs['fixed_input_count']==371
 for row in inputs['rows']:
  p=Path(row['path']);h=row['sha256'];assert reviewed[row['path']]==h
  if sha(p)!=h:
   local=p.resolve().relative_to(ROOT).as_posix()
   if local in ALLOWED_INTEGRATION:p=RUN/'snapshots'/(local.replace('/','--')+'.raw')
   elif local in OWN_METADATA:p=RUN/'snapshots'/('BODY-review-'+local.replace('/','--')+'.raw')
   else:raise AssertionError(row['path'])
  assert sha(p)==h,row['path']
def fixed_integrated():
 body_fixed()
 for p,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineNoRegretSemantics\n'),('Tests.lean',b'\nimport Tests.OnlineNoRegretSemanticsCanary\n')]:
  assert Path(p).read_bytes()==(RUN/'snapshots'/(p+'.raw')).read_bytes()+addition,p
 old=original('website/content/readings.json');new=load('website/content/readings.json')
 assert len(old['readings'])==len(new['readings'])
 for before,after in zip(old['readings'],new['readings']):
  if before['slug']!=ROUTE:assert before==after
  else:
   assert len(before['source_theorems'])==9 and len(after['source_theorems'])==10
   assert after['source_theorems'][:9]==before['source_theorems']
   assert {k:v for k,v in after.items() if k!='source_theorems'}=={k:v for k,v in before.items() if k!='source_theorems'}
 old=original('website/content/highlights.json');new=load('website/content/highlights.json')
 assert new['highlights'][:len(old['highlights'])]==old['highlights']
 assert {k:v for k,v in new.items() if k!='highlights'}=={k:v for k,v in old.items() if k!='highlights'}
 added=new['highlights'][len(old['highlights']):];assert len(added)==6
 assert all(x['full_name'].startswith(PRE) and not x['featured'] for x in added)
 old=original('website/content/chapters.json');new=load('website/content/chapters.json')
 assert len(old['chapters'])==len(new['chapters'])
 for before,after in zip(old['chapters'],new['chapters']):
  if before['slug']!=ROUTE:assert before==after
  else:
   assert after['module_globs']==before['module_globs']+[PUBLIC.as_posix()]
   keys={'completion_blockers','open_gaps','module_globs'}
   assert {k:v for k,v in before.items() if k not in keys}=={k:v for k,v in after.items() if k not in keys}
