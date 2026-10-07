from common_v1 import *

ROUTE='online-foundations'
TEST='GuessingLogLowerProbe.'
MANIFEST=Path('research-wiki/contribution-contracts/online-guessing-log-lower-20261008.json')
ALLOWED_INTEGRATION={'BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json'}
def original(p):
 return load(RUN/'snapshots'/(p.replace('/','--')+'.raw'))
def fixed_integrated():
 assert sha(PDF)==PDF_SHA
 for p,h in load(RUN/'draft-freeze-v1.json')['fixed_files'].items():
  if p not in ALLOWED_INTEGRATION:assert sha(p)==h,p
 b=load(RUN/'body-bindings-v1.json')
 assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
 for p,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingLogLower\n'),('Tests.lean',b'\nimport Tests.OnlineGuessingLogLowerCanary\n')]:
  assert Path(p).read_bytes()==(RUN/'snapshots'/(p+'.raw')).read_bytes()+addition,p
 old=original('website/content/readings.json');new=load('website/content/readings.json')
 for before,after in zip(old['readings'],new['readings']):
  if before['slug']!=ROUTE:assert before==after
  else:
   assert len(before['source_theorems'])==8 and len(after['source_theorems'])==9
   assert after['source_theorems'][:8]==before['source_theorems']
   assert {k:v for k,v in after.items() if k!='source_theorems'}=={k:v for k,v in before.items() if k!='source_theorems'}
 assert len(old['readings'])==len(new['readings'])
 old=original('website/content/highlights.json');new=load('website/content/highlights.json')
 assert new['highlights'][:len(old['highlights'])]==old['highlights']
 assert {k:v for k,v in new.items() if k!='highlights'}=={k:v for k,v in old.items() if k!='highlights'}
 assert all(x['full_name'].startswith(PRE) and not x['featured'] for x in new['highlights'][len(old['highlights']):])
 old=original('website/content/chapters.json');new=load('website/content/chapters.json')
 assert len(old['chapters'])==len(new['chapters'])
 for before,after in zip(old['chapters'],new['chapters']):
  if before['slug']!=ROUTE:assert before==after
  else:
   assert after['module_globs']==before['module_globs']+[PUBLIC.as_posix()]
   keys={'completion_blockers','open_gaps','module_globs'}
   assert {k:v for k,v in before.items() if k not in keys}=={k:v for k,v in after.items() if k not in keys}
