"""Actual bounded diff and positive preservation of older mathematics and Book surfaces."""
from common_v2 import *
fixed(True,True)
owned=load(RUN/'owned-commit-paths-v1.json')
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
for p,line in [('BanditRLProof.lean','import BanditRLProof.OnlineConvexUncountability'),('Tests.lean','import Tests.OnlineConvexUncountabilityCanary')]:
 old=(RUN/'snapshots'/('before-'+p+'.txt')).read_bytes();new=Path(p).read_bytes()
 assert new==old+(b'' if old.endswith(b'\n') else b'\n')+line.encode()+b'\n',p
checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('chapter')==ROUTE),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 old=load(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt'));new=load(p)
 assert [x for x in old[key] if not pred(x)]==[x for x in new[key] if not pred(x)],p
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in new.items() if k!=key},p
 checks.append(dict(path=p,other_Book_subtrees_unchanged=True))
 if key=='readings':
  a=next(x for x in old[key] if pred(x));b=next(x for x in new[key] if pred(x))
  assert b['source_theorems'][:3]==a['source_theorems'] and b['notation']==a['notation']
  assert b['proof_bridge']['steps'][:-1]==a['proof_bridge']['steps'][:-1]
  oldlast=a['proof_bridge']['steps'][-1];newlast=b['proof_bridge']['steps'][-1]
  assert {k:v for k,v in oldlast.items() if k!='detail'}=={k:v for k,v in newlast.items() if k!='detail'}
  assert newlast['detail'].startswith(oldlast['detail'])
 if key=='highlights':assert [x for x in new[key] if pred(x)][:3]==[x for x in old[key] if pred(x)]
for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']:
 snapshot=RUN/'snapshots'/('contract-reviewed-'+p.replace('/','--')+'.txt')
 assert Path(p).read_bytes().startswith(snapshot.read_bytes()),p
write(RUN/'source-scope-audit-v3.json',dict(status='passed',exact_base=BASE,changed_paths=paths,all_changed_paths_owned=True,shared_root_and_Tests_exact_additive_imports=True,old_math_and_pins_unchanged=True,global_SGB_unchanged=True,old_contracts_and_runs_not_modified=True,three_old_sourcecards_highlights_and_notation_preserved=True,all_five_old_bridge_steps_explanations_preserved=True,Book_surface_checks=checks,actual_native_journal_raw_prefixes_preserved=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual owned diff/older math/old contracts and runs/other Books/sourcecards/notes/additive rootTests/native rawprefixes preserved.')
