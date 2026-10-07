"""Positive preservation of existing proofs, roots, links, contracts and other Books."""
from common_v2 import *
fixed(True);owned=load(RUN/'owned-commit-paths-v1.json');paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('chapter')==ROUTE),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 old=load(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt'));new=load(p)
 assert [x for x in old[key] if not pred(x)]==[x for x in new[key] if not pred(x)],p
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in new.items() if k!=key},p
 checks.append(dict(path=p,all_other_Book_subtrees_unchanged=True))
 if key=='readings':
  a=next(x for x in old[key] if pred(x));b=next(x for x in new[key] if pred(x));assert a['teaching_route']==b['teaching_route'] and a['notation']==b['notation']
  assert [(c['label'],c['url'],c['pdf_page']) for c in a['source_theorems']]==[(c['label'],c['url'],c['pdf_page']) for c in b['source_theorems']]
 if key=='highlights':assert [x['full_name'] for x in old[key] if pred(x)]==[x['full_name'] for x in new[key] if pred(x)]
for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']:
 s=RUN/'snapshots'/('contract-v2-reviewed-'+p.replace('/','--')+'.txt');assert Path(p).read_bytes().startswith(s.read_bytes()),p
write(RUN/'source-scope-audit-v2.json',dict(status='passed',exact_base=BASE,changed_paths=paths,all_changed_paths_owned=True,public_canary_shared_root_Tests_bytes_unchanged=True,old_math_pins_SGB_contracts_unchanged=True,old_runs_unmodified=True,source_links_ids_and_curated_names_unchanged=True,Book_surface_checks=checks,native_journal_raw_prefixes_preserved=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Owned diff/whole public-canary/rootTests/pins/contracts/otherBooks/native prefix preserved.')
