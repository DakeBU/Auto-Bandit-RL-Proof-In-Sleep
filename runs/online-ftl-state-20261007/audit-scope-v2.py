from common_v1 import *
fixed(proving=True,integrated=True);owned=load(RUN/'owned-commit-paths-v1.json');b=load(RUN/'body-bindings-v1.json')
for p,k in [(MEAN,'Mean_sha256'),(PUBLIC,'public_sha256'),(CANARY,'canary_sha256')]:assert sha(p)==b[k]
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
for p,imp in [('BanditRLProof.lean','BanditRLProof.OnlineLearningFTLState'),('Tests.lean','Tests.OnlineLearningFTLStateCanary')]:
 assert Path(p).read_bytes()==(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes()+('\nimport '+imp+'\n').encode(),p
names={PRE+n for n in load(CONTRACT/'new-public-headers-v1.json')}
for p,key in [('website/content/readings.json','readings'),('website/content/highlights.json','highlights'),('website/content/chapters.json','chapters')]:
 a=load(RUN/'snapshots'/(p.replace('/','--')+'.raw'));c=load(p)
 assert {k:v for k,v in a.items() if k!=key}=={k:v for k,v in c.items() if k!=key}
 if key=='highlights':
  route=set(next(x for x in load('website/content/readings.json')['readings'] if x['slug']=='online-foundations')['teaching_route'])
  for oldnote,newnote in zip(a[key],c[key][:len(a[key])]):
   if oldnote['full_name'] in route:
    assert oldnote['featured'] is False and newnote['featured'] is True
    assert {k:v for k,v in oldnote.items() if k!='featured'}=={k:v for k,v in newnote.items() if k!='featured'}
   else:assert oldnote==newnote
  assert {x['full_name'] for x in c[key]}-{x['full_name'] for x in a[key]}==names
 else:
  pred=lambda x:x.get('slug')=='online-foundations'
  assert [x for x in a[key] if not pred(x)]==[x for x in c[key] if not pred(x)]
  old=next(x for x in a[key] if pred(x));new=next(x for x in c[key] if pred(x))
  excluded=['source_theorems'] if key=='readings' else ['completion_blockers','open_gaps']
  assert {k:v for k,v in old.items() if k not in excluded}=={k:v for k,v in new.items() if k not in excluded}
  if key=='readings':assert new['source_theorems'][:6]==old['source_theorems'] and len(new['source_theorems'])==7
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 old=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes();new=Path(p).read_bytes();assert new.startswith(old)
 for line in new[len(old):].decode('utf-8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK
old=(RUN/'snapshots/MANIFEST.md.raw').read_bytes();new=Path('MANIFEST.md').read_bytes();assert new.startswith(old)
assert all(TASK in s for s in new[len(old):].decode('utf-8').splitlines() if s.strip())
write(RUN/('source-scope-audit-'+sys.argv[1]+'.json'),dict(status='passed',exact_base=BASE,changed_paths=paths,all_paths_owned=True,allold_Mean_bodies_and_definitions_retained=True,actual_three_compiled_sources_unchanged=True,new9proof3definitions6canaries_frozen=True,publicroot_Tests_exact_one_import_each=True,allold6cards_note_text_math_links_globs_Books_preserved=True,four_existing_route_featured_flags_explicit_only=True,journal_raw_prefixes_preserved=True,new_public_math=9,new_named_validation_proofs=6,source_subobligations=2,chapter_complete=False,goal_complete=False))
