from common_v1 import *
fixed(proving=True,integrated=True);owned=load(RUN/'owned-commit-paths-v1.json');binding=load(RUN/'body-bindings-v1.json')
assert sha(PUBLIC)==binding['public_sha256'] and sha(CANARY)==binding['canary_sha256']
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
def old(p):return load(RUN/'snapshots'/(p.replace('/','--')+'.raw'))
def formulas(o):
 if isinstance(o,dict):return [v for k,v in o.items() if k=='math']+sum([formulas(v) for k,v in o.items() if k!='math'],[])
 if isinstance(o,list):return sum([formulas(v) for v in o],[])
 return []
newnames={PRE+n for n in load(CONTRACT/'new-public-headers-v1.json')};checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('full_name')==PRE+'theorem_1_3' or x.get('full_name') in newnames),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 a=old(p);b=load(p);assert [x for x in a[key] if not pred(x)]==[x for x in b[key] if not pred(x)]
 assert {k:v for k,v in a.items() if k!=key}=={k:v for k,v in b.items() if k!=key}
 if key=='readings':
  before=next(x for x in a[key] if pred(x));after=next(x for x in b[key] if pred(x));assert len(after['source_theorems'])==6
  assert {k:v for k,v in before.items() if k!='source_theorems'}=={k:v for k,v in after.items() if k!='source_theorems'}
  for i in [0,2,3]:assert before['source_theorems'][i]==after['source_theorems'][i]
  assert {k:v for k,v in before['source_theorems'][1].items() if k not in ['contract','local_status']}=={k:v for k,v in after['source_theorems'][1].items() if k not in ['contract','local_status']}
  assert formulas(before)==formulas({**after,'source_theorems':after['source_theorems'][:4]})
 if key=='highlights':
  before=next(x for x in a[key] if x['full_name']==PRE+'theorem_1_3');after=next(x for x in b[key] if x['full_name']==PRE+'theorem_1_3')
  assert {k:v for k,v in before.items() if k not in ['lean_notes','proof_idea','why']}=={k:v for k,v in after.items() if k not in ['lean_notes','proof_idea','why']}
  assert {x['full_name'] for x in b[key]}-{x['full_name'] for x in a[key]}==newnames
 if key=='chapters':
  before=next(x for x in a[key] if pred(x));after=next(x for x in b[key] if pred(x));assert {k:v for k,v in before.items() if k not in ['completion_blockers','open_gaps']}=={k:v for k,v in after.items() if k not in ['completion_blockers','open_gaps']}
 checks.append(dict(path=p,all_other_Books_notes_cards_unchanged=True,existing_math_links_moduleglobs_preserved=True))
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 before=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes();after=Path(p).read_bytes();assert after.startswith(before),p
 for line in after[len(before):].decode('utf-8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK,(p,line)
before=(RUN/'snapshots/MANIFEST.md.raw').read_bytes();after=Path('MANIFEST.md').read_bytes();assert after.startswith(before)
assert all(TASK in s for s in after[len(before):].decode('utf-8').splitlines() if s.strip())
write(RUN/('source-scope-audit-'+sys.argv[1]+'.json'),dict(status='passed',exact_base=BASE,changed_paths=paths,all_paths_owned=True,old5proof1definition_complete_prefix_unchanged=True,actual_compiled_public_canary_bodies_frozen=True,new2source_6test_headers_frozen=True,Tests_exact_one_import=True,reader_checks=checks,journal_raw_prefixes_preserved=True,MANIFEST_only_OWNrow=True,new_public_math=2,new_named_validation_proofs=6,chapter_complete=False,goal_complete=False))
