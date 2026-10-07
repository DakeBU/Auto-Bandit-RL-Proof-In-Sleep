from common_v1 import *
fixed(True);owned=load(RUN/'owned-commit-paths-v1.json')
binding=load(RUN/'body-bindings-v1.json')
assert sha(CANARY)==binding['canary_sha256'] and sha('Tests.lean')==binding['Tests_root_sha256']
headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by\b)',CANARY.read_text(encoding='utf-8'))}
assert headers==load(CONTRACT/'planned-canary-headers-v1.json')
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
def old(p):return load(RUN/'snapshots'/(p.replace('/','--')+'.raw'))
def formulas(o):
 if isinstance(o,dict):return [v for k,v in o.items() if k=='math']+sum([formulas(v) for k,v in o.items() if k!='math'],[])
 if isinstance(o,list):return sum([formulas(v) for v in o],[])
 return []
checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('full_name')==PRE+'lemma_1_2'),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 a=old(p);b=load(p)
 assert [x for x in a[key] if not pred(x)]==[x for x in b[key] if not pred(x)]
 assert {k:v for k,v in a.items() if k!=key}=={k:v for k,v in b.items() if k!=key}
 before=next(x for x in a[key] if pred(x));after=next(x for x in b[key] if pred(x))
 assert formulas(before)==formulas(after)
 if key=='readings':
  assert before['teaching_route']==after['teaching_route'] and before['source_theorems'][1:]==after['source_theorems'][1:]
  assert {k:v for k,v in before.items() if k not in ['source_theorems','worked_example']}=={k:v for k,v in after.items() if k not in ['source_theorems','worked_example']}
  assert {k:v for k,v in before['worked_example'].items() if k!='boundary'}=={k:v for k,v in after['worked_example'].items() if k!='boundary'}
  assert {k:v for k,v in before['source_theorems'][0].items() if k not in ['contract','local_status']}=={k:v for k,v in after['source_theorems'][0].items() if k not in ['contract','local_status']}
 if key=='highlights':assert {k:v for k,v in before.items() if k not in ['lean_notes','proof_idea','why']}=={k:v for k,v in after.items() if k not in ['lean_notes','proof_idea','why']}
 if key=='chapters':assert {k:v for k,v in before.items() if k not in ['completion_blockers','open_gaps']}=={k:v for k,v in after.items() if k not in ['completion_blockers','open_gaps']}
 checks.append(dict(path=p,all_other_Books_notes_cards_unchanged=True,all_math_links_moduleglobs_preserved=True))
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 before=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes();after=Path(p).read_bytes();assert after.startswith(before),p
 for line in after[len(before):].decode('utf-8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK,(p,line)
before=(RUN/'snapshots/MANIFEST.md.raw').read_bytes();after=Path('MANIFEST.md').read_bytes();assert after.startswith(before)
assert all(TASK in s for s in after[len(before):].decode('utf-8').splitlines() if s.strip())
write(RUN/('source-scope-audit-'+sys.argv[1]+'.json'),dict(status='passed',exact_base=BASE,changed_paths=paths,all_paths_owned=True,all_existing_public_oldcanary_roots_pins_oldcontracts_inventory_SGB_immutable=True,new_canary_exact7_frozenheaders=True,Tests_exact_one_import=True,reader_checks=checks,journal_raw_prefixes_preserved=True,MANIFEST_only_OWNrow=True,new_public_math=0,new_named_validation_proofs=7,new_source_math_closures=0,chapter_complete=False,goal_complete=False))
print('Actual exact source/public/Tests import/seven frozen targets/one-card one-note math-links/OWNjournal preservation PASS.')
