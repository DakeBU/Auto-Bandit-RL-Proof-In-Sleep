from common_v1 import *
fixed(integrated=True)
resolution=load(RUN/'body-reviewed-source-resolution-v1.json');assert sha(resolution['immutable_snapshot'])==resolution['reviewed_sha256']
for stage,packet,receipt in [('CONTRACT','source-contract-inputs-v1.json','source-contract-receipt-v1.json'),('BODY','body-review-inputs-v1.json','public-body-receipt-v1.json')]:
 reviewed={x['path']:x['sha256'] for x in load(RUN/receipt)['reviewed_files']}
 for x in load(RUN/packet)['rows']:
  p=x['path'];resolved=resolution['immutable_snapshot'] if Path(p).resolve()==PUBLIC.resolve() else p
  assert sha(resolved)==x['sha256']==reviewed[p],(stage,p)
for p,key in [('website/content/readings.json','readings'),('website/content/highlights.json','highlights'),('website/content/chapters.json','chapters')]:
 old=load(RUN/'snapshots'/(p.replace('/','--')+'.raw'));new=load(p)
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in new.items() if k!=key}
 if key=='highlights':
  assert new[key][:len(old[key])]==old[key]
  assert {x['full_name'] for x in new[key]}-{x['full_name'] for x in old[key]}=={PRE+'comparatorRegret_eq_sum',PRE+'noRegret_of_vanishing_bound'}
 else:
  pred=lambda x:x.get('slug')==ROUTE
  assert [x for x in old[key] if not pred(x)]==[x for x in new[key] if not pred(x)]
  a=next(x for x in old[key] if pred(x));b=next(x for x in new[key] if pred(x))
  excluded=['source_theorems'] if key=='readings' else ['completion_blockers','open_gaps']
  assert {k:v for k,v in a.items() if k not in excluded}=={k:v for k,v in b.items() if k not in excluded}
  if key=='readings':assert b['source_theorems'][:7]==a['source_theorems'] and len(b['source_theorems'])==8
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 old=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes();new=Path(p).read_bytes();assert new.startswith(old)
 for line in new[len(old):].decode('utf-8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK
old=(RUN/'snapshots/MANIFEST.md.raw').read_bytes();new=Path('MANIFEST.md').read_bytes();assert new.startswith(old)
assert all(TASK in s for s in new[len(old):].decode('utf-8').splitlines() if s.strip())
owned=load(RUN/'owned-commit-paths-v1.json')
paths=set(subprocess.check_output(['git','diff','--name-only',BASE],text=True).splitlines())|set(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines())
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
write(RUN/('source-scope-'+sys.argv[1]+'.json'),dict(status='passed',changed_owned_paths=sorted(paths),exact_PR189_base=BASE,all_old_mathematical_bytes_and_headers_unchanged=True,only_reviewed_module_doc_inserted=True,one_Tests_import=True,public_root_unchanged=True,seven_old_cards_all_old_notes_math_and_curated_IDs_preserved=True,other_Books_scanner_pins_and_shared_FTLState_source_boundary_unchanged=True,all155_CONTRACT_and262_BODY_inputs_preserved_with_explicit_old_source_snapshot=True,all_journals_raw_prefixes_preserved=True,new_production_math=0,chapter_complete=False,goal_complete=False))
print('Scoped source/reader/journal/pinned input audit passed; ownedpaths',len(paths))
