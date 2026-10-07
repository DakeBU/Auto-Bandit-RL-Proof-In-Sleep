from common_v1 import *
fixed(True);owned=load(RUN/'owned-commit-paths-v1.json')
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('chapter')==ROUTE),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 old=load(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt'));new=load(p)
 assert [x for x in old[key] if not pred(x)]==[x for x in new[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in new.items() if k!=key}
 a=[x for x in old[key] if pred(x)];b=[x for x in new[key] if pred(x)]
 if key=='readings':
  def formulas(o):
   if isinstance(o,dict):return [v for k,v in o.items() if k=='math']+sum([formulas(v) for k,v in o.items() if k!='math'],[])
   if isinstance(o,list):return sum([formulas(v) for v in o],[])
   return []
  assert formulas(a)==formulas(b) and a[0]['source_theorems'][4:]==b[0]['source_theorems'][4:] and a[0]['teaching_route']==b[0]['teaching_route']
 if key=='highlights':assert [x for x in a if x['full_name'].startswith('BanditRL.OnlineGuessingSubgradientPolicy.')]==[x for x in b if x['full_name'].startswith('BanditRL.OnlineGuessingSubgradientPolicy.')]
 if key=='chapters':assert a[0]['module_globs']==b[0]['module_globs']
 checks.append(dict(path=p,all_other_Books_unchanged=True,all_math_and_oldlinks_preserved=True))
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 before=(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt')).read_bytes();after=Path(p).read_bytes();assert after.startswith(before),p
 for line in after[len(before):].decode('utf-8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK,(p,line)
diff=subprocess.check_output(['git','diff',BASE,'--','MANIFEST.md'],text=True)
assert not any(s.startswith('-') and not s.startswith('---') for s in diff.splitlines())
assert all(TASK in s for s in diff.splitlines() if s.startswith('+') and not s.startswith('+++'))
write(RUN/'source-scope-audit-final-v1.json',dict(status='passed',exact_base=BASE,changed_paths=paths,all_changed_paths_owned=True,all_existing_public_canary_root_Tests_pins_contracts_unchanged=True,all_other_Books_and_PR182_notes_cards_math_preserved=True,journal_raw_prefixes_preserved=True,MANIFEST_only_OWNrow=True,Book_checks=checks,new_math=0,chapter_complete=False,goal_complete=False))
print('Scoped ownership/otherBooks/PR182/frozen proofs/root/Tests/pins/SGB/rawjournalprefix preservation passed.')
