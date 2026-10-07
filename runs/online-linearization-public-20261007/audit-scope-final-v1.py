from common_v2 import *
fixed(True);owned=load(RUN/'owned-commit-paths-v1.json');paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
def formulas(obj):
 if isinstance(obj,dict):return [v for k,v in obj.items() if k=='math']+sum([formulas(v) for k,v in obj.items() if k!='math'],[])
 if isinstance(obj,list):return sum([formulas(v) for v in obj],[])
 return []
checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('chapter')==ROUTE),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 old=load(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt'));new=load(p)
 assert [x for x in old[key] if not pred(x)]==[x for x in new[key] if not pred(x)] and {k:v for k,v in old.items() if k!=key}=={k:v for k,v in new.items() if k!=key}
 a=[x for x in old[key] if pred(x)];b=[x for x in new[key] if pred(x)];assert formulas(a)==formulas(b)
 if key=='readings':assert a[0]['teaching_route']==b[0]['teaching_route']
 if key=='highlights':assert [x['full_name'] for x in a]==[x['full_name'] for x in b]
 if key=='chapters':assert a[0]['module_globs']==b[0]['module_globs']
 checks.append(dict(path=p,all_other_Books_unchanged=True,ALL_math_strings_and_oldlinks_preserved=True))
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 before=(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt')).read_bytes();after=Path(p).read_bytes();assert after.startswith(before),p
 for line in after[len(before):].decode('utf-8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK,(p,line)
diff=subprocess.check_output(['git','diff',BASE,'--','MANIFEST.md'],text=True);assert not any(s.startswith('-') and not s.startswith('---') for s in diff.splitlines());assert all(TASK in s for s in diff.splitlines() if s.startswith('+') and not s.startswith('+++'))
write(RUN/'source-scope-audit-final-v1.json',dict(status='passed',exact_base=BASE,changed_paths=paths,all_changed_paths_owned=True,all_existing_public_canary_root_Tests_pins_contracts_unchanged=True,all_other_Books_and_ALL_math_strings_unchanged=True,journal_raw_prefixes_preserved=True,MANIFEST_only_OWNrow=True,Book_checks=checks,new_math=0,chapter_complete=False,goal_complete=False))
print('Actual exact ownership/proofs/root/Tests/pins/oldcontracts/SGB/otherBooks/mathstrings/rawjournalprefix preservation PASS.')
