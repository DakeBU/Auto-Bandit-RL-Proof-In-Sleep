"""Actual changed-path ownership, other-Book and frozen-prefix preservation."""
from common_v1 import *
headers();owned=load(RUN/'owned-commit-paths-v1.json');ROUTE='online-guessing-osd'
paths=subprocess.check_output(['git','diff','--name-only',BASE+'...HEAD'],text=True).splitlines()
for p in paths:assert any(p==x or p.startswith(x+'/') for x in owned),p
checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('chapter')==ROUTE),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 old=load(RUN/'snapshots'/p.replace('/','--'));new=load(p)
 assert [x for x in old[key] if not pred(x)]==[x for x in new[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in new.items() if k!=key}
 a=[x for x in old[key] if pred(x)];b=[x for x in new[key] if pred(x)]
 if key=='readings':
  assert b[0]['teaching_route']==load(RUN/'reader-route-repair-v2.json')['current_curated_names']
  assert [(c['label'],c['url'],c['pdf_page'],c['math']) for c in a[0]['source_theorems']]==[(c['label'],c['url'],c['pdf_page'],c['math']) for c in b[0]['source_theorems'][:4]]
 if key=='highlights':assert a==b[:12]
 checks.append(dict(path=p,all_other_Book_subtrees_unchanged=True,old_links_and_formulas_preserved=True))
for p,line in [('BanditRLProof.lean','import BanditRLProof.OnlineGuessingSubgradientPolicy'),('Tests.lean','import Tests.OnlineGuessingSubgradientPolicyCanary')]:
 before=(RUN/'snapshots'/p).read_bytes();assert Path(p).read_bytes()==before+line.encode()+b'\n',p
for p,key in [('runs/lifecycle_sessions.jsonl','session_id'),('runs/trials.jsonl','task'),('runs/lifecycle_memory.jsonl','task')]:
 before=(RUN/'snapshots'/p.replace('/','--')).read_bytes();after=Path(p).read_bytes();assert after.startswith(before),p
 for line in after[len(before):].decode('utf-8').splitlines():
  if line.strip():assert json.loads(line)[key]==TASK,(p,line)
diff=subprocess.check_output(['git','diff',BASE,'--','MANIFEST.md'],text=True)
assert not any(s.startswith('-') and not s.startswith('---') for s in diff.splitlines())
assert all(TASK in s for s in diff.splitlines() if s.startswith('+') and not s.startswith('+++'))
write(RUN/'source-scope-audit-v3.json',dict(status='passed',exact_base=BASE,changed_paths=paths,all_changed_paths_owned=True,old_pins_math_SGB_contracts_unchanged=True,old_runs_unmodified=True,old_canonical_proofs_and_reader_formulas_preserved=True,Book_surface_checks=checks,only_owned_root_Test_imports_appended=True,native_journal_raw_prefixes_preserved=True,MANIFEST_only_owned_task_rows=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('All changed paths owned; all other Books, old proofs/pins/SGB/receipts and journal prefixes preserved.')
