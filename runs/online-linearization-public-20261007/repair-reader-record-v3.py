"""Finish evidence after the native task manifest was wrongly assumed absent."""
from common_v2 import *
fixed(True);assert not (RUN/'reader-integration-v2.json').exists()
assert (Path('research-wiki/contribution-contracts/online-linearization-public-20261007.json')).is_file()
assert TASK in Path('MANIFEST.md').read_text(encoding='utf-8')
def formulas(obj):
 if isinstance(obj,dict):return [v for k,v in obj.items() if k=='math']+sum([formulas(v) for k,v in obj.items() if k!='math'],[])
 if isinstance(obj,list):return sum([formulas(v) for v in obj],[])
 return []
checks=[]
for p,key,pred in [('website/content/readings.json','readings',lambda x:x.get('slug')==ROUTE),('website/content/highlights.json','highlights',lambda x:x.get('chapter')==ROUTE),('website/content/chapters.json','chapters',lambda x:x.get('slug')==ROUTE)]:
 old=load(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt'));new=load(p)
 assert [x for x in old[key] if not pred(x)]==[x for x in new[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in new.items() if k!=key}
 a=[x for x in old[key] if pred(x)];b=[x for x in new[key] if pred(x)];assert formulas(a)==formulas(b)
 if key=='readings':assert a[0]['teaching_route']==b[0]['teaching_route'] and len(b[0]['source_theorems'])==1
 if key=='highlights':assert [x['full_name'] for x in a]==[x['full_name'] for x in b] and len(b)==18
 if key=='chapters':assert a[0]['module_globs']==b[0]['module_globs']==[PUBLIC.as_posix()]
 checks.append(dict(path=p,old_sha256=sha(RUN/'snapshots'/('before-'+p.replace('/','--')+'.txt')),current_sha256=sha(p),all_other_Books_unchanged=True,ALL_formula_strings_unchanged=True))
diff=subprocess.check_output(['git','diff',BASE,'--','MANIFEST.md'],text=True)
assert not any(s.startswith('-') and not s.startswith('---') for s in diff.splitlines())
assert all(TASK in s for s in diff.splitlines() if s.startswith('+') and not s.startswith('+++'))
write(RUN/'reader-integration-record-repair-v3.json',dict(status='metadata-record-repaired',actual_failures=[dict(command='integrate-reader-v2.py',exit_code=1,error='AssertionError TASK not in MANIFEST; native new-task already created OWN row',point='All three intended reader prose edits and own contribution JSON were applied; no math strings changed; no duplicate reapplication'),dict(command='project-gates-v2.py',exit_code=1,error='FileNotFoundError reader-integration-v2.json',point='Stopped before any root/Tests/harness invocation; no gate success claimed')],original_helpers_retained=True,MANIFEST_native_OWNrow_retained=True,new_Lean_or_formula_changes=False,contract_version=2,reader_metadata_record_version=3))
write(RUN/'reader-integration-v3.json',dict(route=ROUTE,status='actual-scoped-reader-prose-applied-and-preserved',new_proofs=0,new_definitions=0,new_registry_nodes=0,new_source_math_closures=0,checks=checks,all_other_Books_unchanged=True,ALL_formula_strings_unchanged=True,curated_names_unchanged=True,source_cards=1,library_notes=18,curated_links=4,notation_entries=3,proofbridge_steps=4,worked_example_steps=4,R9_format_withdrawn_only_by_separate_correction=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
script=(RUN/'project-gates-v2.py').read_text(encoding='utf-8').replace('reader-integration-v2.json','reader-integration-v3.json').replace('combined-root-v2','combined-root-v3').replace('combined-Tests-v2','combined-Tests-v3').replace('full-harness-v2','full-harness-v3').replace('combined-gates-v2.json','combined-gates-v3.json')
write(RUN/'project-gates-v3.py',script);fixed(True)
print('Actual reader scope audited; record-only repair, native OWN manifest preserved. Root/Tests/harness still pending actual v3 run.')
