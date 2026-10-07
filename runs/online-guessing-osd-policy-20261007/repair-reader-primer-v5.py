"""Keep the existing three-entry notation primer while retaining new legality/history explanations."""
from common_v1 import *
headers();assert load(RUN/'site-check-v1-01-exit.json')['exit_code']==1
assert 'exactly three notation-primer entries' in (RUN/'site-check-v1-01.log').read_text(encoding='utf-8')
p=Path('website/content/readings.json');write(RUN/'snapshots/reader-before-three-entry-primer-repair-v5.json',p.read_bytes());d=load(p);x=next(a for a in d['readings'] if a['slug']=='online-guessing-osd');items=x['notation'];assert len(items)==5
items[0]['meaning']+=' '+items[3]['meaning'];items[1]['meaning']+=' '+items[4]['meaning'];del items[3:]
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'reader-primer-repair-v5.json',dict(status='metadata-only three-entry notation repair',failed_gate='site-check-v1-01',actual_rule='Site checker requires exactly three complete notation-primer entries.',repair='Merge full played-legality explanation into matched-label entry and history/information explanation into known-horizon entry; no content or math removed.',notation_entries=3,source_cards=6,library_notes=16,curated_links=4,proofbridge_steps=5,all_Lean_types_bodies_and_source_formulas_unchanged=True,chapter_complete=False,goal_complete=False))
native('reader-primer-repair-event-v5','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,failed_gate='site-check-v1-01',metadata_repair='Merge history and played legality into three required primer entries; content retained.',no_math_change=True,chapter_complete=False,goal_complete=False)))
native('reader-primer-repair-resume-v5','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,metadata_only=True,chapter_complete=False,goal_complete=False)))
native('reader-primer-repaired-candidate-v5','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,full_site_checker_rerun=True,reader_FINAL_pending=True,chapter_complete=False,goal_complete=False)))
scope=(RUN/'audit-scope-v4.py').read_text(encoding='utf-8').replace('source-scope-audit-v4.json','source-scope-audit-v5.json');write(RUN/'audit-scope-v5.py',scope)
reg=(RUN/'verify-registry-v3.py').read_text(encoding='utf-8').replace('[5,4,6]','[3,4,6]').replace('notation_entries=5','notation_entries=3');write(RUN/'verify-registry-v4.py',reg)
text=(RUN/'source-site-gates-v5.py').read_text(encoding='utf-8')
for a,b in [('contributor-exact-v5-01','contributor-exact-v6-01'),('scoped-diff-v4-01','scoped-diff-v5-01'),("'v4')","'v5')"),('source-scope-v4-01','source-scope-v5-01'),('audit-scope-v4.py','audit-scope-v5.py'),('site-build-v4-01','site-build-v5-01'),('site-build-v4.log','site-build-v5.log'),('site-check-v1-01','site-check-v2-01'),('verify-registry-v3.py','verify-registry-v4.py')]:text=text.replace(a,b)
write(RUN/'source-site-gates-v6.py',text)
headers();print('Three-entry notation primer now fits actual full site checker; new scope explanations retained.')
