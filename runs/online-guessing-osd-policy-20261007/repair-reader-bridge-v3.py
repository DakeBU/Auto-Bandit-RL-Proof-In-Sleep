"""Fit actual 3--5 proof-bridge schema without dropping mathematical contracts or old formulas."""
from common_v1 import *
headers();assert load(RUN/'site-build-v2-01-exit.json')['exit_code']==1
assert 'incomplete proof bridge' in (RUN/'site-build-v2-01.log').read_text(encoding='utf-8')
p=Path('website/content/readings.json');write(RUN/'snapshots/reader-before-five-step-bridge-repair-v3.json',p.read_bytes());d=load(p);x=next(a for a in d['readings'] if a['slug']=='online-guessing-osd');steps=x['proof_bridge']['steps'];assert len(steps)==6
steps[3]['detail']+=' '+steps[5]['detail'];steps[3]['fallback']+=' '+steps[5]['fallback'];steps.pop()
assert len(steps)==5
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'reader-bridge-repair-v3.json',dict(status='metadata-only bridge cardinality repair',failed_gate='site-build-v2-01',actual_rule='Existing proof bridge requires three to five complete steps.',repair='Merge new finite/eventual boundary prose into existing fourth average step, retain new fifth actual support producer; retain all four historical bridge formulas and six complete source cards.',source_cards=6,library_notes=16,curated_links=4,proofbridge_steps=5,no_proof_type_body_change=True,chapter_complete=False,goal_complete=False))
native('reader-bridge-repair-event-v3','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,failed_gate='site-build-v2-01',metadata_repair='Merge prose into existing average step to fit actual five-step bridge schema, contracts/formulas preserved.',no_math_change=True,chapter_complete=False,goal_complete=False)))
native('reader-bridge-repair-resume-v3','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,metadata_only=True,chapter_complete=False,goal_complete=False)))
native('reader-bridge-repaired-candidate-v3','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,site_rerun=True,reader_FINAL_pending=True,chapter_complete=False,goal_complete=False)))
text=(RUN/'verify-registry-v2.py').read_text(encoding='utf-8').replace("len(x['proof_bridge']['steps'])==6","len(x['proof_bridge']['steps'])==5").replace('proofbridge_steps=6','proofbridge_steps=5');write(RUN/'verify-registry-v3.py',text)
text=(RUN/'source-site-gates-v3.py').read_text(encoding='utf-8')
for a,b in [('contributor-exact-v3-01','contributor-exact-v4-01'),('scoped-diff-v2-01','scoped-diff-v3-01'),("'v2')","'v3')"),('source-scope-v2-01','source-scope-v3-01'),('site-build-v2-01','site-build-v3-01'),('site-build-v2.log','site-build-v3.log'),('verify-registry-v2.py','verify-registry-v3.py')]:text=text.replace(a,b)
text=text.replace("'Align guessing-policy contribution production and test coverage fields'","'Fit guessing-policy reader to bounded teaching and proof bridge schemas'")
# The scope audit writes a versioned record, preserving its earlier passed record.
scope=(RUN/'audit-scope-v2.py').read_text(encoding='utf-8').replace('source-scope-audit-v2.json','source-scope-audit-v3.json');write(RUN/'audit-scope-v3.py',scope)
text=text.replace('audit-scope-v2.py','audit-scope-v3.py');write(RUN/'source-site-gates-v4.py',text)
headers();print('Actual complete five-step bridge prepared; frozen theorem bodies and source contracts unchanged.')
