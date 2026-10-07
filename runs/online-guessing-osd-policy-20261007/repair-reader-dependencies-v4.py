"""Use source-qualified project registry links; keep external mathlib dependency evidence explicit."""
from common_v1 import *
headers();assert load(RUN/'site-build-v3-01-exit.json')['exit_code']==1
raw=(RUN/'site-build-v3-01.log').read_text(encoding='utf-8');assert 'missing_highlight_dependencies' in raw
p=Path('website/content/highlights.json');write(RUN/'snapshots/highlights-before-registry-link-repair-v4.json',p.read_bytes());d=load(p)
for x in d['highlights']:
 if x.get('chapter')=='online-guessing-osd' and x['full_name'].startswith('BanditRL.OnlineGuessingSubgradientPolicy.'):
  x['dependencies']=[n.replace('BanditRL.OnlineGuessingOGD.project_unitInterval','BanditRL.OnlineGradientDescent.project_unitInterval') for n in x['dependencies'] if n not in ['Real.tendsto_sqrt_atTop','tendsto_inv_atTop_zero']]
  if x['full_name'].endswith('average_eventually'):x['lean_notes']+=' External mathlib proof-value dependencies Real.tendsto_sqrt_atTop and tendsto_inv_atTop_zero are verified in the actual compiled graph; the site project registry does not create project-declaration links for them.'
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
p=Path('research-wiki/contribution-contracts/online-guessing-osd-policy-20261007.json');write(RUN/'snapshots/manifest-before-registry-link-repair-v4.json',p.read_bytes());c=load(p);c['reuse_plan']['reused_declarations']=[n.replace('BanditRL.OnlineGuessingOGD.project_unitInterval','BanditRL.OnlineGradientDescent.project_unitInterval') for n in c['reuse_plan']['reused_declarations']];p.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'reader-dependency-repair-v4.json',dict(status='metadata-only source-qualified link repair',failed_gate='site-build-v3-01',repair='Use actual projection namespace BanditRL.OnlineGradientDescent; external mathlib dependencies remain named as prose and actual kernel value evidence, rather than nonexistent project registry links.',all_old_highlights_unchanged=True,all_proof_types_bodies_and_source_formulas_unchanged=True,chapter_complete=False,goal_complete=False))
native('reader-dependency-repair-event-v4','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,failed_gate='site-build-v3-01',metadata_repair='Actual project namespace and explicit external mathlib dependency prose; no graph or proof changes.',no_math_change=True,chapter_complete=False,goal_complete=False)))
native('reader-dependency-repair-resume-v4','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,metadata_only=True,chapter_complete=False,goal_complete=False)))
# Validate all actual reader schemas and references before the clean verified build.
gate('site-preview-preflight-v4-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--output','tmp/online-guessing-osd-policy-preview-v4')
native('reader-dependency-repaired-candidate-v4','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,actual_preview_schema_pass=True,preview_Lean_verified=False,clean_verified_site_FINAL_pending=True,chapter_complete=False,goal_complete=False)))
text=(RUN/'audit-scope-v3.py').read_text(encoding='utf-8').replace('source-scope-audit-v3.json','source-scope-audit-v4.json');write(RUN/'audit-scope-v4.py',text)
text=(RUN/'source-site-gates-v4.py').read_text(encoding='utf-8')
for a,b in [('contributor-exact-v4-01','contributor-exact-v5-01'),('scoped-diff-v3-01','scoped-diff-v4-01'),("'v3')","'v4')"),('source-scope-v3-01','source-scope-v4-01'),('audit-scope-v3.py','audit-scope-v4.py'),('site-build-v3-01','site-build-v4-01'),('site-build-v3.log','site-build-v4.log')]:text=text.replace(a,b)
write(RUN/'source-site-gates-v5.py',text)
headers();print('Actual preview schemas/references passed, unverified preview only; clean verified site rerun prepared.')
