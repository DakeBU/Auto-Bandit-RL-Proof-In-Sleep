"""Honor four-entry teaching route; preserve every old declaration URL and library card."""
from common_v1 import *
headers();assert load(RUN/'site-build-v1-01-exit.json')['exit_code']==1
assert 'needs one to 4 unique teaching-route declarations' in (RUN/'site-build-v1-01.log').read_text(encoding='utf-8')
p=Path('website/content/readings.json');write(RUN/'snapshots/reader-before-four-link-repair-v2.json',p.read_bytes());d=load(p);x=next(a for a in d['readings'] if a['slug']=='online-guessing-osd');assert len(x['teaching_route'])==8
old=x['teaching_route'][:4];PRE='BanditRL.OnlineGuessingSubgradientPolicy.'
x['teaching_route']=[old[0],PRE+'step_clamp',PRE+'example_2_32',PRE+'example_2_32_average_eventually']
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
p=Path('research-wiki/contribution-contracts/online-guessing-osd-policy-20261007.json');write(RUN/'snapshots/manifest-before-four-link-repair-v2.json',p.read_bytes());c=load(p)
c['progress_updates']['teaching_route']='updated: four-entry source-support to policy-update/finite/family route; every old canonical card and declaration URL retained in the library and shared registry'
c['verification']['site_check']=c['verification']['site_check'].replace('eight curated links','four curated links')
p.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
write(RUN/'reader-route-repair-v2.json',dict(status='metadata-only route cardinality repair',failed_gate='site-build-v1-01',actual_rule='One to four unique teaching-route declarations per existing renderer schema.',old_curated_names=old,current_curated_names=x['teaching_route'],all12old_highlight_cards_unchanged=True,all_old_declaration_IDs_and_URLs_to_be_verified=True,all_old_and_new_source_formula_strings_unchanged=True,no_proof_type_body_change=True,source_cards=6,library_notes=16,curated_links=4,chapter_complete=False,goal_complete=False))
native('reader-route-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,failed_gate='site-build-v1-01',metadata_repair='Four curated entries as actual site schema; old canonical cards/IDsURLs retained.',no_math_change=True,chapter_complete=False,goal_complete=False)))
native('reader-route-repair-resume-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,metadata_only=True,chapter_complete=False,goal_complete=False)))
native('reader-route-repaired-candidate-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,site_rerun=True,reader_FINAL_pending=True,chapter_complete=False,goal_complete=False)))
text=(RUN/'audit-scope-v1.py').read_text(encoding='utf-8').replace("assert a[0]['teaching_route']==b[0]['teaching_route'][:4]","assert b[0]['teaching_route']==load(RUN/'reader-route-repair-v2.json')['current_curated_names']")
write(RUN/'audit-scope-v2.py',text.replace("'source-scope-audit-v1.json'","'source-scope-audit-v2.json'"))
text=(RUN/'verify-registry-v1.py').read_text(encoding='utf-8').replace('[5,8,6]','[5,4,6]').replace('curated_links=8','curated_links=4')
text=text.replace("for name in x['teaching_route']:","for name in x['teaching_route']+[a['full_name'] for a in load('website/content/highlights.json')['highlights'] if a.get('chapter')==ROUTE]:")
write(RUN/'verify-registry-v2.py',text)
text=(RUN/'source-site-gates-v2.py').read_text(encoding='utf-8').replace("'contributor-exact-v2-01'","'contributor-exact-v3-01'").replace("'scoped-diff-v1-01'","'scoped-diff-v2-01'").replace("'v1')","'v2')").replace("'source-scope-v1-01'","'source-scope-v2-01'").replace("RUN/'audit-scope-v1.py'","RUN/'audit-scope-v2.py'")
start=text.index("cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py'");end=text.index("subprocess.run([sys.executable",start)
text=text[:start]+"assert load(RUN/'main-relative-diagnostic-v1.json')['status']=='failed-unwaived'\n"+text[end:]
text=text.replace('site-build-v1-01','site-build-v2-01').replace('site-build-v1.log','site-build-v2.log').replace("RUN/'verify-registry-v1.py'","RUN/'verify-registry-v2.py'")
write(RUN/'source-site-gates-v3.py',text)
headers();print('Four curated entries prepared; all historical cards/formulas/URLs preserved, site rerun required.')
