"""Conserve primer information within the existing exactly-three-entry schema."""
from common_v4 import *
fixed(True,True);assert load(RUN/'site-check-v1-01-exit.json')['exit_code']==1
assert 'online-lipschitz needs exactly three notation-primer entries' in (RUN/'site-check-v1-01.log').read_text(encoding='utf-8')
p=Path('website/content/readings.json');write(RUN/'snapshots/readings-before-notation-primer-repair-v2.txt',p.read_bytes())
d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE);notes=x['notation'];assert len(notes)==4
rest={k:v for k,v in x.items() if k!='notation'}
x['notation']=[notes[0],dict(term='Ambient queries: global supports and plane derivatives',meaning=notes[1]['meaning']+' '+notes[3]['meaning']),notes[2]]
assert len(x['notation'])==3 and rest=={k:v for k,v in x.items() if k!='notation'}
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
p=Path('research-wiki/contribution-contracts/online-convex-nondifferentiability-20261007.json');write(RUN/'snapshots/manifest-before-notation-count-repair-v2.txt',p.read_bytes())
t=p.read_text(encoding='utf-8');t=t.replace('4notations','3notations').replace('4notation','3notation');p.write_bytes(t.encode())
write(RUN/'notation-primer-reader-repair-v2.json',dict(failed_attempt='site-check-v1-01',reason='Existing checker requires exactly three primer entries',repair='Combine global-support ambient-query explanation with plane ambient-derivative explanation; preserve every original meaning and other reading fields',all_source_cards_proof_bridge_unchanged=True,existing_checker_unchanged=True,current_notation_entries=3,prior_candidate_four_entry_counts_preserved_as_historical=True,mathematical_repairs=[],Lean_source_headers_bodies_unchanged=True))
write(RUN/'reader-counts-overlay-v2.json',dict(source_cards=3,highlight_links=3,curated_links=3,notation_entries=3,proof_bridge_steps=5,supersedes_only_historical_candidate_four_notation_count=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
t=(RUN/'verify-registry-v1.py').read_text(encoding='utf-8').replace("len(x['notation'])==4","len(x['notation'])==3").replace('notation_entries=4','notation_entries=3').replace('4notation.','3notation.')
write(RUN/'verify-registry-v2.py',t);compile(t,str(RUN/'verify-registry-v2.py'),'exec')
t=(RUN/'bind-integrated-gates-v3.py').read_text(encoding='utf-8').replace('contributor-exact-v3-01','contributor-exact-v4-01').replace('scoped-diff-v2-01','scoped-diff-v3-01').replace('site-build-v2-01','site-build-v3-01').replace('site-check-v1-01','site-check-v2-01').replace('registry-v1-01','registry-v2-01').replace('full-harness-v2-01','full-harness-v3-01').replace('notation_entries=4','notation_entries=3')
t=t.replace("'Site build v1 rejected seven bridge steps; existing 3-to-5-step schema preserved, earlier forward/reverse pairs consolidated without losing explanations/formulas, all three new producer steps retained'","'Site build v1 rejected seven bridge steps; existing 3-to-5-step schema preserved, earlier forward/reverse pairs consolidated without losing explanations/formulas, all three new producer steps retained','Site check v1 rejected four primer entries; ambient-support and derivative explanations consolidated without losing meaning, current exactly three entries; earlier four-entry candidate counts retained as historical'")
write(RUN/'bind-integrated-gates-v4.py',t);compile(t,str(RUN/'bind-integrated-gates-v4.py'),'exec')
t=(RUN/'record-acceptance-v1.py').read_text(encoding='utf-8').replace('notation_entries=4','notation_entries=3')
write(RUN/'record-acceptance-v2.py',t);compile(t,str(RUN/'record-acceptance-v2.py'),'exec')
t=(RUN/'prepare-pr-payload-v1.py').read_text(encoding='utf-8').replace('four notation entries','three notation entries').replace('root/Tests/fullharnessv2','root/Tests/fullharnessv2 plus current-reader fullharnessv3').replace('No test or source weakening.','Existing site-schema rejections are retained: seven proof-bridge steps consolidated into five and four primer entries into three, preserving every explanation/formula/source card. No test or source weakening.')
write(RUN/'prepare-pr-payload-v2.py',t);compile(t,str(RUN/'prepare-pr-payload-v2.py'),'exec')
fixed(True,True);print('Exactly three primer entries retain all ambient-query explanations; current counts versioned, all mathematical bytes unchanged.')
