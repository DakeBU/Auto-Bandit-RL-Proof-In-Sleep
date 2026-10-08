from common_v1 import *

prior=ROOT/'docs/contracts/online-ae-causal-v1/targets-v1.json'
expected={x['name'] for x in load(prior)['targets']}
rows=[]
for n in ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards','proof_weapon_cards','local_leaf_cards','local_lean_declarations']:
    old=load(RUN/'baseline'/('retrieval-'+n+'.raw'))
    p=ROOT/'research-wiki/retrieval-index'/(n+'.json');new=load(p)
    assert set(new)==set(old) and isinstance(new['generated'],str)
    a={k:v for k,v in old.items() if k!='generated'}
    b={k:v for k,v in new.items() if k!='generated'}
    added=[]
    if n=='local_lean_declarations':
        oldnames={x['full_name'] for x in a['declarations']}
        added=[x for x in b['declarations'] if x['full_name'] not in oldnames]
        assert {x['full_name'] for x in added}==expected
        assert all(x['file']=='BanditRLProof/OnlineGuessingAECausal.lean' and x['kind']=='theorem' for x in added)
        b['declarations']=[x for x in b['declarations'] if x['full_name'] in oldnames]
    assert a==b,n
    rows.append(dict(path=p.as_posix(),old_sha256=sha(RUN/'baseline'/('retrieval-'+n+'.raw')),
        current_sha256=sha(p),only_generated_timestamp_and_exact_prior3_added=True,actual_added=added))
write(RUN/'draft-retrieval-scope-audit-v1.json',dict(rows=rows,all_old_records_unchanged=True,
    exact_prior_actual_proved_names=sorted(expected),new_current_draft_targets_registered_as_proved=False,
    source_scanner_not_compilation=True,chapter_complete=False,goal_complete=False))
print('Actual six-index audit: old records preserved; only timestamps and prior three exact proved declarations added.',flush=True)
