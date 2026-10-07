"""Repair an actual source-card schema rejection without weakening any meaning/checker."""
from common_v2 import *
fixed(True,True);assert load(RUN/'site-build-v1-01-exit.json')['exit_code']==1
p=Path('website/content/readings.json');d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
write(RUN/'snapshots/reader-before-sourcecontract-repair-v2.txt',p.read_bytes())
oldcards=list(x['source_theorems'][:3]);card=x['source_theorems'][3];old=dict(card['contract'])
assert set(old)=={'space','losses','horizon','decision','regret','guarantee'}
card['contract']=dict(model='Deterministic real Euclidean plane and set cardinality.',assumptions=' '.join([old['space'],old['losses'],old['decision']]),parameters=old['horizon']+' The same fixed nondegenerate CLOSED segment has endpoints (0,0) and (0,1); every actual member is ambient nonsmooth. No countability premise is assumed in the production terminal.',regret=old['regret'],guarantee=old['guarantee'])
card['plain']='Here N_f denotes the set of all real-plane points x where f has no ambient real Frechet derivative. '+card['plain']
assert x['source_theorems'][:3]==oldcards
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
p=Path('research-wiki/contribution-contracts/online-convex-uncountability-20261007.json');c=load(p)
write(RUN/'snapshots/manifest-before-sourcecontract-repair-v2.txt',p.read_bytes())
c['truth_boundary']+=' Actual sitebuild v1 rejected the new source-card contract keys. Repair reorganizes every original sentence into the existing exact model/assumptions/parameters/regret/guarantee schema and explicitly defines displayed N_f as the same-function ambient nonsmooth locus. Original three cards unchanged; no generator/checker/math/header weakening. Current-reader full harness rerun separately.'
p.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'reader-contract-repair-v2.json',dict(failed_attempt='site-build-v1-01',reason='Exact source-card contract schema requires model/assumptions/parameters/regret/guarantee; new card authored six different field names.',original_contract=old,repaired_contract=card['contract'],all_original_sentences_retained=True,three_old_sourcecards_unchanged=True,existing_site_schema_and_checker_unchanged=True,explicit_N_f_definition_added=True,public_and_canary_bodies_headers_unchanged=True,applicable_actual_root_Tests_gate='combined-project-gates-v1.json',current_reader_full_harness_rerun_required=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('repair',dict(reason='Source-card schema rejection',repair=(RUN/'reader-contract-repair-v2.json').as_posix(),mathematical_targets_unchanged=True),attempt='reader-v2')
fixed(True,True);print('Actual source-card schema failure preserved; all meaning retained in exact existing five fields.')
