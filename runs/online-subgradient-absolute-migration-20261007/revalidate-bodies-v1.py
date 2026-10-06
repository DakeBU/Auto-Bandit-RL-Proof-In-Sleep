from common import *
f=fixed();r=bind_review('source-contract-receipt-v1.json','source-contract-inputs-v1.json','contract-binding-audit-v1.json')
event('stabilized',dict(contract_report_sha256=r['report_sha256'],frozen_headers=f['headers'],source_package_accepted=False))
event('proving',dict(route='single retained actual scalar support producer',allowed_math_mutations=False,source_package_accepted=False))
write(RUN/'30_lower_worker-v1.md','Actual four retained scalar support bodies revalidated only after distinct CONTRACT. Preserve global-y two directions/inclusive zero interval/strict-sign nonzero cancellation/allx actual dispatch. Whole threecanary proofs/0defs unchanged; no new math/TEST/registry nodes or supplied support oracle. Source package and whole Goal not closed.')
gate('public-body-v1-01','lake','env','lean',PUBLIC)
gate('public-canary-focused-v1-01','lake','build','Tests.OnlineSubgradientAbsoluteCanary')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
for n,h in f['headers'].items():
 p=RUN/'native-public-fences'/(n+'.json');native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p)
 assert load(p)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC,'--lean-file',CANARY)
fixed()
raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
named=load(RUN/'public-named-declarations-v1.json');q=named['axiom_probe'];assert len(matches)==len(set(q))==7 and {n for n,a in matches}==set(q)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==7 and {n['name'] for n in g['nodes']}==set(q) and all(n['has_value'] and n['kind']=='theorem' for n in g['nodes'])
new={n['name']:n for n in g['nodes']};old=load(RUN/'compiled-ready-graph-v1.json');assert all(n==new[n['name']] for n in old['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};required=load(RUN/'ready-dependencies-v1.json')['required_value_pairs']
required.extend([['AbsoluteZeroProbe.zero_boundary_canary',PRE+'abs_subgradient_zero'],['AbsoluteZeroProbe.zero_is_not_a_singleton',PRE+'abs_subgradient_zero'],['AbsoluteAllPointsProbe.source_three_branches_canary',PRE+'example_2_24']])
for pair in required:assert tuple(pair) in pairs,pair
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=7,proof_nodes=7,definition_nodes=0,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-public-graph-v1.json'),required_value_pairs=required,ready_four_nodes_exactly_preserved=True,full_registry_export=False))
jobs={}
for label in ['retained-focused-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',fixed_headers=f['headers'],module_sha256=sha(PUBLIC),whole_canary_sha256=sha(CANARY),retained_proofs=4,new_production_proofs=0,new_test_proofs=0,whole_canary_proofs=3,named_kernel_checks=7,named_kernel_axes=axes,native_guards=4,focused_jobs=jobs,selected_graph_nodes=7,selected_graph_direct_references=len(g['edges']),body_seconds=passed('public-body-v1-01')['elapsed_seconds'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('retained-body-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','SUBGRADIENT-ABSOLUTE-RETAINED-BODIES-V1','--lean',PUBLIC,'--statement-hash',f['headers']['example_2_24'],'--reused-declaration',PRE+'example_2_24','--verifier-evidence',RUN/'public-body-v1-01.log','--progress-class','retrieval-reuse','--notes','Actual four retained proofs/whole threecanaries/seven unique named kernel checks/four guards/selected sevenproof nodes checked; zero new math/TESTs. BODY/package gates pending; Chapter2/book incomplete.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=n,statement_hash=h,state='retained exact body compiled; distinct BODY pending') for n,h in f['headers'].items()],source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Four actual bodies/whole threecanaries/sevenkernel checks/fourguards/sevenproofnodes',len(g['edges']),'refs PASS; distinct BODY pending.')
