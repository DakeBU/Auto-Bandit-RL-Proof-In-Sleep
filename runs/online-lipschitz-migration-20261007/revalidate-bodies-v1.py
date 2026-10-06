"""After actual CONTRACT, re-elaborate both retained producers and the whole old canary."""
from common_v2 import *
f=fixed();r=bind_review('source-contract-receipt-v1.json','source-contract-inputs-v1.json','contract-binding-audit-v1.json')
assert load(RUN/'prior-contract-binding-v1.json')['status']=='passed'
assert r.get('source_convention_verdict',{}),'A separate actual source convention decision is required before proving'
event('stabilized',dict(contract_report_sha256=r['report_sha256'],frozen_headers=f['headers'],source_package_accepted=False,source_convention_verdict=r['source_convention_verdict']))
write(RUN/'stabilized-leaf-selection-v1.json',dict(stage='stabilized',source_review=r['report_sha256'],source_convention_verdict=r['source_convention_verdict'],selected_finite_leaves=['SourceLipschitzOn','theorem_2_30'],actual_ready_graph=sha(RUN/'compiled-ready-graph-v1.json'),terminal_mutations_allowed=False,allowed_edits='Versioned evidence, ordinary leading comment and only online-lipschitz reader subtrees after BODY; no mathematics/canary/shared/root/pin edit',source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('proving',dict(route='single actual finite-on-V/open-ball perturbation and properconvex support existence/two-sign route',allowed_math_mutations=False,source_package_accepted=False))
write(RUN/'30_lower_worker-v1.md','ONE retained normed-additive finite-on-V/allpairs definition and ONE retained full-interior iff actual body re-elaborated after distinct CONTRACT/convention judgment. Forward openinteriorball -> actual LipschitzOnWith -> shared normalizedsupport perturbation; reverse actual supports from properconvexinterior at BOTHpoints -> exclude infinities -> actual global inequalities -> CauchySchwarz/two signs -> absbound. Whole18oldcanaryproof6TESTdefs2abbrevs fixed; negativeL0Dobstruction included;0newmath/TEST. No chapter/Goal acceptance from compilation.')
gate('public-body-v1-01','lake','env','lean',PUBLIC)
gate('public-canary-focused-v1-01','lake','build','Tests.OnlineLipschitzSubgradientCanary')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
for n,h in f['headers'].items():
 p=RUN/('native-public-fences/'+n+'.json');native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC,'--lean-file',CANARY)
fixed();raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
q=load(RUN/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(set(q))==28 and {n for n,a in matches}==set(q)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==28 and {n['name'] for n in g['nodes']}==set(q) and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==19 and sum(n['kind']=='definition' for n in g['nodes'])==9
new={n['name']:n for n in g['nodes']};old=load(RUN/'compiled-ready-graph-v1.json');assert all(n==new[n['name']] for n in old['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};required=list(load(RUN/'ready-dependencies-v1.json')['required_value_pairs'])
for n in ['abs_all_supports_and_nonzero','linear_three_reverse','zero_constant','singleton_empty_interior_and_boundary','halfline_interior_not_whole_domain','zero_dimension']:
 required.append(['LipschitzProbe.'+n,PRE+'theorem_2_30'])
required.extend([['LipschitzProbe.abs_all_supports_and_nonzero',PRE+'abs_subgradient_positive'],['LipschitzProbe.abs_all_supports_and_nonzero',PRE+'abs_subgradient_negative'],['LipschitzProbe.linear_three_reverse',PRE+'affine_subdifferential'],['LipschitzSourceAudit.negative_constant_zero_dimension',PRE+'affine_convex']])
for pair in required:assert tuple(pair) in pairs,pair
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=28,proof_nodes=19,definition_nodes=9,owned_production_definitions=1,TEST_definitions=6,TEST_abbreviations=2,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-public-graph-v1.json'),required_value_pairs=required,ready_two_nodes_exactly_preserved=True,full_registry_export=False))
jobs={}
for label in ['retained-focused-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',fixed_headers=f['headers'],module_sha256=sha(PUBLIC),whole_canary_sha256=sha(CANARY),retained_proofs=1,retained_definitions=1,new_production_proofs=0,new_definitions=0,new_test_proofs=0,whole_canary_proofs=18,whole_canary_definitions=6,whole_canary_abbreviations=2,named_kernel_checks=28,named_kernel_axes=axes,native_guards=2,focused_jobs=jobs,selected_graph_nodes=28,selected_graph_direct_references=len(g['edges']),body_seconds=passed('public-body-v1-01')['elapsed_seconds'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('retained-body-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','LIPSCHITZ-RETAINED-BODY-V1','--lean',PUBLIC,'--statement-hash',f['headers']['theorem_2_30'],'--reused-declaration',PRE+'theorem_2_30','--reused-declaration',PRE+'SourceLipschitzOn','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--progress-class','retrieval-reuse','--notes','Actual1retainedproof1owneddefinition/whole18canaryproof6TESTdefs2abbrevs/28kernelchecks2guards/28selectednodes;0newmathTEST. Explicit NNReal source convention and negativeL0Dobstruction retained. BODY/packagepending; Chapterbookincomplete.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=PRE+n,statement_hash=h,state='retained exactbody compiled; distinctBODYpending') for n,h in f['headers'].items()],source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual1proof1definition/whole18canaryproof6TESTdefs2abbrevs/28kernelchecks2guards/28nodes',len(g['edges']),'refs PASS; distinctBODYpending.')
