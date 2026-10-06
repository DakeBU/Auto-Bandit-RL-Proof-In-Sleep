from common_v2 import *
f=fixed();r=bind_review('source-contract-receipt-v1.json','source-contract-inputs-v1.json','contract-binding-audit-v1.json')
event('stabilized',dict(contract_report_sha256=r['report_sha256'],frozen_headers=f['headers'],source_package_accepted=False))
write(RUN/'stabilized-leaf-selection-v1.json',dict(stage='stabilized',source_review=r['report_sha256'],selected_finite_leaves=f['proof_names'],owned_dependency='SourceFiniteMax and SourceActiveSubgradientUnion fully frozen/compiled',actual_ready_graph=sha(RUN/'compiled-ready-graph-v1.json'),terminal_mutations_allowed=False,allowed_edits='Versioned evidence and ordinary leading source/scope comment/only selected reader subtree after BODY; no original math/canary/shared/root/pin edit',source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('proving',dict(route='single actual finite max/support/compact hull/nearby support limit/strict separation route; ONE source terminal plus16supporting proof dependencies',allowed_math_mutations=False,source_package_accepted=False))
write(RUN/'30_lower_worker-v1.md','Actual SEVENTEEN retained proof bodies and TWO full owned definitions re-elaborated only after distinct CONTRACT. Actual max lifting and convex global supports; ambient continuity gives interior and local bounds, compact convex-join induction; near-point argmax/support choices and compact subsequence/repeated finite index produce active direction witness; actual separation and Riesz close FULL ordinaryhull equality. Whole19canaryproofs2TESTdefs unchanged. No newmath/tests/registrynodes/assumed oracle. All source/chapter/Goal gates separate.')

gate('public-body-v1-01','lake','env','lean',PUBLIC)
gate('public-canary-focused-v1-01','lake','build','Tests.OnlineSubgradientMaxCanary')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v2.lean',RUN/'compiled-public-graph-v1.json')
for n,h in f['headers'].items():
 p=RUN/'native-public-fences'/(n+'.json');native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC,'--lean-file',CANARY)
fixed();raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
q=load(RUN/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(set(q))==40 and {n for n,a in matches}==set(q)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==40 and {n['name'] for n in g['nodes']}==set(q) and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==36 and sum(n['kind']=='definition' for n in g['nodes'])==4
new={n['name']:n for n in g['nodes']};old=load(RUN/'compiled-ready-graph-v1.json');assert all(n==new[n['name']] for n in old['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};required=load(RUN/'ready-dependencies-v1.json')['required_value_pairs']
required.extend([['MaximumProbe.full_tie_hull_canary', 'BanditRL.OnlineConvex.theorem_2_26'], ['MaximumProbe.full_tie_interval_canary', 'MaximumProbe.full_tie_hull_canary'], ['MaximumProbe.mixture_and_rejection_canary', 'MaximumProbe.full_tie_interval_canary'], ['MaximumProbe.strict_active_canary', 'BanditRL.OnlineConvex.theorem_2_26'], ['MaximumExtendedProbe.singleton_extended_domain_canary', 'BanditRL.OnlineConvex.theorem_2_26']])
for pair in required:assert tuple(pair) in pairs,pair
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=40,proof_nodes=36,definition_nodes=4,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-public-graph-v1.json'),required_value_pairs=required,ready_nineteen_nodes_exactly_preserved=True,full_registry_export=False))
jobs={}
for label in ['retained-focused-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',fixed_headers=f['headers'],module_sha256=sha(PUBLIC),whole_canary_sha256=sha(CANARY),retained_proofs=17,retained_definitions=2,new_production_proofs=0,new_definitions=0,new_test_proofs=0,whole_canary_proofs=19,whole_canary_definitions=2,named_kernel_checks=40,named_kernel_axes=axes,native_guards=19,focused_jobs=jobs,selected_graph_nodes=40,selected_graph_direct_references=len(g['edges']),body_seconds=passed('public-body-v1-01')['elapsed_seconds'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('retained-body-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FINITE-MAX-RETAINED-BODIES-V1','--lean',PUBLIC,'--statement-hash',f['headers']['theorem_2_26'],'--reused-declaration',PRE+'theorem_2_26','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--progress-class','retrieval-reuse','--notes','Actual17retainedproofs2fullowneddefs/whole19canaryproof2TESTdefs/40namedkernel checks19guards/40selectednodes checked; no newmath/TEST. BODY/package gates pending; Chapter2/book incomplete.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=n,statement_hash=f['headers'][n],state='retained exact body compiled; distinctBODYpending') for n in f['proof_names']],owned_definition_full_body_fixed=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual17proof2owneddefs/whole19canaryproof2TESTdefs/40namedaxes19guards/40nodes',len(g['edges']),'refs PASS; distinctBODYpending.')
