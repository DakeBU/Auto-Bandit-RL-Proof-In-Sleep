"""After distinct CONTRACT, re-elaborate the actual full affine producer and all old canaries."""
from common_v2 import *
f=fixed();r=bind_review('source-contract-receipt-v1.json','source-contract-inputs-v1.json','contract-binding-audit-v1.json')
assert load(RUN/'prior-contract-binding-v1.json')['status']=='passed'
event('stabilized',dict(contract_report_sha256=r['report_sha256'],frozen_headers=f['headers'],source_package_accepted=False))
write(RUN/'stabilized-leaf-selection-v1.json',dict(stage='stabilized',source_review=r['report_sha256'],selected_finite_leaves=['theorem_2_28'],actual_ready_graph=sha(RUN/'compiled-ready-graph-v1.json'),terminal_mutations_allowed=False,allowed_edits='Versioned evidence, ordinary leading comment and only online-affine-subgradient reader subtrees after BODY; no mathematics/canary/shared/root/pin edit',source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('proving',dict(route='single actual global support / affine cancellation / actual adjoint route',allowed_math_mutations=False,source_package_accepted=False))
write(RUN/'30_lower_worker-v1.md','ONE retained actual theorem body re-elaborated after distinct CONTRACT. Fullimagewitnessg -> actual hg(Ay+b) everyy -> actual map_sub/translationcancellation -> actual adjoint_inner_left -> EReal support. Sourceproper retained though algebraically unused. WHOLE7oldscalarcanaryproof2TESTdefs fixed,0newmath/TEST. Compiler success is not source/chapter/Goal acceptance.')
gate('public-body-v1-01','lake','env','lean',PUBLIC)
gate('public-canary-focused-v1-01','lake','build','Tests.OnlineAffineSubgradientCanary')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
p=RUN/'native-public-fences/theorem_2_28.json';native('public-fence-theorem_2_28-v1','statement-fence','--declaration',PRE+'theorem_2_28','--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==f['headers']['theorem_2_28']
native('public-safe-theorem_2_28-v1','safe-verify','--fence',p,'--lean-file',PUBLIC,'--lean-file',CANARY)
fixed();raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
q=load(RUN/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(set(q))==10 and {n for n,a in matches}==set(q)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==10 and {n['name'] for n in g['nodes']}==set(q) and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==8 and sum(n['kind']=='definition' for n in g['nodes'])==2
new={n['name']:n for n in g['nodes']};old=load(RUN/'compiled-ready-graph-v1.json');assert all(n==new[n['name']] for n in old['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};required=list(load(RUN/'ready-dependencies-v1.json')['required_value_pairs'])
required.extend([['AffineProbe.double_adjoint','ContinuousLinearMap.adjoint_inner_left'],['AffineProbe.nonzero_shifted_support',PRE+'theorem_2_28'],['AffineProbe.nonzero_shifted_support','AffineProbe.absolute_proper'],['AffineProbe.nonzero_shifted_support','AffineProbe.double_adjoint'],['AffineProbe.nonzero_shifted_support',PRE+'abs_subgradient_zero'],['AffineProbe.proper_nonconvex_strict_inclusion',PRE+'theorem_2_28'],['AffineProbe.proper_nonconvex_strict_inclusion','AffineProbe.neg_abs_proper'],['AffineProbe.proper_nonconvex_strict_inclusion','AffineProbe.neg_abs_support_empty'],['AffineProbe.proper_nonconvex_strict_inclusion','AffineProbe.neg_abs_not_convex'],['AffineProbe.proper_nonconvex_strict_inclusion',PRE+'affine_subdifferential']])
for pair in required:assert tuple(pair) in pairs,pair
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=10,proof_nodes=8,definition_nodes=2,definitions_are_TEST_only=True,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-public-graph-v1.json'),required_value_pairs=required,ready_single_node_exactly_preserved=True,full_registry_export=False))
jobs={}
for label in ['retained-focused-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',fixed_headers=f['headers'],module_sha256=sha(PUBLIC),whole_canary_sha256=sha(CANARY),retained_proofs=1,retained_definitions=0,new_production_proofs=0,new_definitions=0,new_test_proofs=0,whole_canary_proofs=7,whole_canary_definitions=2,named_kernel_checks=10,named_kernel_axes=axes,native_guards=1,focused_jobs=jobs,selected_graph_nodes=10,selected_graph_direct_references=len(g['edges']),body_seconds=passed('public-body-v1-01')['elapsed_seconds'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('retained-body-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','AFFINE-RETAINED-BODY-V1','--lean',PUBLIC,'--statement-hash',f['headers']['theorem_2_28'],'--reused-declaration',PRE+'theorem_2_28','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--progress-class','retrieval-reuse','--notes','Actual ONE retained full affine inclusion producer/whole7canaryproof2TESTdefs/10namedkernelchecks1guard/10selectednodes;0newmath/TEST. Sourceproper retained/no convexity/equality strengthening. BODY/package gatespending; Chapterbook incomplete.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=PRE+'theorem_2_28',statement_hash=f['headers']['theorem_2_28'],state='retained exactbody compiled; distinctBODYpending')],source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual1proof/whole7canaryproof2TESTdefs/10kernelchecks1guard/10nodes',len(g['edges']),'refs PASS; distinctBODYpending.')
