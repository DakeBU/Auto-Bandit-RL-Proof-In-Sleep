"""Re-elaborate the real retained producers after distinct source CONTRACT review."""
from common_v2 import *
f=fixed();r=bind_review('source-contract-receipt-v1.json','source-contract-inputs-v1.json','contract-binding-audit-v1.json')
assert load(RUN/'prior-contract-binding-v1.json')['status']=='passed'
event('stabilized',dict(contract_report_sha256=r['report_sha256'],frozen_headers=f['headers'],source_package_accepted=False))
write(RUN/'stabilized-leaf-selection-v1.json',dict(stage='stabilized',source_review=r['report_sha256'],selected_finite_leaves=f['proof_names'],owned_dependency='Two complete actual hinge/Bool affine definitions frozen/compiled',actual_ready_graph=sha(RUN/'compiled-ready-graph-v1.json'),terminal_mutations_allowed=False,allowed_edits='Versioned evidence, ordinary leading source/scope comment and only online-hinge reader subtrees after BODY; no original mathematics/canary/shared/root/pin edit',source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('proving',dict(route='single actual affine support/two-component maximum/active sign/ordinary segment route; ONE body example THREE branches with twelve foundations',allowed_math_mutations=False,source_package_accepted=False))
write(RUN/'30_lower_worker-v1.md','Actual THIRTEEN retained proof bodies and TWO complete owned definitions re-elaborated after distinct CONTRACT. Every-y affine supporting inequalities/inner positivity give full singleton; actual two affine proper/convex/finite/continuous components and Bool maximum identity instantiate complete Theorem2.26; actual sign classification and ordinary pair hull produce both inclusions of all three branches. Whole FIVE unchanged scalar canaries/zero new math or TEST nodes. Compilation not source/chapter/Goal acceptance.')
gate('public-body-v1-01','lake','env','lean',PUBLIC)
gate('public-canary-focused-v1-01','lake','build','Tests.OnlineHingeCanary')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
for n,h in f['headers'].items():
 p=RUN/'native-public-fences'/(n+'.json');native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC,'--lean-file',CANARY)
fixed();raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
q=load(RUN/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(set(q))==20 and {n for n,a in matches}==set(q)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==20 and {n['name'] for n in g['nodes']}==set(q) and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==18 and sum(n['kind']=='definition' for n in g['nodes'])==2
new={n['name']:n for n in g['nodes']};old=load(RUN/'compiled-ready-graph-v1.json');assert all(n==new[n['name']] for n in old['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};required=load(RUN/'ready-dependencies-v1.json')['required_value_pairs']
required.extend([['HingeProbe.'+n,PRE+'example_2_27'] for n in ['strict_zero','strict_slope','boundary_interval','zero_vector']]+[['HingeProbe.actual_mixture_and_rejection','HingeProbe.boundary_interval'],['HingeProbe.actual_mixture_and_rejection',PRE+'hinge_active_zero']])
for pair in required:assert tuple(pair) in pairs,pair
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=20,proof_nodes=18,definition_nodes=2,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-public-graph-v1.json'),required_value_pairs=required,ready_fifteen_nodes_exactly_preserved=True,full_registry_export=False))
jobs={}
for label in ['retained-focused-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',fixed_headers=f['headers'],module_sha256=sha(PUBLIC),whole_canary_sha256=sha(CANARY),retained_proofs=13,retained_definitions=2,new_production_proofs=0,new_definitions=0,new_test_proofs=0,whole_canary_proofs=5,whole_canary_definitions=0,named_kernel_checks=20,named_kernel_axes=axes,native_guards=15,focused_jobs=jobs,selected_graph_nodes=20,selected_graph_direct_references=len(g['edges']),body_seconds=passed('public-body-v1-01')['elapsed_seconds'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('retained-body-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','HINGE-RETAINED-BODIES-V1','--lean',PUBLIC,'--statement-hash',f['headers']['example_2_27'],'--reused-declaration',PRE+'example_2_27','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--progress-class','retrieval-reuse','--notes','Actual13retainedproofs2fullowneddefs/whole5canaryproofs/20namedkernelchecks15guards/20selectednodes; zero newmath/TEST. BODY/package gates pending; chapter/book incomplete.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=n,statement_hash=f['headers'][n],state='retained exact body compiled; distinct BODY pending') for n in f['proof_names']],owned_definition_full_body_fixed=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual13proofs2owneddefs/whole5canaryproofs/20kernelaxes15guards/20nodes',len(g['edges']),'refs PASS; distinctBODYpending.')
