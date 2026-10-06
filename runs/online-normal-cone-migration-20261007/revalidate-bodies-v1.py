from common import *
f=fixed();r=bind_review('source-contract-receipt-v1.json','source-contract-inputs-v1.json','contract-binding-audit-v1.json')
event('stabilized',dict(contract_report_sha256=r['report_sha256'],frozen_headers=f['headers'],source_package_accepted=False))
write(RUN/'stabilized-leaf-selection-v1.json',dict(stage='stabilized',source_review=r['report_sha256'],selected_finite_leaves=f['proof_names'],owned_dependency='SourceNormalCone fully frozen/compiled',actual_ready_graph=sha(RUN/'compiled-ready-graph-v1.json'),terminal_mutations_allowed=False,allowed_edits='Versioned evidence and ordinary leading source/scope comment/only selected reader subtree after BODY; no original math/canary/shared/root/pin edit',source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('proving',dict(route='single retained actual normal-cone producer route, three independent leaves sharing full N',allowed_math_mutations=False,source_package_accepted=False))
write(RUN/'30_lower_worker-v1.md','Actual THREE retained bodies and ONE full owned definition re-elaborated only after distinct CONTRACT. Indicator feasibility from properness/global support; actual ambient-ball contradiction; actual normalize-g/Cauchy/norm-sub-square gives full radiality and converse. WHOLE4canaryproofs+2TESTdefs unchanged; no newmath/TEST/registry node or supplied oracle. Package/chapter/Goal gates separate.')
gate('public-body-v1-01','lake','env','lean',PUBLIC)
gate('public-canary-focused-v1-01','lake','build','Tests.OnlineNormalConeCanary')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
for n,h in f['headers'].items():
 p=RUN/'native-public-fences'/(n+'.json');native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',p);assert load(p)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC,'--lean-file',CANARY)
fixed();raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
q=load(RUN/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==len(set(q))==10 and {n for n,a in matches}==set(q)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==10 and {n['name'] for n in g['nodes']}==set(q) and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==7 and sum(n['kind']=='definition' for n in g['nodes'])==3
new={n['name']:n for n in g['nodes']};old=load(RUN/'compiled-ready-graph-v1.json');assert all(n==new[n['name']] for n in old['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};required=load(RUN/'ready-dependencies-v1.json')['required_value_pairs']
required.extend([['NormalIndicatorProbe.interval_boundary_and_outside_canary',PRE+'indicator_subdifferential_eq_normalCone'],['NormalIndicatorProbe.thin_singleton_all_normals_canary',PRE+'indicator_subdifferential_eq_normalCone'],['NormalGeometryProbe.interval_interior_canary',PRE+'indicator_subdifferential_eq_normalCone'],['NormalGeometryProbe.interval_interior_canary',PRE+'normalCone_interior_eq_zero'],['NormalGeometryProbe.two_dimensional_unit_boundary_canary',PRE+'normalCone_unitBall_boundary'],['NormalGeometryProbe.two_dimensional_unit_boundary_canary','NormalGeometryProbe.e0'],['NormalGeometryProbe.two_dimensional_unit_boundary_canary','NormalGeometryProbe.e1']])
for pair in required:assert tuple(pair) in pairs,pair
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=10,proof_nodes=7,definition_nodes=3,direct_references=len(g['edges']),graph_sha256=sha(RUN/'compiled-public-graph-v1.json'),required_value_pairs=required,ready_four_nodes_exactly_preserved=True,full_registry_export=False))
jobs={}
for label in ['retained-focused-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m,label;jobs[label]=int(m.group(1))
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',fixed_headers=f['headers'],module_sha256=sha(PUBLIC),whole_canary_sha256=sha(CANARY),retained_proofs=3,retained_definitions=1,new_production_proofs=0,new_definitions=0,new_test_proofs=0,whole_canary_proofs=4,whole_canary_definitions=2,named_kernel_checks=10,named_kernel_axes=axes,native_guards=4,focused_jobs=jobs,selected_graph_nodes=10,selected_graph_direct_references=len(g['edges']),body_seconds=passed('public-body-v1-01')['elapsed_seconds'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('retained-body-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','NORMAL-CONE-RETAINED-BODIES-V1','--lean',PUBLIC,'--statement-hash',f['headers']['normalCone_unitBall_boundary'],'--reused-declaration',PRE+'normalCone_unitBall_boundary','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--progress-class','retrieval-reuse','--notes','Actual3retainedproofs1fullowneddef/whole4canaryproof2TESTdefs/10namedkernel checks4guards/10selectednodes checked; no newmath/TEST. BODY/package gates pending; Chapter2/book incomplete.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',required=[dict(name=n,statement_hash=f['headers'][n],state='retained exact body compiled; distinctBODYpending') for n in f['proof_names']],owned_definition_full_body_fixed=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual3proof1owneddef/whole4canaryproof2TESTdefs/10namedaxes4guards/10nodes',len(g['edges']),'refs PASS; distinctBODYpending.')
