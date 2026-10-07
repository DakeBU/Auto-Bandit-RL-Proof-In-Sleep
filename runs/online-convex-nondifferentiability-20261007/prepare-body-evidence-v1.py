"""Fresh named/kernel/fence/value evidence for the actual new source terminal."""
from common_v4 import *
fixed(False,True);passed('public-body-v2-01');passed('public-canary-focused-v1-01')
contract=load(RUN/'source-contract-receipt-v2.json');resolutions={r['path']:r['resolved'] for r in load(RUN/'contract-native-prefix-bindings-v1.json')['rows'] if r['receipt'].endswith('v2.json')};bound=[]
for row in contract['reviewed_files']:
 p=row['path'];q=resolutions.get(p,p);assert sha(q)==row['sha256'];bound.append(dict(path=p,sha256=row['sha256'],resolved=q))
write(RUN/'prior-contract-bindings-v2.json',dict(status='passed',rows=bound,rejected_v1_preserved=True))
headers=load(CONTRACT/'headers.json');names=[PRE+n for n in headers]
tests=re.findall(r'^theorem\s+(\w+)',CANARY.read_text(encoding='utf-8'),re.M);assert len(tests)==5
targets=names+['ConvexNondiffProbe.'+n for n in tests];assert len(set(targets))==9
definition=(CONTRACT/'complete-definition.lean').read_text(encoding='utf-8');actual=PUBLIC.read_text(encoding='utf-8');full='def coordinateAbsolute (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|';assert full in definition and full in actual
write(RUN/'public-named-declarations-v1.json',dict(production=names,production_proofs=names[1:],production_definitions=names[:1],canary_proofs=['ConvexNondiffProbe.'+n for n in tests],canary_definitions=[],canary_abbreviations=[],axiom_probe=targets,unique_checks=9))
write(RUN/'leaves/actual-public-types-v1.lean','import Tests.OnlineConvexNondifferentiabilityCanary\n'+'\n'.join('#check @'+n for n in targets)+'\n#print '+PRE+'coordinateAbsolute')
write(RUN/'leaves/public-all-axioms-v1.lean','import Tests.OnlineConvexNondifferentiabilityCanary\n'+'\n'.join('#print axioms '+n for n in targets))
template=Path('runs/online-lipschitz-migration-20261007/leaves/export-public-dependencies-v1.lean').read_text(encoding='utf-8').replace('OnlineLipschitzSubgradientCanary','OnlineConvexNondifferentiabilityCanary')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in targets)+']'+template[end:]
template=template.replace('selected actual Lipschitz nodes','selected actual convex nondifferentiability nodes')
write(RUN/'leaves/export-public-dependencies-v1.lean',template)
generated('body-probes-before-first-use-v1.json',list((RUN/'leaves').glob('*v1.lean')))
gate('actual-public-types-v1-01','lake','env','lean',RUN/'leaves/actual-public-types-v1.lean')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 fence=RUN/('native-public-fences/'+n+'.json');native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence);assert load(fence)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC,'--lean-file',CANARY)
raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(matches)==9 and {n for n,a in matches}==set(targets)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==9 and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==8 and sum(n['kind']=='definition' for n in g['nodes'])==1
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[[PRE+'coordinate_absolute_convex','convexOn_univ_norm'],[PRE+'coordinate_absolute_convex','ConvexOn.comp_linearMap'],[PRE+'coordinate_absolute_not_differentiable','DifferentiableAt.comp'],[PRE+'coordinate_absolute_not_differentiable','not_differentiableAt_abs_zero'],[PRE+'convex_nondifferentiable_segment',PRE+'coordinate_absolute_convex'],[PRE+'convex_nondifferentiable_segment',PRE+'coordinate_absolute_not_differentiable']]
for n in ['closed_endpoints','nonzero_midpoint']:required.append(['ConvexNondiffProbe.'+n,PRE+'convex_nondifferentiable_segment'])
required.append(['ConvexNondiffProbe.axis_outside_segment',PRE+'coordinate_absolute_not_differentiable'])
for p in required:assert tuple(p) in pairs,p
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=9,proof_nodes=8,definition_nodes=1,direct_references=len(g['edges']),required_value_pairs=required,actual_producer_to_terminal_and_canary_pairs=True,full_registry_export=False))
m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v1-01.log').read_text(encoding='utf-8'));assert m
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',module_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),new_public_proofs=3,new_public_definitions=1,new_canary_proofs=5,canary_definitions=0,canary_abbreviations=0,named_type_checks=9,named_kernel_checks=9,axes=axes,native_guards=4,native_normalized_fingerprints=load(CONTRACT/'native-statement-fingerprints-v1.json'),raw_header_fingerprints=load(RUN/'draft-freeze-v1.json')['headers'],focused_jobs=int(m.group(1)),actual_source_terminal=PRE+'convex_nondifferentiable_segment',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','NONDIFF-BODY-V2','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['convex_nondifferentiable_segment'],'--new-declaration',PRE+'convex_nondifferentiable_segment','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--harness','hierarchical','--progress-class','compiled-leaf','--notes','New actualsource exact2Dconvex+ALLclosedsegment ambientfailure terminal with real producer leaves,5nondegeneratecanaries,9standardkernel4guards/actualvaluegraph. CONTRACTM1repairedseparately; BODY/combined/site/FINAL/native/PRpending, cardinalityrequiredseparate.')
write(RUN/'proof-obligations-proving-v2.json',dict(stage='proving',terminal=dict(name=PRE+'convex_nondifferentiable_segment',state='actual bodycompiled, BODYreviewpending'),source_package_accepted=False,chapter_complete=False,goal_complete=False,required_cardinality='separate formal uncountability terminal planned'))
fixed(False,True);print('Actual3newpublicproofs/1def/5canaryproofs/9kernel4guards/9nodevaluegraph:',len(g['edges']),'refs. BODYpending.')
