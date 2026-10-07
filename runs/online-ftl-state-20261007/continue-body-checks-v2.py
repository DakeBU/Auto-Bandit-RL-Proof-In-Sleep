from common_v1 import *
fixed(proving=True)
old=load(CONTRACT/'existing-Mean-headers-v1.json');new=load(CONTRACT/'new-public-headers-v1.json');tests=load(CONTRACT/'planned-canary-headers-v1.json');defs=load(CONTRACT/'production-definitions-v1.json')
proofnames=[PRE+n for n in [*old,*new]]+[TEST+n for n in tests]
names=proofnames+[PRE+'empiricalMean']+[PRE+n for n in defs]+[TEST+'probeTargets']
axes=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8')
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",axes)
assert len(matched)==24
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert load(RUN/'all-exact-types-v2-exit.json')['exit_code']==0
template=Path('runs/online-ftl-sharp-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf-8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineLearningFTLSharpCanary','Tests.OnlineLearningFTLStateCanary')
template=template.replace('Existing five FTL proofs and predictor plus two new source-bound proofs and six named validation proofs/one test definition. Selected15 actual compiled nodes; direct type/VALUE constant references, not whole registry or teaching graph.','Existing4Meanproof1def plus actual9newpublicproof3defs and6namedvalidationproof1testdef. Selected24 compiled nodes with direct type/VALUE constant occurrences; not whole registry, source inventory or teaching graph.')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==24
assert sum(x['kind']=='theorem' for x in graph['nodes'])==19 and sum(x['kind']=='definition' for x in graph['nodes'])==5
assert all(x['has_value'] for x in graph['nodes'])
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
pairs=load(CONTRACT/'proof-value-obligations-v1.json')['required_pairs']
for pair in pairs:assert tuple(pair) in actual,pair
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header,normalize_statement
fences=[]
for n,h in [*old.items(),*new.items(),*tests.items()]:
 path=CANARY if n in tests else MEAN if n in old or n=='empiricalMean_succ' else PUBLIC
 full=(TEST if n in tests else PRE)+n
 actualheader=lean_declaration_header(path,n);assert actualheader==normalize_statement(h),n
 fence=RUN/'full-header-fences-v1'/(n+'.json')
 native('full-fence-'+n+'-v1','statement-fence','--declaration',full,'--file',path,'--source-assumption',h,'--output',fence)
 native('full-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',path)
 assert load(fence)['statement']==actualheader
 fences.append(dict(name=full,path=fence.as_posix(),sha256=sha(fence),statement_hash=load(fence)['statement_hash']))
write(RUN/'full-fence-bindings-v1.json',fences)
assert re.findall(r'(?m)^theorem (\w+)\b',PUBLIC.read_text(encoding='utf-8'))==[n for n in new if n!='empiricalMean_succ']
assert re.findall(r'(?m)^theorem (\w+)\b',MEAN.read_text(encoding='utf-8'))==[*old,'empiricalMean_succ']
assert re.findall(r'(?m)^theorem (\w+)\b',CANARY.read_text(encoding='utf-8'))==list(tests)
for n,d in defs.items():assert PUBLIC.read_text(encoding='utf-8').count(d)==1,n
write(RUN/'body-bindings-v1.json',dict(status='Actual9 public production proof bodies and6 canaries compiled; central recursive producer terminal closed locally',Mean_sha256=sha(MEAN),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),public_root_sha256=sha('BanditRLProof.lean'),Tests_root_sha256=sha('Tests.lean'),existing_Mean_proofs=4,existing_Mean_definitions=1,new_public_proofs=9,new_public_definitions=3,new_named_validation_proofs=6,new_test_definitions=1,source_subobligation_count=2,named_kernel_checks=24,exact_proposition_identities=19,identity_method='Exact whole-function neutral-state equality by extensional Nat induction, remaining function identities rfl; propositions unfold/rewrite that proved equality then rfl. No recursive rfl or unsupported native recursion-fence claim.',axioms=axioms,selected_nodes=24,proof_nodes=19,definition_nodes=5,direct_references=len(graph['edges']),required_value_pairs=pairs,full_native_proof_fences=19,raw_full_definitions_preserved=True,old_Mean_headers_and_bodies_unchanged=True,all_frozen_headers_unchanged=True,first_attempt_Lean_production_bodies=True,actual_failed_definition_rfl_and_guard_layout_invocations_retained=True,BODY_review='pending',combined_reader_FINAL_native_PR='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-STATE-BODIES-V1','--lean',PUBLIC,'--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--progress-class','closed-frontier','--new-declaration',PRE+'ftlState_eq_predict','--reused-declaration',PRE+'empiricalMean_mem','--notes','Actual central producer terminal closed from genuine local recursion/alltime mean recurrence;9newpublicproof3defs,6validationproof1def,24namedkernel/19exactprops/19fullguards/16prespecifiedVALUE calls. Sourcepackage/BODY/rootTests/fullharness/readerFINAL/native/PR/chapter/Goal pending.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=(RUN/'body-bindings-v1.json').as_posix(),source_package_accepted=False,chapter_complete=False,goal_complete=False)))
fixed(proving=True)
