from common_v1 import *
fixed(proving=True)
old=load(CONTRACT/'existing-proof-headers-v1.json');new=load(CONTRACT/'new-public-headers-v1.json');plan=load(CONTRACT/'planned-canary-headers-v1.json')
proofnames=[PRE+n for n in [*old,*new]]+[TEST+n for n in plan]
names=proofnames+[PRE+'meanPredict',TEST+'probeTargets']
write(RUN/'public-named-declarations-v1.json',dict(existing_public_proofs=5,existing_public_definitions=1,new_public_proofs=2,new_public_definitions=0,new_named_test_proofs=6,new_test_definitions=1,names=names,named_checks=15,new_source_math_closures_pending_semantic_acceptance=2,chapter_complete=False,goal_complete=False))
imp='import Tests.OnlineLearningFTLSharpCanary\n'
write(RUN/'leaves/all-public-types-v1.lean',imp+'\n'.join('#check @'+n for n in names))
write(RUN/'leaves/all-axioms-v1.lean',imp+'\n'.join('#print axioms '+n for n in names))
gate('all-public-types-v1','lake','env','lean',RUN/'leaves/all-public-types-v1.lean')
gate('all-axioms-v1','lake','env','lean',RUN/'leaves/all-axioms-v1.lean')
axes=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8');assert 'sorryAx' not in axes
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",axes)
assert len(matched)==15 and {n for n,a in matched}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
neutral=(RUN/'leaves/neutral-closed-props-v1.lean').read_text(encoding='utf-8')
identity=imp+neutral+'\ndef propositionOf {P : Prop} (_ : P) : Prop := P\nexample : Neutral.a = BanditRL.OnlineLearning.empiricalMean := by rfl\nexample : Neutral.b = BanditRL.OnlineLearning.meanPredict := by rfl\nexample : Neutral.c = FTLSharpProbe.probeTargets := by rfl\n'
for x in load(RUN/'neutral-map-v1.json'):
 identity+='example : Neutral.'+x['neutral']+' = propositionOf (@'+x['actual']+') := by rfl\n'
write(RUN/'leaves/all-exact-types-v1.lean',identity)
gate('all-exact-types-v1','lake','env','lean',RUN/'leaves/all-exact-types-v1.lean')
template=Path('runs/online-foundations-public-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf-8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineLearningFoundationsCanary','Tests.OnlineLearningFTLSharpCanary').replace('Existing single Be-the-Leader proof plus seven new named validation tests; actual compiled TEST selected8 proof nodes, no public/source mathematical additions','Existing five FTL proofs and predictor plus two new source-bound proofs and six named validation proofs/one test definition. Selected15 actual compiled nodes; direct type/VALUE constant references, not whole registry or teaching graph.')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==15
assert sum(n['kind']=='theorem' for n in graph['nodes'])==13 and sum(n['kind']=='definition' for n in graph['nodes'])==2
assert all(n['has_value'] for n in graph['nodes'])
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in load(CONTRACT/'proof-value-obligations-v1.json')['required_pairs']:assert tuple(pair) in actual,pair
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
fences=[]
for n,h in [*old.items(),*new.items()]:
 actualheader=lean_declaration_header(PUBLIC,n)
 assert re.sub(r'\s+',' ',actualheader).strip()==re.sub(r'\s+',' ',h).strip(),n
 fence=RUN/'native-public-fences'/(n+'-v1.json')
 args=['statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence]
 if n in new:args+=['--source-assumption','(hy :']
 native('public-fence-'+n+'-v1',*args)
 assert load(fence)['statement_hash']==hashlib.sha256(actualheader.encode()).hexdigest()
 native('public-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC)
 fences.append(dict(name=PRE+n,path=fence.as_posix(),sha256=sha(fence),statement_hash=load(fence)['statement_hash']))
headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by\b)',CANARY.read_text(encoding='utf-8'))};assert headers==plan
for n in plan:
 fence=RUN/'native-canary-fences'/(n+'-v1.json')
 native('canary-fence-'+n+'-v1','statement-fence','--declaration',TEST+n,'--file',CANARY,'--output',fence)
 native('canary-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',CANARY)
 fences.append(dict(name=TEST+n,path=fence.as_posix(),sha256=sha(fence),statement_hash=load(fence)['statement_hash']))
write(RUN/'full-fence-bindings-v1.json',fences)
write(RUN/'body-bindings-v1.json',dict(status='Actual focused builds/15 named checks and axioms/13 exact proposition identities/13 full fences/9 prespecified direct VALUE pairs PASS',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),Tests_root_sha256=sha('Tests.lean'),existing_public_proofs=5,existing_public_definitions=1,new_public_math=2,new_public_definitions=0,new_named_test_proofs=6,new_test_definitions=1,named_kernel_checks=15,exact_proposition_identities=13,axioms=axioms,selected_nodes=15,proof_nodes=13,definition_nodes=2,direct_references=len(graph['edges']),required_value_pairs=load(CONTRACT/'proof-value-obligations-v1.json')['required_pairs'],full_native_fences=13,old_source_headers_and_bodies_unchanged=True,all_frozen_headers_unchanged=True,BODY_review='pending',combined_reader_FINAL_native_PR='pending',chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FTL-SHARP-BODIES-V1','--lean',PUBLIC,'--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--progress-class','closed-frontier','--new-declaration',PRE+'meanPredict_initial_stability','--new-declaration',PRE+'meanPredict_regret_refined','--notes','Two frozen maintext source-bound proofs and six validation proofs/one testdef compiled, actual13rfl/15kernelaxioms/13fences/9VALUE calls. Old5proof1def unchanged. Bounded terminals local; BODY/combined/reader/FINAL/native/PR/chapter/Goal pending.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=(RUN/'body-bindings-v1.json').as_posix(),source_package_accepted=False,new_public_math=2,new_named_test_proofs=6,chapter_complete=False,goal_complete=False)))
fixed(proving=True)
