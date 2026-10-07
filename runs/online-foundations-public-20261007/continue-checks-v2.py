from common_v1 import *
fixed(True)
plan=load(CONTRACT/'planned-canary-headers-v1.json')
names=[PRE+'lemma_1_2']+[TEST+n for n in plan]
write(RUN/'public-named-declarations-v1.json',dict(public_proofs=[PRE+'lemma_1_2'],new_test_proofs=names[1:],new_test_definitions=[],named_checks=len(names),new_public_math=0,new_source_math_closures=0))
imp='import Tests.OnlineLearningFoundationsCanary\n'
write(RUN/'leaves/all-public-types-v1.lean',imp+'\n'.join('#check @'+n for n in names))
write(RUN/'leaves/all-axioms-v1.lean',imp+'\n'.join('#print axioms '+n for n in names))
gate('all-public-types-v1','lake','env','lean',RUN/'leaves/all-public-types-v1.lean')
gate('all-axioms-v1','lake','env','lean',RUN/'leaves/all-axioms-v1.lean')
axes=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8');assert 'sorryAx' not in axes
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",axes)
assert len(matched)==8 and {n for n,a in matched}==set(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
neutral=(RUN/'leaves/neutral-closed-props-v2.lean').read_text(encoding='utf-8')
identity=imp+neutral+'''
universe u
def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.a = ChapterOneCase0.demoLoss := by rfl
example : Neutral.b = ChapterOneCase0.demoLeader := by rfl
'''
mapping=load(RUN/'neutral-map-v1.json')
for i,x in enumerate(mapping,1):
 poly=i in [1,5,6]
 identity+='example : Neutral.'+x['neutral']+('.{u}' if poly else '')+' = propositionOf (@'+x['actual']+('.{u}' if poly else '')+') := by rfl\n'
write(RUN/'leaves/all-exact-types-v1.lean',identity)
gate('all-exact-types-v1','lake','env','lean',RUN/'leaves/all-exact-types-v1.lean')
template=Path('runs/online-unit-scaling-public-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf-8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineUnitScalingCanary','Tests.OnlineLearningFoundationsCanary')
template=template.replace('Existing22 unit-scaling proof bodies/3 definitions/1 abbreviation and whole canary; compiled TEST environment selected62 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics','Existing single Be-the-Leader proof plus seven new named validation tests; actual compiled TEST selected8 proof nodes, no public/source mathematical additions')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==8 and all(n['kind']=='theorem' and n['has_value'] for n in graph['nodes'])
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in load(RUN/'value-pairs-before-first-export-v1.json')['required_pairs']:assert tuple(pair) in actual,pair
native('public-full-fence-v1','statement-fence','--declaration',PRE+'lemma_1_2','--file',PUBLIC,'--source-assumption','(hmin :','--source-assumption','(hmem : ∀ n, 0 < n → n ≤ T → leader n ∈ V)','--output',RUN/'native-public-full-fence-v1.json')
assert load(RUN/'native-public-full-fence-v1.json')['statement_hash']==fixed(True)['native_header_hash']
native('public-safe-v1','safe-verify','--fence',RUN/'native-public-full-fence-v1.json','--lean-file',PUBLIC,'--lean-file',CANARY)
headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by\b)',CANARY.read_text(encoding='utf-8'))}
assert headers==plan
for n in plan:
 fence=RUN/'native-canary-fences'/(n+'-v1.json')
 native('canary-fence-'+n+'-v1','statement-fence','--declaration',TEST+n,'--file',CANARY,'--output',fence)
 native('canary-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',CANARY)
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'focused-v2.log').read_text(encoding='utf-8'));assert jobs
write(RUN/'body-bindings-v1.json',dict(status='Actual focused/eight named types/all exact type identities/axiom audit/eight full fences/four direct VALUE pairs PASS',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),Tests_root_sha256=sha('Tests.lean'),existing_public_proofs=1,new_named_test_proofs=7,new_public_math=0,new_source_math_closures=0,new_production_registry_nodes=0,focused_jobs=int(jobs.group(1)),cached_jobs_included=True,named_kernel_checks=8,axes=axioms,selected_nodes=8,proof_nodes=8,definition_nodes=0,direct_references=len(graph['edges']),required_value_pairs=load(RUN/'value-pairs-before-first-export-v1.json')['required_pairs'],full_native_fences=8,source_statement_and_proof_unchanged=True,BODY_review='pending',combined_reader_FINAL_native_PR='pending',chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','FOUNDATIONS-PUBLIC-REUSE-V1','--lean',PUBLIC,'--statement-hash',fixed(True)['native_header_hash'],'--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reused-declaration',PRE+'lemma_1_2','--notes','Existing exact public proof retained; seven new named validation tests, no new public/source math. Eight full type/kernel/axiom/fences/four prespecified proof VALUE calls actual. BODY/combined/currentreader/FINAL/nativeaccepted/PR/chapter gates pending.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=(RUN/'body-bindings-v1.json').as_posix(),source_package_accepted=False,new_public_math=0,new_named_test_proofs=7,chapter_complete=False,goal_complete=False)))
fixed(True);print('Actual existing public + seven named validation bodies compiled; separate BODY/current integrated gates pending.')
