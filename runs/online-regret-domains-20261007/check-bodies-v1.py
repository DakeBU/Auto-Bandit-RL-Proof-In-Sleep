from common_v1 import *
fixed();old=load(CONTRACT/'existing-public-headers-v1.json');tests=load(CONTRACT/'planned-canary-headers-v1.json');defs=load(CONTRACT/'planned-test-definitions-v1.json')
proofnames=[PRE+n for n in old]+[TEST+n for n in tests]
names=proofnames+[PRE+'comparatorRegret',PRE+'NoRegret']+[TEST+n for n in defs]
write(RUN/'leaves/all-axioms-v1.lean','import Tests.OnlineLearningRegretDomainsCanary\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names))
gate('all-axioms-v1','lake','env','lean',RUN/'leaves/all-axioms-v1.lean')
log=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8');assert 'sorryAx' not in log
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(matched)==20
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
scratch=(RUN/'leaves/neutral-closed-props-v1.lean').read_text(encoding='utf-8')
identity='import Tests.OnlineLearningRegretDomainsCanary\n'+scratch+'\nuniverse u\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
generic={'comparatorRegret_eq_sum','noRegret_of_vanishing_bound','domain_gap_sum','restriction_commutes','loss_prefix','zero_horizon'}
for i,(n,h) in enumerate([*old.items(),*tests.items()],1):
 suffix='.{u}' if n in generic else ''
 identity+='example : Neutral.N%02d%s = propositionOf (@%s%s%s) := by rfl\n'%(i,suffix,PRE if n in old else TEST,n,suffix)
aliases={'comparatorRegret':'a','NoRegret':'b','embed':'c','sourceV':'d','outputW':'e','domainLoss':'f','output':'g','referenceOne':'h','referenceZero':'i','liftedComparators':'j'}
for n,a in aliases.items():
 suffix='.{u}' if n in ['comparatorRegret','NoRegret','embed'] else ''
 identity+='example : @Neutral.%s%s = @%s%s%s := by rfl\n'%(a,suffix,PRE if n in ['comparatorRegret','NoRegret'] else TEST,n,suffix)
write(RUN/'leaves/all-exact-types-v1.lean',identity)
gate('all-exact-types-v1','lake','env','lean',RUN/'leaves/all-exact-types-v1.lean')
template=Path('runs/online-ftl-state-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf-8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineLearningFTLStateCanary','Tests.OnlineLearningRegretDomainsCanary')
template=template.replace('Existing4Meanproof1def plus actual9newpublicproof3defs and6namedvalidationproof1testdef. Selected24 compiled nodes with direct type/VALUE constant occurrences; not whole registry, source inventory or teaching graph.','Existing2shared Regret proofs/2definitions plus8named validation proofs/8fixturedefinitions. Selected20compiled nodes with direct type/VALUE references; zero new production nodes; not the full shared registry or source inventory.')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==20
assert sum(x['kind']=='theorem' for x in graph['nodes'])==10 and sum(x['kind']=='definition' for x in graph['nodes'])==10
assert all(x['has_value'] for x in graph['nodes'])
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
pairs=load(CONTRACT/'proof-value-obligations-v1.json')['required_pairs']
for pair in pairs:assert tuple(pair) in actual,pair
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header,normalize_statement
fences=[]
for n,h in [*old.items(),*tests.items()]:
 path=PUBLIC if n in old else CANARY;full=(PRE if n in old else TEST)+n
 actualheader=lean_declaration_header(path,n);assert actualheader==normalize_statement(h),n
 fence=RUN/'full-header-fences-v1'/(n+'.json')
 native('full-fence-'+n+'-v1','statement-fence','--declaration',full,'--file',path,'--source-assumption',h,'--output',fence)
 native('full-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',path)
 assert load(fence)['statement']==actualheader
 fences.append(dict(name=full,path=fence.as_posix(),sha256=sha(fence),statement_hash=load(fence)['statement_hash']))
write(RUN/'full-fence-bindings-v1.json',fences)
write(RUN/'body-bindings-v1.json',dict(status='Actual8 typed named validation bodies compiled; owning public mathematical bytes unchanged; BODY pending',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),existing_public_proofs=2,existing_public_definitions=2,new_production_math=0,named_validation_proofs=8,test_definitions=8,named_kernel_checks=20,exact_proposition_identities=10,exact_definition_identities=10,axioms=axioms,selected_nodes=20,proof_nodes=10,definition_nodes=10,direct_references=len(graph['edges']),required_value_pairs=pairs,full_native_proof_fences=10,first_attempt_canary_bodies_compiled=True,preparation_universe_audit_failure_preserved=True,header_body_hashes_unchanged=True,BODY_review='pending',combined_reader_FINAL_native_PR='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--lean',CANARY,'--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reused-declaration',PRE+'comparatorRegret_eq_sum','--reused-declaration',PRE+'noRegret_of_vanishing_bound','--notes','Actual8typedcanaries/8fixturedefs,20namedkernel/10exactProps/10definition identities/10fullguards/3prespecifiedVALUE pairs. W/V modelmapping only;0newproductionmath; BODY/combined/reader/native/PR/chapter/Goal pending.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=(RUN/'body-bindings-v1.json').as_posix(),source_package_accepted=False,chapter_complete=False,goal_complete=False)))
fixed();print('Actual BODY checks complete; distinct BODY review pending.')
