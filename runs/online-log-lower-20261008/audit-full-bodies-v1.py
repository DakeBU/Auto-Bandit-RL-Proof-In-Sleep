from common_v1 import *
fixed()
assert load(RUN/'public-full-body-build-v1-exit.json')['exit_code']==0
assert load(RUN/'public-canary-build-v3-exit.json')['exit_code']==0
actual=load(RUN/'actual-public-canary-headers-v1.json')
index=load(RUN/'full-neutral-map-v2.json')
TEST='GuessingLogLowerProbe.'
pubdefs=re.findall(r'(?m)^(?:noncomputable )?def (\w+)\b',PUBLIC.read_text(encoding='utf-8'))
testdefs=re.findall(r'(?m)^(?:noncomputable )?def (\w+)\b',CANARY.read_text(encoding='utf-8'))
names=[x['name'] for x in actual]+[PRE+n for n in pubdefs]+[TEST+n for n in testdefs]
assert len(names)==76 and len(pubdefs)==10 and len(testdefs)==2
write(RUN/'leaves/all-axioms-v1.lean','import Tests.OnlineGuessingLogLowerCanary\n'+
      '\n'.join('#check '+n+'\n#print axioms '+n for n in names))
gate('all-axioms-v1','lake','env','lean',RUN/'leaves/all-axioms-v1.lean')
log=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8');assert 'sorryAx' not in log
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(matched)==76
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
identity='import Tests.OnlineGuessingLogLowerCanary\n'+(RUN/'full-neutral-packet-v2.lean').read_text(encoding='utf-8')
identity+='\nuniverse u\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
for row in index:
    suffix='.{u}' if row['polymorphic'] else ''
    identity+='example : NeutralContext.'+row['id']+suffix+' = propositionOf (@'+row['name']+suffix+') := by rfl\n'
for i,n in enumerate(pubdefs+testdefs,1):
    identity+='example : @NeutralContext.f'+str(i)+' = @'+(PRE if i<=10 else TEST)+n+' := by rfl\n'
write(RUN/'leaves/all-exact-types-v1.lean',identity)
gate('all-exact-types-v1','lake','env','lean',RUN/'leaves/all-exact-types-v1.lean')
template=Path('runs/online-regret-domains-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf-8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineLearningRegretDomainsCanary','Tests.OnlineGuessingLogLowerCanary')
template=template.replace('Existing2shared Regret proofs/2definitions plus8named validation proofs/8fixturedefinitions. Selected20compiled nodes with direct type/VALUE references; zero new production nodes; not the full shared registry or source inventory.',
    'Actual48 public proof bodies/10 model-component definitions and16 named validation proofs/2 fixtures. Selected76 compiled nodes with direct type/VALUE references. Private decomposition and imported dependencies appear as references; not a full registry or source-inventory count.')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==76
assert sum(x['kind']=='theorem' for x in graph['nodes'])==64
assert sum(x['kind']=='definition' for x in graph['nodes'])==12
assert all(x['has_value'] for x in graph['nodes'])
pairs=[
 ('prefix_distribution','pathWeight_nonneg'),('prefix_distribution','prefix_mass_one'),
 ('prefixMeasure_probability','prefix_distribution'),('pathExpectation_integral','prefix_distribution'),
 ('expected_heads','heads_succ'),('expected_heads_sq','heads_sq_succ'),
 ('expected_next_variance','expected_heads'),('expected_next_variance','expected_heads_sq'),
 ('pathLearnerLoss_cons','causalPredict_prefix'),('pathLearnerLoss_cons','causalPredict_cons_last'),
 ('expected_pathBestLoss','pathBestLoss_count'),('expected_pathBestLoss','expected_heads_sq'),
 ('expected_pathLearnerLoss_step','expected_next_variance'),
 ('expected_pathLearnerLoss_step','conditional_square_lower'),
 ('expected_pathRegret_lower','expected_pathLearnerLoss_lower'),
 ('expected_pathRegret_lower','expected_pathBestLoss'),
 ('expected_pathRegret_lower','pathRegret_eq_losses'),
 ('randomized_harmonic_lower','expected_pathRegret_lower'),
 ('randomized_harmonic_lower','pathRegret_integrable'),
 ('randomized_harmonic_lower','pathWeight_pos'),
 ('randomized_harmonic_lower','prefix_mass_one'),
 ('randomized_log_lower','randomized_harmonic_lower')]
required=[(PRE+a,PRE+b) for a,b in pairs]+[
 (PRE+'binary_mean_minimizer','BanditRL.OnlineLearning.empiricalMean_mem'),
 (PRE+'binary_mean_minimizer','BanditRL.OnlineLearning.empiricalMean_minimizes'),
 (PRE+'prefixMeasure_probability','BanditRLProof.Exp3.finiteActionMeasure_isProbabilityMeasure'),
 (PRE+'pathExpectation_integral','BanditRLProof.Exp3.integral_finiteActionMeasure_eq_sum'),
 (PRE+'randomized_log_lower','log_add_one_le_harmonic'),
 (TEST+'seeded_fixed_sequence_endpoint',PRE+'randomized_harmonic_lower'),
 (TEST+'seeded_log_endpoint',PRE+'randomized_log_lower'),
 (TEST+'deterministic_fixed_sequence_endpoint',PRE+'randomized_log_lower')]
edges={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in required:assert tuple(pair) in edges,pair
write(RUN/'required-value-pairs-v1.json',dict(required_pairs=required,
    status='actual compiled VALUE occurrences verified; not a teaching DAG'))
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header
fences=[]
for row in actual:
    n=row['name'].rsplit('.',1)[1];path=Path(row['path']);header=row['header']
    assert lean_declaration_header(path,n)==header,n
    label=('public-' if path==PUBLIC else 'canary-')+n
    fence=RUN/'full-header-fences-v1'/(label+'.json')
    native('full-fence-'+label+'-v1','statement-fence','--declaration',row['name'],
        '--file',path,'--source-assumption',header,'--output',fence)
    native('full-safe-'+label+'-v1','safe-verify','--fence',fence,'--lean-file',path)
    assert load(fence)['statement']==header
    fences.append(dict(name=row['name'],path=fence.as_posix(),sha256=sha(fence),
        statement_hash=load(fence)['statement_hash']))
write(RUN/'full-fence-bindings-v1.json',fences)
native('actual-public-lookup-v1','list-lean-decls','--statement',PRE)
native('actual-canary-lookup-v1','list-lean-decls','--include-tests','--statement',TEST)
write(RUN/'body-bindings-v1.json',dict(
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    frozen_proofs=16,actual_public_proofs=48,actual_public_definitions=10,
    named_validation_proofs=16,test_definitions=2,named_kernel_checks=76,
    exact_closed_proposition_identities=64,exact_definition_identities=12,
    axioms=axioms,selected_nodes=76,proof_nodes=64,definition_nodes=12,
    direct_references=len(graph['edges']),required_value_pairs=required,
    full_native_proof_fences=64,
    safe_verify_scope='Header hash/source substring/forbidden-token checks; DOES NOT compile Lean. Compilation independently bound by focused builds/kernel checks.',
    full_source_claim_terminal_proved=True,BODY_review='pending',
    combined_reader_FINAL_native_PR='pending',source_package_accepted=False,
    chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower',
    '--kind','build','--status','compiled','--run-id',RUN.name,'--lean',PUBLIC,
    '--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical',
    '--progress-class','terminal','--new-declaration',PRE+'randomized_log_lower',
    '--notes','All16 frozen targets closed by actual recursive law/moments/causal same-path loss/minimum and measurable bounded seed-integrability/fixed-sequence averaging producer. Actual76 kernel nodes,64 closed Prop identities,12 definition identities,64 native guards and30 VALUE pairs. Semantic BODY, integrated rootTests/harness/reader/FINAL and PR remain pending; no source/chapter/Goal acceptance.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate',
    '--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,
    body_bindings=(RUN/'body-bindings-v1.json').as_posix(),
    source_package_accepted=False,chapter_complete=False,goal_complete=False)))
fixed()
print('Actual body/kernel/definition/fence/VALUE gates complete; mandatory BODY review pending.')
