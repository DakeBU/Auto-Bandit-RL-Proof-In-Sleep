from common_reviewed_v1 import *
import re
headers_fixed(4)
assert load(RUN/'canary-focused-build-v1-exit.json')['exit_code']==0
rows=load(CONTRACT/'targets-v1.json')['targets']
draft=(CONTRACT/'public-context-v1.lean').read_text(encoding='utf8')
neutral=(CONTRACT/'neutral-context-v1.lean').read_text(encoding='utf8')
text='import Tests.OnlineGuessingIIDSuccessCanary\n'+draft.replace(
    'import BanditRLProof.OnlineGuessingRandomizedIID\n','')
text+=neutral.replace('import Mathlib\n','').replace('universe u v w z\n','')
text+='\nopen BanditRL.OnlineLearning NeutralLimit\n'
for i,row in enumerate(rows,1):
    levels='' if i==1 else ('.{u, v}' if i==2 else '.{u}')
    text+='example : S00'+str(i)+levels+' = Q00'+str(i)+levels+' := rfl\n'
    text+='example : S00'+str(i)+levels+' := @'+row['name']+levels+'\n'
text+='example : @C0.{u} = @expectedFixedMinimum.{u} := rfl\n'
text+='example : @C1.{u} = @expectedFixedRegret.{u} := rfl\n'
text+='example : C2 = meanPredict := rfl\n'
canary_text=CANARY.read_text(encoding='utf8')
canary_names=['Tests.OnlineGuessingIIDSuccess.'+m.group(1) for m in
    re.finditer(r'^(?:theorem|def)\s+(\w+)',canary_text,re.M)]
reused=[PRE+n for n in ['expectedFixedMinimum','expectedFixedRegret','expectedFixedMinimum_eq_variance',
    'expected_fixed_prefix_decomposition','meanPredict_expectedFixed_excess',
    'randomized_history_policy_expectedFixed_excess','theorem_1_3','empiricalMean_minimizes','meanPredict','empiricalMean']]
fixtures=['Tests.OnlineGuessingIIDBenchmark.'+n for n in
    ['coinLaw','iidLaw','observation','iidLaw_probability','observation_independent',
     'observation_support','observation_sameLaw','meanPredict_two_round_excess']]
fixtures+=['Tests.OnlineGuessingRandomizedIID.'+n for n in
    ['seededLaw','seed','target','seedBit','seededLaw_probability','seed_independent_whole_process','target_independent']]
names=[r['name'] for r in rows]+canary_names+reused+fixtures
text+='\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
write(RUN/'actual-public-canary-types-kernel-v1.lean',text)
gate('actual-public-canary-types-kernel-v1','lake','env','lean',RUN/'actual-public-canary-types-kernel-v1.lean')
log=(RUN/'actual-public-canary-types-kernel-v1.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
axioms=set()
for s in re.findall(r'depends on axioms: \[([^\]]*)\]',log):
    axioms.update(x.strip() for x in s.split(',') if x.strip())
assert axioms<=set(['propext','Classical.choice','Quot.sound'])
old=Path('runs/online-randomized-iid-20261008/leaves/export-compiled-body-graph-v2.lean').read_text(encoding='utf8')
prefix=old[:old.index('def targets')].replace('Tests.OnlineGuessingRandomizedIIDCanary','Tests.OnlineGuessingIIDSuccessCanary')
rest=old[old.index('def moduleName'):]
rest=rest.replace('Tests.OnlineGuessingRandomizedIIDCanary','Tests.OnlineGuessingIIDSuccessCanary').replace(
    'Tests.OnlineGuessingRandomizedIID.instMeasurable','Tests.OnlineGuessingIIDSuccess.instMeasurable')
scope='Four frozen public proof values;14 actual canary proofs/2 fixturedefinitions; actual reused infinite-IID/private-tape laws and independence/probability declarations. Direct TYPE/VALUE occurrences only, not source coverage.'
start=rest.index('Seven frozen public producer/interface proofs')
end=rest.index('"',start)
rest=rest[:start]+scope+rest[end:]
graph=prefix+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']\n\n'+rest
write(RUN/'export-compiled-body-graph-v1.lean',graph)
gate('export-compiled-body-graph-v1','lake','env','lean','--run',RUN/'export-compiled-body-graph-v1.lean',
    RUN/'compiled-body-graph-v1.json')
g=load(RUN/'compiled-body-graph-v1.json')
node_map={n['name']:n for n in g['nodes']}
required=[
    (PRE+'centered_total_sublinear_iff_average',PRE+'normalized_excess'),
    (PRE+'randomized_history_policy_success_iff',PRE+'centered_total_sublinear_iff_average'),
    (PRE+'randomized_history_policy_success_iff',PRE+'randomized_history_policy_expectedFixed_excess'),
    (PRE+'meanPredict_expectedFixed_upper',PRE+'theorem_1_3'),
    (PRE+'meanPredict_expectedFixed_upper',PRE+'empiricalMean_minimizes'),
    (PRE+'meanPredict_expectedFixed_upper',PRE+'expected_fixed_prefix_decomposition'),
    (PRE+'meanPredict_iid_success',PRE+'meanPredict_expectedFixed_upper'),
    (PRE+'meanPredict_iid_success',PRE+'meanPredict_expectedFixed_excess'),
    (PRE+'meanPredict_iid_success',PRE+'centered_total_sublinear_iff_average'),
    ('Tests.OnlineGuessingIIDSuccess.actual_meanPredict_success',PRE+'meanPredict_iid_success'),
    ('Tests.OnlineGuessingIIDSuccess.actual_meanPredict_upper',PRE+'meanPredict_expectedFixed_upper'),
    ('Tests.OnlineGuessingIIDSuccess.persistent_policy_not_successful',PRE+'randomized_history_policy_success_iff'),
    ('Tests.OnlineGuessingIIDSuccess.nonzero_initial_total_sublinear',PRE+'centered_total_sublinear_iff_average'),
    ('Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_upper',PRE+'meanPredict_expectedFixed_upper')]
for a,b in required:
    assert b in node_map[a]['value_dependencies'],(a,b)
write(RUN/'actual-kernel-graph-audit-v1.json',dict(actual_lean_exit=0,
    public_VALUE_type_instantiations=4,whole_neutral_Prop_identities=4,whole_Def_identities=3,
    named_canary_theorems=14,canary_Def_values=2,named_kernel_checks=len(names),
    compiler_graph_nodes=len(g['nodes']),actual_TYPE_VALUE_occurrences=len(g['edges']),
    required_direct_VALUE_pairs=required,actual_axioms=sorted(axioms),sorryAx=False,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),headers_unchanged=True,
    BODY_and_combined_gates_pending=True,chapter_complete=False,goal_complete=False))
for row in rows:
    # Production fences already recorded per leaf; actual compiledVALUE audit above is additional.
    assert node_map[row['name']]['kind']=='theorem' and node_map[row['name']]['has_value']
write(RUN/'body-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    frozen_targets_sha256=sha(CONTRACT/'targets-v1.json'),kernel_audit_sha256=sha(RUN/'actual-kernel-graph-audit-v1.json'),
    compiled_bounded_terminals=4,remaining_bounded_math_terminals=0,
    source_objects_C1=16,required_proof_leaf_total_C1=None,
    package_accepted=False,chapter_complete=False,goal_complete=False))
headers_fixed(4)
print('Four actualpublicVALUEs,4wholeProp/3Def identities,14canaryproofs, compiled TYPE/VALUE graph and required14 VALUE pairs; standard axioms only. BODY/combined gates pending.')
