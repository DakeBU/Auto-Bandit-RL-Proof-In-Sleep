from common_proving_v1 import *
import re

contract_bindings_fixed()
assert load(RUN/'canary-focused-build-v3-exit.json')['exit_code']==0
rows=load(CONTRACT/'targets-v2.json')['targets']
canary_names=['Tests.OnlineLearningCoreAudit.'+m.group(1) for m in
    re.finditer(r'^(?:theorem|def)\s+(\w+)',CANARY.read_text(encoding='utf8'),re.M)]
foundations=['FoundationsProbe.'+n for n in ['prefix_minimizers','instantiated_compare','strict_values',
    'zero_horizon','one_horizon','without_optimality','without_feasibility']]
fixtures=['Tests.OnlineGuessingIIDBenchmark.'+n for n in ['coinLaw','iidLaw','observation',
    'iidLaw_probability','observation_independent','observation_support','observation_sameLaw',
    'observation_mean','observation_variance','support_is_not_pointwise','lastPolicy_not_globally_bounded']]
names=[r['name'] for r in rows]+canary_names+foundations+fixtures+[PRE+'meanPredict',PRE+'empiricalMean']
old=(RUN/'typed-public-neutral-identities-v2.lean').read_text(encoding='utf8')
write(RUN/'actual-public-canary-types-kernel-v1.lean',
    'import Tests.OnlineLearningCoreAuditCanary\n'+old+'\n'+
    '\n'.join('#check '+n+'\n#print axioms '+n for n in canary_names+foundations+fixtures)+'\n')
gate('actual-public-canary-types-kernel-v1','lake','env','lean',RUN/'actual-public-canary-types-kernel-v1.lean')
log=(RUN/'actual-public-canary-types-kernel-v1.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
axioms=set()
for s in re.findall(r'depends on axioms: \[([^\]]*)\]',log):
    axioms.update(x.strip() for x in s.split(',') if x.strip())
assert axioms <= {'propext','Classical.choice','Quot.sound'}
prior=Path('runs/online-iid-success-20261008/export-compiled-body-graph-v1.lean').read_text(encoding='utf8')
prefix=prior[:prior.index('def targets')].replace('Tests.OnlineGuessingIIDSuccessCanary','Tests.OnlineLearningCoreAuditCanary')
rest=prior[prior.index('def moduleName'):].replace('Tests.OnlineGuessingIIDSuccessCanary','Tests.OnlineLearningCoreAuditCanary')
rest=rest.replace('Tests.OnlineGuessingIIDSuccess.instMeasurable','Tests.OnlineLearningCoreAudit.instMeasurable')
rest=rest.replace('Four frozen public proof values;14 actual canary proofs/2 fixturedefinitions; actual reused infinite-IID/private-tape laws and independence/probability declarations. Direct TYPE/VALUE occurrences only, not source coverage.',
    'Twelve unchanged old public proof values, original seven Foundations canaries and actual clipped infinite-IID/current-variance canaries. Direct TYPE/VALUE constant occurrences only; five source audits, no new production proofs or whole-source coverage.')
write(RUN/'export-compiled-body-graph-v1.lean',prefix+
    'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']\n\n'+rest)
gate('export-compiled-body-graph-v1','lake','env','lean','--run',RUN/'export-compiled-body-graph-v1.lean',RUN/'compiled-body-graph-v1.json')
g=load(RUN/'compiled-body-graph-v1.json');nodes={n['name']:n for n in g['nodes']}
prefix='Tests.OnlineLearningCoreAudit.'
required=[('FoundationsProbe.instantiated_compare',PRE+'lemma_1_2')]
for canary, public in [('outside_comparator_loss','expected_square_decomposition'),
    ('independent_coordinate_loss','independent_prediction_square'),('actual_mean_independent','meanPredict_independent'),
    ('actual_mean_measurable','meanPredict_measurable'),('actual_mean_memLp','meanPredict_memLp'),
    ('actual_mean_excess_identity','iid_meanPredict_excess'),('actual_mean_excess_nonnegative','iid_meanPredict_excess_nonneg'),
    ('actual_mean_optimal','source_mean_optimal'),('actual_history_independent','history_policy_independent'),
    ('actual_history_lower','history_policy_loss_ge_variance'),('positive_scalar_normalization','normalized_excess')]:
    required.append((prefix+canary,PRE+public))
required += [(PRE+'iid_meanPredict_excess',PRE+n) for n in ['independent_prediction_square','meanPredict_independent','meanPredict_memLp']]
required += [(PRE+'history_policy_loss_ge_variance',PRE+n) for n in ['independent_prediction_square','history_policy_independent']]
required += [(prefix+'nonidentical_current_variance_lower',PRE+'history_policy_loss_ge_variance'),
    (prefix+'actual_mean_two_round_excess',prefix+'actual_mean_excess_identity')]
for a,b in required: assert b in nodes[a]['value_dependencies'],(a,b)
for r in rows: assert nodes[r['name']]['kind']=='theorem' and nodes[r['name']]['has_value']
write(RUN/'actual-kernel-value-audit-v1.json',dict(actual_named_graph_nodes=len(g['nodes']),
    actual_TYPE_VALUE_occurrences=len(g['edges']),required_direct_VALUE_pairs=required,
    twelve_whole_Prop_identities=True,twelve_actual_public_proof_VALUE_instantiations=True,whole_meanPredict_Def_identity=True,
    actual_canary_theorems=sum(n['kind']=='theorem' for n in g['nodes'] if n['name'] in canary_names),
    test_only_fixture_definitions=sum(n['kind']=='definition' for n in g['nodes'] if n['name'] in canary_names),
    seven_original_foundations_canaries_reused=True,actual_axioms=sorted(axioms),sorryAx=False,
    public_files_sha256={p.as_posix():sha(p) for p in MODULES},canary_sha256=sha(CANARY),
    all_original_public_proof_header_bytes_unchanged=True,source_audits_pending=5,new_proofs=0,
    BODY_pending=True,chapter_complete=False,goal_complete=False))
contract_bindings_fixed()
print('Actual12 unchanged public proofVALUEs, neutraltype identities, original7 and new nondegenerate canaries, standard axioms and compiler VALUE graph passed; BODY/combined acceptance pending.')
