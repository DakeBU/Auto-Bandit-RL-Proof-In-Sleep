from common_proving_v1 import *
import re

s = proving_fixed()
write(RUN/'safe-verify-helper-repair-v2.json', dict(
    failed_command_receipt='safe-verify-L1-v1-exit.json',
    failed_output='safe-verify-L1-v1.log',
    failure='The helper passed descriptive scope prose to a native option that checks literal normalized declaration-header premises. The statement hashes already matched; no mathematical assumption was removed.',
    repair='Bind native source-assumption fields to exact existing hypothesis lines. Retain all complete frozen-header hashes, compiled proof-value evidence, and the rejected v1 fence unchanged.',
    public_sha256=sha(PUBLIC), old_helper_sha256=sha(RUN/'audit-public-values-v1.py'),
    changed_production_or_frozen_contract=False))

for label in ['whole-public-types-axioms-v1', 'export-compiled-body-graph-v1']:
    receipt=load(RUN/(label+'-exit.json'))
    assert receipt['actual_exit']==0
    assert receipt['log_sha256']==sha(RUN/(label+'.log'))

canary=ROOT/'Tests/OnlineGuessingAECausalCanary.lean'
assert load(RUN/'canary-focused-v2-exit.json')['actual_exit']==0
assert canary.read_bytes()==(RUN/'canary-attempt-v2.lean.raw').read_bytes()
names=[t['name'] for t in s['targets']]
testprefix='Tests.OnlineGuessingAECausal.'
prefix='BanditRL.OnlineLearning.'
cnames=[testprefix+m.group(1) for m in re.finditer(r'^(?:theorem|def)\s+(\w+)',canary.read_text(encoding='utf8'),re.M)]
parents=[prefix+n for n in ['privateSeedPastInformation','private_seed_past_independent',
    'predictable_private_seed_independent','expectedFixedMinimum','expectedFixedRegret',
    'expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition']]
fixtures=['Tests.OnlineGuessingRandomizedIID.'+n for n in ['seededLaw','seed','target','seededLaw_probability',
    'seed_measurable','target_measurable','seed_has_coinLaw','target_has_coinLaw','target_sameLaw','target_support',
    'target_independent','seed_independent_whole_process','target_mean','target_variance']]
log=(RUN/'whole-public-types-axioms-v1.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
axioms={a.strip() for _, aa in rows for a in aa.split(',') if a.strip()}
assert axioms <= {'propext','Classical.choice','Quot.sound'}
assert set(names+cnames+parents+fixtures+['NeutralAECausal.wholePublicValue'+str(i) for i in range(1,4)]) <= {n for n,_ in rows}
g=load(RUN/'compiled-body-graph-v1.json')
nodes={n['name']:n for n in g['nodes']}
required=[(names[0],'Measurable.exists_eq_measurable_comp'),(names[0],'MeasureTheory.ae_all_iff'),
    (names[1],prefix+'predictable_private_seed_independent'),(names[1],'ProbabilityTheory.IndepFun.congr'),
    (names[2],names[1]),(names[2],prefix+'expectedFixedMinimum_eq_variance'),(names[2],prefix+'iid_cumulative_prediction_decomposition'),
    (testprefix+'actual_all_time_bounded_policy',names[0]),(testprefix+'actual_current_independence',names[1]),
    (testprefix+'actual_original_excess_identity',names[2]),(testprefix+'bad_is_not_pointwise_predictable','Measurable.factorsThrough'),
    (testprefix+'actual_nonzero_excess',testprefix+'actual_original_excess_identity')]
for a,b in required: assert b in nodes[a]['value_dependencies'],(a,b)
for name in names: assert nodes[name]['kind']=='theorem' and nodes[name]['has_value']

for t in s['targets']:
    assumptions=[line.strip() for line in t['header'].splitlines()
        if '(h' in line or '[IsProbabilityMeasure' in line]
    assert assumptions
    args=[]
    for a in assumptions: args.extend(['--source-assumption', a])
    p=RUN/('statement-fence-'+t['id']+'-v2.json')
    native('statement-fence-'+t['id']+'-v2','statement-fence','--declaration',t['name'],
        '--file',PUBLIC.relative_to(ROOT).as_posix(),*args,'--output',p)
    assert load(p)['statement_hash']==t['statement_hash']
    native('safe-verify-'+t['id']+'-v2','safe-verify','--fence',p,'--lean-file',PUBLIC.relative_to(ROOT).as_posix())
    assert json.loads((RUN/('safe-verify-'+t['id']+'-v2.log')).read_text(encoding='utf8'))['ok']

write(RUN/'actual-kernel-value-audit-v2.json',dict(
    actual_graph_nodes=len(g['nodes']),actual_TYPE_VALUE_occurrences=len(g['edges']),required_direct_VALUE_pairs=required,
    actual_named_axiom_outputs=len(rows),actual_unique_axiom_names=len(set(n for n,_ in rows)),
    actual_axioms=sorted(axioms),sorryAx=False,three_whole_public_type_VALUE_checks=True,
    public_source_sha256=sha(PUBLIC),canary_sha256=sha(canary),
    actual_test_theorems=sum(nodes[n]['kind']=='theorem' for n in cnames),test_only_definitions=sum(nodes[n]['kind']=='definition' for n in cnames),
    frozen_headers_unchanged=True,nondegenerate_AE_only_canary=True,
    reused_actual_compilation=['whole-public-types-axioms-v1','export-compiled-body-graph-v1'],
    native_fence_revision=2, BODY_combined_site_FINAL_acceptance_pending=True,
    accepted_local_obligations=0,remaining_local_obligations=3,chapter_complete=False,goal_complete=False))
proving_fixed()
print('Actual whole public types, proof values, standard axioms, direct VALUE dependencies and exact-premise fences passed',flush=True)
