from common_proving_v1 import *
import re
s=proving_fixed()
assert load(RUN/'leaf-L3-attempt-v1.json')['actual_exit']==0
assert load(RUN/'canary-focused-v2-exit.json')['actual_exit']==0
canary=ROOT/'Tests/OnlineGuessingAECausalCanary.lean'
assert canary.read_bytes()==(RUN/'canary-attempt-v2.lean.raw').read_bytes()
targets=s['targets'];prefix='BanditRL.OnlineLearning.';testprefix='Tests.OnlineGuessingAECausal.'
names=[t['name'] for t in targets]
cnames=[testprefix+m.group(1) for m in re.finditer(r'^(?:theorem|def)\s+(\w+)',canary.read_text(encoding='utf8'),re.M)]
parents=[prefix+n for n in ['privateSeedPastInformation','private_seed_past_independent',
    'predictable_private_seed_independent','expectedFixedMinimum','expectedFixedRegret',
    'expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition']]
fixtures=['Tests.OnlineGuessingRandomizedIID.'+n for n in ['seededLaw','seed','target','seededLaw_probability',
    'seed_measurable','target_measurable','seed_has_coinLaw','target_has_coinLaw','target_sameLaw','target_support',
    'target_independent','seed_independent_whole_process','target_mean','target_variance']]
typetext='import Tests.OnlineGuessingAECausalCanary\nopen MeasureTheory ProbabilityTheory BanditRL.OnlineLearning\nuniverse u v\nnamespace NeutralAECausal\n'
for i,t in enumerate(targets,1):
    rest=t['header'].split(t['name'].split('.')[-1],1)[1].strip().replace(' :\n', ',\n', 1)
    typetext+='def Q'+str(i)+' : Prop := ∀ '+rest+'\n\n'
    typetext+='theorem wholePublicValue'+str(i)+' : Q'+str(i)+' := @'+t['name']+'\n\n'
    typetext+='#check wholePublicValue'+str(i)+'\n#print axioms wholePublicValue'+str(i)+'\n'
typetext+='end NeutralAECausal\n\n'+ '\n'.join('#check '+n+'\n#print axioms '+n for n in names+cnames+parents+fixtures)+'\n'
write(RUN/'whole-public-types-axioms-v1.lean',typetext)
gate('whole-public-types-axioms-v1','lake','env','lean',RUN/'whole-public-types-axioms-v1.lean')
log=(RUN/'whole-public-types-axioms-v1.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
actual_axiom_rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
axioms={x.strip() for _,a in actual_axiom_rows for x in a.split(',') if x.strip()}
assert axioms<={'propext','Classical.choice','Quot.sound'}
assert set(names+cnames+parents+fixtures+['NeutralAECausal.wholePublicValue'+str(i) for i in range(1,4)]) <= {n for n,_ in actual_axiom_rows}
allnames=names+cnames+parents+fixtures
old=(ROOT/'runs/online-c1-core-audit-20261008/export-compiled-body-graph-v1.lean').read_text(encoding='utf8')
head=old[:old.index('def targets')].replace('Tests.OnlineLearningCoreAuditCanary','Tests.OnlineGuessingAECausalCanary')
rest=old[old.index('def moduleName'):].replace('Tests.OnlineLearningCoreAuditCanary','Tests.OnlineGuessingAECausalCanary').replace('Tests.OnlineLearningCoreAudit.instMeasurable','Tests.OnlineGuessingAECausal.instMeasurable')
rest=rest.replace('Twelve unchanged old public proof values, original seven Foundations canaries and actual clipped infinite-IID/current-variance canaries. Direct TYPE/VALUE constant occurrences only; five source audits, no new production proofs or whole-source coverage.',
    'Three exact AE causal public proof bodies, actual AE-only non-pointwise canaries and reused independent private seed/infinite IID laws. Direct TYPE/VALUE constants only, not chapter/source coverage.')
write(RUN/'export-compiled-body-graph-v1.lean',head+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in allnames)+']\n\n'+rest)
gate('export-compiled-body-graph-v1','lake','env','lean','--run',RUN/'export-compiled-body-graph-v1.lean',RUN/'compiled-body-graph-v1.json')
g=load(RUN/'compiled-body-graph-v1.json');nodes={n['name']:n for n in g['nodes']}
required=[(names[0],'Measurable.exists_eq_measurable_comp'),(names[0],'MeasureTheory.ae_all_iff'),
    (names[1],prefix+'predictable_private_seed_independent'),(names[1],'ProbabilityTheory.IndepFun.congr'),
    (names[2],names[1]),(names[2],prefix+'expectedFixedMinimum_eq_variance'),(names[2],prefix+'iid_cumulative_prediction_decomposition'),
    (testprefix+'actual_all_time_bounded_policy',names[0]),(testprefix+'actual_current_independence',names[1]),
    (testprefix+'actual_original_excess_identity',names[2]),(testprefix+'bad_is_not_pointwise_predictable','Measurable.factorsThrough'),
    (testprefix+'actual_nonzero_excess',testprefix+'actual_original_excess_identity')]
for a,b in required:assert b in nodes[a]['value_dependencies'],(a,b)
for name in names:assert nodes[name]['kind']=='theorem' and nodes[name]['has_value']
for t in targets:
    p=RUN/('statement-fence-'+t['id']+'-v1.json')
    native('statement-fence-'+t['id']+'-v1','statement-fence','--declaration',t['name'],
        '--file',PUBLIC.relative_to(ROOT).as_posix(),'--source-assumption',
        'Exact source-derived AE information model specialization; completion/kernel/fullchapter required separately.', '--output',p)
    assert load(p)['statement_hash']==t['statement_hash']
    native('safe-verify-'+t['id']+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC.relative_to(ROOT).as_posix())
write(RUN/'actual-kernel-value-audit-v1.json',dict(
    actual_graph_nodes=len(g['nodes']),actual_TYPE_VALUE_occurrences=len(g['edges']),required_direct_VALUE_pairs=required,
    actual_named_axiom_outputs=len(actual_axiom_rows),actual_unique_axiom_names=len(set(n for n,_ in actual_axiom_rows)),
    actual_axioms=sorted(axioms),sorryAx=False,three_whole_public_type_VALUE_checks=True,
    public_source_sha256=sha(PUBLIC),canary_sha256=sha(canary),
    actual_test_theorems=sum(nodes[n]['kind']=='theorem' for n in cnames),test_only_definitions=sum(nodes[n]['kind']=='definition' for n in cnames),
    frozen_headers_unchanged=True,nondegenerate_AE_only_canary=True,
    BODY_combined_site_FINAL_acceptance_pending=True,accepted_local_obligations=0,remaining_local_obligations=3,
    chapter_complete=False,goal_complete=False))
proving_fixed()
print('Actual whole public types, proof values, standard axioms, direct VALUE dependencies and exact fences passed')
