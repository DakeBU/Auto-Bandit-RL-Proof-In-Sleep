from common_proving_v1 import *
import re

s=proving_fixed()
assert load(RUN/'leaf-L4-attempt-v1.json')['mathematical_body_compiled']
assert load(RUN/'canary-attempt-v1.json')['mathematical_test_bodies_compiled']
assert CANARY.read_bytes()==(RUN/'canary-attempt-v1.lean.raw').read_bytes()
assert PUBLIC.read_bytes()==(RUN/'leaf-L4-attempt-v1.lean.raw').read_bytes()
names=[t['name'] for t in s['targets']]
pre='BanditRL.OnlineLearning.';tp='Tests.OnlineGuessingCompletedCausal.'
cnames=[tp+m.group(1) for m in re.finditer(r'^theorem\s+(\w+)',CANARY.read_text(encoding='utf8'),re.M)]
parents=[pre+x for x in ['ae_predictable_exists_bounded_history_policy','ae_predictable_private_seed_independent',
    'ae_predictable_private_seed_expectedFixed_excess','privateSeedPastInformation','private_seed_past_independent',
    'predictable_private_seed_independent','expectedFixedMinimum','expectedFixedRegret',
    'expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition']]
mathlib=['MeasurableSpace.measurable_mapNatBool','MeasurableSpace.injective_mapNatBool',
    'Measurable.measurableEmbedding','MeasurableEmbedding.measurable_invFun',
    'MeasurableEmbedding.leftInverse_invFun','MeasureTheory.ae_all_iff']
fixtures=['Tests.OnlineGuessingRandomizedIID.'+x for x in ['seededLaw','seed','target','seededLaw_probability',
    'seed_measurable','target_measurable','seed_has_coinLaw','target_has_coinLaw','target_sameLaw','target_support',
    'target_independent','seed_independent_whole_process','target_mean','target_variance']]
fixtures+=['Tests.OnlineGuessingAECausal.'+x for x in ['badPrediction','bad_eq_causal_ae','causal_version_measurable',
    'bad_ae_unit','bad_is_not_pointwise_predictable','bad_is_not_everywhere_unit','actual_mean_square']]
allnames=list(dict.fromkeys(names+cnames+parents+mathlib+fixtures))
q='import Tests.OnlineGuessingCompletedCausalCanary\nopen MeasureTheory ProbabilityTheory Filter BanditRL.OnlineLearning\nuniverse u v\nnamespace NeutralCompletedCausal\n'
for i,t in enumerate(s['targets'],1):
    rest=t['header'].split(t['name'].split('.')[-1],1)[1].strip().replace(' :\n',',\n',1)
    q+='def Q'+str(i)+' : Prop := ∀ '+rest+'\n\n'
    q+='theorem wholePublicValue'+str(i)+' : Q'+str(i)+' := @'+t['name']+'\n\n'
    q+='#check wholePublicValue'+str(i)+'\n#print axioms wholePublicValue'+str(i)+'\n'
q+='end NeutralCompletedCausal\n\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in allnames)+'\n'
write(RUN/'whole-public-types-axioms-v1.lean',q)
gate('whole-public-types-axioms-v1','lake','env','lean',RUN/'whole-public-types-axioms-v1.lean')
log=(RUN/'whole-public-types-axioms-v1.log').read_text(encoding='utf8');assert 'sorryAx' not in log
axiomrows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
axioms={a.strip() for _,v in axiomrows for a in v.split(',') if a.strip()}
assert axioms<={'propext','Classical.choice','Quot.sound'}
assert set(allnames+['NeutralCompletedCausal.wholePublicValue'+str(i) for i in range(1,5)])<={n for n,_ in axiomrows}
old=(ROOT/'runs/online-ae-causal-20261008/export-compiled-body-graph-v1.lean').read_text(encoding='utf8')
head=old[:old.index('def targets')].replace('Tests.OnlineGuessingAECausalCanary','Tests.OnlineGuessingCompletedCausalCanary')
rest=old[old.index('def moduleName'):].replace('Tests.OnlineGuessingAECausalCanary','Tests.OnlineGuessingCompletedCausalCanary')
rest=rest.replace('Tests.OnlineGuessingAECausal.instMeasurable','Tests.OnlineGuessingCompletedCausal.instMeasurable')
rest=rest.replace('direct-constant-occurrence','coalesced-direct-TYPE_VALUE-constant-presence-not-occurrence-count')
rest=rest.replace('Three exact AE causal public proof bodies, actual AE-only non-pointwise canaries and reused independent private seed/infinite IID laws. Direct TYPE/VALUE constants only, not chapter/source coverage.',
    'Four exact completed-causal proof bodies, eleven genuine augmented-but-not-ordinary canaries and selected actual parents. Direct coalesced TYPE_VALUE constant presence only, not a full dependency graph or chapter/source coverage.')
write(RUN/'export-compiled-body-graph-v1.lean',head+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in allnames)+']\n\n'+rest)
gate('export-compiled-body-graph-v1','lake','env','lean','--run',RUN/'export-compiled-body-graph-v1.lean',RUN/'compiled-body-graph-v1.json')
g=load(RUN/'compiled-body-graph-v1.json');nodes={n['name']:n for n in g['nodes']}
required=[(names[0],m) for m in mathlib]
for i in range(1,4):required.extend([(names[i],names[0]),(names[i],parents[i-1])])
required.extend([(tp+'actual_completed_real_version',names[0]),(tp+'actual_all_time_bounded_policy',names[1]),
    (tp+'actual_current_independence',names[2]),(tp+'actual_original_excess_identity',names[3]),
    (tp+'actual_nonzero_excess',tp+'actual_original_excess_identity'),
    (tp+'bad_completed_but_not_ordinary_at_zero','Tests.OnlineGuessingAECausal.bad_is_not_pointwise_predictable')])
for a,b in required:assert b in nodes[a]['value_dependencies'],(a,b)
for n in names:assert nodes[n]['has_value'] and nodes[n]['kind']=='theorem'
for t in s['targets']:
    args=[]
    assumptions=[line.strip() for line in t['header'].splitlines() if '(h' in line or '[IsProbabilityMeasure' in line]
    assert assumptions
    for a in assumptions:args.extend(['--source-assumption',a])
    p=RUN/('statement-fence-'+t['id']+'-v1.json')
    native('statement-fence-'+t['id']+'-v1','statement-fence','--declaration',t['name'],
        '--file',PUBLIC.relative_to(ROOT).as_posix(),*args,'--output',p)
    assert load(p)['statement_hash']==t['statement_hash']
    native('safe-verify-'+t['id']+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC.relative_to(ROOT).as_posix())
    assert load(RUN/('safe-verify-'+t['id']+'-v1.log'))['ok']
write(RUN/'actual-kernel-value-audit-v1.json',dict(actual_selected_graph_nodes=len(g['nodes']),
    actual_coalesced_TYPE_VALUE_edges=len(g['edges']),not_occurrence_or_full_graph_count=True,
    required_direct_VALUE_pairs=required,actual_required_VALUE_pairs=len(required),
    actual_named_axiom_outputs=len(axiomrows),actual_unique_axiom_names=len(set(n for n,_ in axiomrows)),
    actual_axioms=sorted(axioms),sorryAx=False,four_whole_public_type_VALUE_checks=True,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),actual_named_canary_proofs=len(cnames),
    frozen_headers_unchanged=True,BODY_full_root_Test_harness_site_FINAL_pending=True,
    accepted_obligations=0,remaining_obligations=4,chapter_complete=False,goal_complete=False))
proving_fixed()
print('Actual full four proposition VALUE witnesses, axioms, coalesced dependency presence and exact fences passed.',flush=True)
