from common_canary_v1 import *
import re

canary_fixed()
s = proving_fixed()
assert load(RUN/'canary-attempt-v4.json')['mathematical_body_compiled']
assert CANARY.read_bytes() == (RUN/'canary-attempt-v4.lean.raw').read_bytes()
names = [t['name'] for t in s['targets']]
pre = 'BanditRL.OnlineLearning.'
tp = 'Tests.OnlineGuessingKernelCausal.'
cnames = [t['name'] for t in load(RUN/'canary-frozen-targets-v2.json')['targets']]
definitions = [pre+n for n in ['KernelDecisionHistory','KernelDecisionSampler','kernelGeneratedActions',
    'kernelCausalPolicy','kernelGeneratedHistory','kernelGeneratedPrediction','kernelUniformTapeLaw','kernelGameLaw']]
fixtures = [tp+n for n in ['lowLaw','highLaw','lowLaw_probability','highLaw_probability','switchSet',
    'decisionKernel','decisionKernel_markov','oneHistory','selectedSampler','observationLaw','prediction','target','gameLaw']]
parents = [pre+n for n in ['independent_private_seed_pair','randomized_history_policy_expectedFixed_excess',
    'expectedFixedMinimum','expectedFixedRegret','expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition']]
mathlib = ['ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval',
    'ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd','ProbabilityTheory.iIndepFun_infinitePi',
    'ProbabilityTheory.indepFun_prod','ProbabilityTheory.iIndepFun.indepFun_finset',
    'MeasureTheory.Measure.infinitePi_map_eval','MeasureTheory.Measure.compProd_apply']
allnames = list(dict.fromkeys(names+cnames+definitions+fixtures+parents+mathlib))
q = 'import Tests.OnlineGuessingKernelCausalCanary\nopen MeasureTheory ProbabilityTheory unitInterval BanditRL.OnlineLearning\nnamespace NeutralKernelCausal\n'
for i,t in enumerate(s['targets'],1):
    rest = t['header'].split(t['name'].split('.')[-1],1)[1].strip().replace(' :\n',',\n',1)
    q += 'def Q'+str(i)+' : Prop := ∀ '+rest+'\n\n'
    q += 'theorem wholePublicValue'+str(i)+' : Q'+str(i)+' := @'+t['name']+'\n\n'
    q += '#check wholePublicValue'+str(i)+'\n#print axioms wholePublicValue'+str(i)+'\n'
q += 'end NeutralKernelCausal\n\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in allnames)+'\n'
write(RUN/'whole-public-types-axioms-v1.lean',q)
gate('whole-public-types-axioms-v1','lake','env','lean',RUN/'whole-public-types-axioms-v1.lean')
log = (RUN/'whole-public-types-axioms-v1.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
axiomrows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
axioms = {a.strip() for _,v in axiomrows for a in v.split(',') if a.strip()}
assert axioms <= {'propext','Classical.choice','Quot.sound'}
assert set(allnames+['NeutralKernelCausal.wholePublicValue'+str(i) for i in range(1,6)]) <= {n for n,_ in axiomrows}
old = (ROOT/'runs/online-completed-causal-20261008/export-compiled-body-graph-v1.lean').read_text(encoding='utf8')
head = old[:old.index('def targets')].replace('Tests.OnlineGuessingCompletedCausalCanary','Tests.OnlineGuessingKernelCausalCanary')
rest = old[old.index('def moduleName'):].replace('Tests.OnlineGuessingCompletedCausalCanary','Tests.OnlineGuessingKernelCausalCanary')
rest = rest.replace('Tests.OnlineGuessingCompletedCausal.instMeasurable','Tests.OnlineGuessingKernelCausal.instMeasurable')
rest = rest.replace('Four exact completed-causal proof bodies, eleven genuine augmented-but-not-ordinary canaries and selected actual parents. Direct coalesced TYPE_VALUE constant presence only, not a full dependency graph or chapter/source coverage.',
    'Five frozen actual causal-kernel proof bodies, stochastic history-feedback canaries and exact parents. Selected direct coalesced TYPE_VALUE constants only; not full transitive graph or source/chapter coverage.')
write(RUN/'export-compiled-body-graph-v1.lean',head+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in allnames)+']\n\n'+rest)
gate('export-compiled-body-graph-v1','lake','env','lean','--run',RUN/'export-compiled-body-graph-v1.lean',RUN/'compiled-body-graph-v1.json')
g = load(RUN/'compiled-body-graph-v1.json')
nodes = {n['name']:n for n in g['nodes']}
required = [(names[0],mathlib[0]),(names[2],pre+'independent_private_seed_pair'),
    (names[2],mathlib[2]),(names[2],mathlib[3]),(names[2],mathlib[4]),
    (names[3],names[1]),(names[3],names[2]),(names[3],mathlib[1])]
required += [(names[4],n) for n in names[:4]+[pre+'randomized_history_policy_expectedFixed_excess']]
required += [(tp+'public_family_realizes',names[0]),(tp+'public_causal_process',names[1]),
    (tp+'public_joint_law',names[2]),(tp+'public_conditional_law',names[3]),
    (tp+'actual_process_excess',names[4]),(tp+'selectedSampler',names[4]),
    (tp+'actual_prediction_binary',tp+'public_joint_law'),
    (tp+'every_horizon_excess',tp+'actual_process_excess'),
    (tp+'every_horizon_excess',tp+'actual_prediction_binary')]
for a,b in required:
    assert b in nodes[a]['value_dependencies'],(a,b)
for n in names:
    assert nodes[n]['has_value'] and nodes[n]['kind'] == 'theorem'
native('help-statement-fence-v1','statement-fence','--help')
native('help-safe-verify-v1','safe-verify','--help')
for t in s['targets']:
    args = []
    assumptions = [line.strip() for line in t['header'].splitlines() if '(h' in line or '[∀ t' in line]
    assert assumptions
    for a in assumptions:
        args.extend(['--source-assumption',a])
    p = RUN/('statement-fence-'+t['id']+'-v1.json')
    native('statement-fence-'+t['id']+'-v1','statement-fence','--declaration',t['name'],
        '--file',PUBLIC.relative_to(ROOT).as_posix(),*args,'--output',p)
    assert load(p)['statement_hash'] == t['statement_hash']
    native('safe-verify-'+t['id']+'-v1','safe-verify','--fence',p,'--lean-file',PUBLIC.relative_to(ROOT).as_posix())
    assert load(RUN/('safe-verify-'+t['id']+'-v1.log'))['ok']
write(RUN/'actual-kernel-value-audit-v1.json',dict(actual_selected_graph_nodes=len(g['nodes']),
    actual_coalesced_TYPE_VALUE_edges=len(g['edges']),not_occurrence_or_full_graph_count=True,
    required_direct_VALUE_pairs=required,actual_required_VALUE_pairs=len(required),
    actual_named_axiom_outputs=len(axiomrows),actual_unique_axiom_names=len(set(n for n,_ in axiomrows)),
    actual_axioms=sorted(axioms),sorryAx=False,five_whole_public_type_VALUE_checks=True,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),actual_named_canary_proofs=len(cnames),
    frozen_headers_unchanged=True,body_combined_root_Test_harness_site_final_pending=True,
    accepted_obligations=0,remaining_obligations=5,chapter_complete=False,goal_complete=False))
canary_fixed()
print('Actual complete public VALUE witnesses, axioms, selected dependency pairs and exact fences passed.',flush=True)
