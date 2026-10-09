from common_proving_v2 import *
import re
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
spec=load(CONTRACT/'chapter-canary-targets-stabilized-v1.json')
targets=spec['targets'];module=ROOT/'Tests/OnlineLearningChapterAuditCanary.lean'
assert len(targets)==27
for t in targets:assert statement_hash(lean_declaration_header(module,t['name']))==t['statement_hash'],t['id']
write(RUN/'snapshots/chapter-canary-body-candidate-v1.lean.raw',module.read_bytes())
code=spec['setup'].split('namespace Tests.OnlineLearningChapterAudit')[0]
code='import Tests.OnlineLearningChapterAuditCanary\n'+code
code+='open Tests.OnlineLearningChapterAudit\n\n'
for t in targets:
    code+='#check '+t['name']+'\n#print axioms '+t['name']+'\n'
    code+='example :\n    '+t['conclusion']+' :=\n  '+t['name']+'\n\n'
probe=RUN/'chapter-canary-public-values-v1.lean';write(probe,code)
gate('chapter-canary-public-values-v1','lake','env','lean',probe)
log=(RUN/'chapter-canary-public-values-v1.log').read_text('utf8')
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
empty=re.findall(r"'([^']+)' does not depend on any axioms",log)
assert len(found)+len(empty)==27
audit=[]
for name,raw in found:
    used=sorted({x.strip() for x in raw.split(',') if x.strip()})
    assert set(used)<={'propext','Classical.choice','Quot.sound'},(name,used)
    audit.append(dict(name=name,actual_axioms=used))
audit += [dict(name=name,actual_axioms=[]) for name in empty]
assert {r['name'] for r in audit}=={t['name'] for t in targets}
write(RUN/'chapter-canary-axiom-audit-v1.json',dict(rows=audit,actual_log_sha256=sha(RUN/'chapter-canary-public-values-v1.log'),standard_only=True,complete_brackets_multiline=True))
old=(RUN/'export-general-init-readiness-v1.lean').read_text('utf8')
names=[t['name'] for t in targets]+['Tests.OnlineLearningChapterAudit.rising','Tests.OnlineLearningChapterAudit.falling']
old=old.replace('import BanditRLProof\n','import BanditRLProof\nimport Tests.OnlineLearningChapterAuditCanary\n',1)
old=old.replace('def targets : Array Name := #[','def targets : Array Name := #[\n'+','.join('`'+n for n in names)+',',1)
old=old.replace('Lean.importModules #[{ module := `BanditRLProof }, { module := `BanditRLProof.OnlineFTLInitializationRegret }]', 'Lean.importModules #[{ module := `BanditRLProof }, { module := `BanditRLProof.OnlineFTLInitializationRegret }, { module := `Tests.OnlineLearningChapterAuditCanary }]')
old=old.replace('Fifty unchanged reused Chapter1 public proof targets, four exact actual general-initial FTL bodies and selected support definitions.','Fifty unchanged reused Chapter1 public proof targets, four actual initialized-FTL bodies,27 actual new Test canary proofs/two probe definitions and selected support definitions. Test proofs are not new canonical source results.')
script=RUN/'export-chapter-canary-readiness-v1.lean';write(script,old)
graph=RUN/'compiled-chapter-canary-readiness-graph-v1.json'
gate('export-chapter-canary-readiness-v1','lake','env','lean','--run',script,graph)
g=load(graph);nodes={n['name']:n for n in g['nodes']}
assert len(nodes)==106 and all(n['has_value'] and n['module']!='unknown' for n in nodes.values())
required={
 'C001':['BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret'],
 'C002':['BanditRL.OnlineLearning.ftlPredict_bestRegret_initial_correction'],
 'C003':['BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret'],
 'C004':['BanditRL.OnlineLearning.ftlPredict_bestRegret_refined','BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret'],
 'C005':['BanditRL.OnlineLearning.ftlState_prefix'],
 'C006':['BanditRL.OnlineLearning.ftlState_first','BanditRL.OnlineLearning.ftlState_eq_predict'],
 'C007':['BanditRL.OnlineLearning.ftlPredict_upperNoRegret'],
 'C008':['BanditRL.OnlineLearning.ftlPredict_bestRegret_average_tendsto_zero'],
 'C009':['BanditRL.OnlineLearning.ftlPredict_bestRegret_initial_correction'],
 'C010':['BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret'],
 'C011':['Tests.OnlineLearningChapterAudit.general_initial_finite_values'],
 'C012':['Tests.OnlineGuessingIIDBenchmark.observation_variance','Tests.OnlineGuessingIIDBenchmark.meanPredict_two_round_excess'],
 'C013':['Tests.OnlineGuessingIIDBenchmark.actual_mean_attainment','Tests.OnlineGuessingIIDBenchmark.constant_known_mean_zero'],
 'C014':['Tests.OnlineGuessingIIDBenchmark.hindsight_minimum_two','Tests.OnlineGuessingIIDBenchmark.two_round_fixed_minimum'],
 'C015':['Tests.OnlineGuessingIIDSuccess.actual_meanPredict_success'],
 'C016':['RegretDomainsProbe.outside_prediction_and_negative_regret'],
 'C017':['BanditRL.OnlineLearning.squaredLoss_minimum_eq'],
 'C018':['BanditRL.OnlineLearning.empiricalMean_unique'],
 'C019':['BanditRL.OnlineLearning.lemma_1_2'],
 'C020':['BanditRL.OnlineLearning.meanPredict_bestRegret_refined','BanditRL.OnlineLearning.meanPredict_bestRegret_bound'],
 'C021':['BanditRL.OnlineLearning.meanPredict_stability'],
 'C022':['Tests.OnlineGuessingKernelCausal.every_horizon_excess','Tests.OnlineGuessingKernelCausal.history_feedback_distribution'],
 'C023':['Tests.OnlineGuessingIIDSuccess.correlated_meanPredict_negative_two','Tests.OnlineGuessingIIDBenchmark.meanPredict_two_round_excess'],
 'C024':['BanditRL.OnlineLearning.dyadic_meanPredict_obstruction'],
 'C025':['GuessingLogLowerProbe.seeded_log_endpoint'],
 'C026':['harmonic_le_one_add_log'],
 'C027':['Tests.OnlineGuessingIIDSuccess.nonzero_initial_total_sublinear']}
checks=[]
for t in targets:
    for parent in required[t['id']]:
        assert parent in nodes[t['name']]['value_dependencies'],(t['id'],parent)
        checks.append(dict(public=t['name'],actual_direct_value_parent=parent))
write(RUN/'chapter-canary-direct-value-audit-v1.json',dict(required_actual_pairs=checks,selected_nodes=len(nodes),coalesced_direct_TYPE_VALUE_edges=len(g['edges']),full_transitive_graph=False,canonical_source_new_result_count=4,Test_canaries=27,source_audit_objects=17,proof_total=None))
for t in targets:
    fence=CONTRACT/('public-'+t['id']+'-fence-v1.json')
    gate('fence-'+t['id']+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['name'],'--file',module,'--output',fence)
    assert load(fence)['statement_hash']==t['statement_hash']
    gate('safe-'+t['id']+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',fence,'--lean-file',module)
    fixed()
assert sha(module)==sha(RUN/'snapshots/chapter-canary-body-candidate-v1.lean.raw')
write(RUN/'chapter-canary-public-readiness-v1.json',dict(phase='candidate actual27canary bodies; distinct BODY/Tests/fullchapter gates pending',Test_sha256=sha(module),exact_frozen_headers=27,actual_whole_type_public_value_witnesses=27,actual_axiom_outputs=27,standard_only=True,actual_required_direct_value_pairs=len(checks),native_fence_and_safe_pairs=27,selected_nodes=len(nodes),coalesced_direct_TYPE_VALUE_edges=len(g['edges']),chapter_complete=False,goal_complete=False,source_audit_objects=17,proof_total=None))
fixed()
print('Actual27 full public proof values/axioms/fences/safe/directVALUE verified; BODY pending.',flush=True)
