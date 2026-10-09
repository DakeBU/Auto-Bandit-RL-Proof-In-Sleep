from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
import re
fixed();test=ROOT/'Tests/OnlineProximalComparisonCanary.lean'
assert load(RUN/'focused-canary-inspected-v1.json')['compiled']
assert sha(PUBLIC)=='04dae0024d9a2b61016b4652767f4d678725325a040a02c62680a202ec2593d2'
assert sha(test)==load(RUN/'focused-canary-inspected-v1.json')['test_sha256']
targets=load(CONTRACT/'canary-stabilized-v1.json')['targets']
lines=['import Tests.OnlineProximalComparisonCanary','open Set','namespace OnlineProximalCanaryAudit']
for t in targets:
    short=t['declaration'].rsplit('.',1)[1]
    lines.extend([t['exact_proposed_header'].replace('theorem '+short,'theorem '+short+'_value',1)+' := by\n  exact '+t['declaration'], '#check '+t['declaration'],'#print axioms '+t['declaration'],'#print axioms '+short+'_value'])
lines.append('end OnlineProximalCanaryAudit')
write(RUN/'CompleteCanaryPublicValues.lean','\n\n'.join(lines))
code,out=capture('canary-public-VALUE-kernel-v1','lake','env','lean',RUN/'CompleteCanaryPublicValues.lean')
found=re.findall(r'depends on axioms:\s*\[([^]]*)\]',out)
assert len(found)==6 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for a in found)
for i,t in enumerate(targets):
    assert statement_hash(lean_declaration_header(test,t['declaration']))==t['statement_hash']
    capture('canary-fence-%d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',t['declaration'],'--file',test.relative_to(ROOT).as_posix(),'--output',(CONTRACT/('canary-fence-%d-v1.json'%i)).relative_to(ROOT).as_posix())
    capture('canary-safe-%d-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',(CONTRACT/('canary-fence-%d-v1.json'%i)).relative_to(ROOT).as_posix(),'--lean-file',test.relative_to(ROOT).as_posix())
    assert load(CONTRACT/('canary-fence-%d-v1.json'%i))['statement_hash']==t['statement_hash']
old=(ROOT/'runs/online-ch2-prescient-20261009/export-combined-selected-dependencies-v1.lean').read_text(encoding='utf8')
old=old.replace('BanditRLProof.OnlinePrescientLinear','BanditRLProof.OnlineProximalComparison').replace('Tests.OnlinePrescientLinearCanary','Tests.OnlineProximalComparisonCanary')
allnames=[load(CONTRACT/'stabilized-v1.json')['targets'][0]['declaration']]+[t['declaration'] for t in targets]
start=old.index('def targets : Array Name := #[');end=old.index('\n\ndef moduleName',start)
old=old[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in allnames)+']'+old[end:]
old=old.replace('Seven frozen production terminals, five exact canaries, actual definitions/projection/gradient parents and recursively selected private scalar Test helpers. Direct TYPE_VALUE constant presence only; private helper traversal does not make this the full transitive or shared registry graph. Counts are not printed results or chapter acceptance.','One frozen real convex minimizer-comparison proof and three exact public canary families. Selected direct TYPE_VALUE constant presences; not occurrence counts, full transitive graph, shared registry or chapter/source theorem denominator.')
write(RUN/'export-selected-dependencies-v1.lean',old)
capture('selected-compiled-dependencies-v1','lake','env','lean','--run',RUN/'export-selected-dependencies-v1.lean',RUN/'selected-compiled-dependencies-v1.json')
graph=load(RUN/'selected-compiled-dependencies-v1.json');nodes={n['name']:n for n in graph['nodes']}
p=allnames[0]
pairs=[[n,p] for n in allnames[1:]]+[[p,n] for n in ['IsLocalMinOn.hasFDerivWithinAt_nonneg','sub_mem_posTangentConeAt_of_segment_subset','HasFDerivAt.comp_hasDerivAt_of_eq']]
for a,b in pairs:assert b in nodes[a]['value_dependencies'],(a,b)
write(RUN/'canary-complete-body-v1.raw',test.read_bytes())
write(RUN/'complete-candidate-inspected-v1.json',dict(production_sha256=sha(PUBLIC),test_sha256=sha(test),focused_production_actual_exit=0,focused_canary_actual_exit=0,focused_canary_cached_inclusive_jobs=2395,canary_linter_warnings='Two unnecessarySeqFocus style warnings; no suppression or semantic mutation.',canary_public_kernel_actual_exit=code,actual_axiom_outputs=found,standard_only=True,one_production_plus3canary_frozen_headers=True,selected_graph_sha256=sha(RUN/'selected-compiled-dependencies-v1.json'),selected_nodes=len(nodes),coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),required_VALUE_pairs=pairs,source_container_closed=False,package_accepted=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
event('candidate-native-v1','candidate',dict(production_sha256=sha(PUBLIC),test_sha256=sha(test),evidence_sha256=sha(RUN/'complete-candidate-inspected-v1.json'),status='One production terminal and3canary fullvalues/standardaxioms/6actualVALUEpairs/frozen guards verified. Canary BODY/publication/combined/FINAL review pending.',source_container_closed=False,chapter_complete=False,goal_complete=False))
write(RUN/'memory-digest-candidate-v1.md','TASK '+TASK+'\nOne reusable real comparison lemma BODYaccepted,3canary families focusedcompiled onfirstattempt and full publicVALUE/6standardaxiom outputs/frozen guards/6actualVALUE pairs inspected. Convex loss may be nonsmooth; regularizer need not be convex; boundary minimum does not imply unconstrained minimum. Actual minima and derivatives proved ineach instance, every-comparator results use samepublichelper. Two teststylewarnings retained, no suppression. Canary BODYandpublication review pending, roots/Tests/fullharness/site/registry/FINAL/nativeacceptance/delivery unrun. Full sourcegeneralBregman/EReal/recursivefixedvariable andall8Ch2forwardsrequiredopen; wholeGoalACTIVE.')
paths=[PUBLIC,test]+[p for p in RUN.iterdir() if p.is_file() and p.name not in ['lifecycle-state.json','lifecycle-sessions.jsonl','own-artifact-journal.md','trials.jsonl']]+list(CONTRACT.glob('*'))
write(RUN/'canary-BODY-review-inputs-v1.json',dict(rows=rows(paths),allowed_new_outputs=['canary-BODY-review-v1.md','canary-BODY-review-v1.json'],no_existing_inputs_changed=True))
fixed();print('Actual nondegenerate public canaries/full VALUE/standard axioms/frozen headers/6required compiled VALUE pairs verified. Distinct BODY and combined integration remain pending.')
