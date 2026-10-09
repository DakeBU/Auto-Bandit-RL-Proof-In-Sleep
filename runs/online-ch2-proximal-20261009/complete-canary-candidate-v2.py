from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
import re
fixed();test=ROOT/'Tests/OnlineProximalComparisonCanary.lean'
assert sha(PUBLIC)=='04dae0024d9a2b61016b4652767f4d678725325a040a02c62680a202ec2593d2'
assert sha(test)==load(RUN/'focused-canary-inspected-v1.json')['test_sha256']
assert load(RUN/'focused-canary-inspected-v1.json')['compiled']
targets=load(CONTRACT/'canary-stabilized-v1.json')['targets']
out=base64.b64decode(load(RUN/'canary-public-VALUE-kernel-v1.json')['stdout_base64']).decode('utf8')
assert load(RUN/'canary-public-VALUE-kernel-v1.json')['actual_exit']==0
found=re.findall(r'depends on axioms:\s*\[([^]]*)\]',out)
assert len(found)==6 and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for a in found) and 'sorryAx' not in out
for i,t in enumerate(targets):
    assert statement_hash(lean_declaration_header(test,t['declaration']))==t['statement_hash']
    assert load(RUN/('canary-fence-%d-v1.json'%i))['actual_exit']==0 and load(RUN/('canary-safe-%d-v1.json'%i))['actual_exit']==0
write(RUN/'candidate-artifact-collision-v1.json',dict(kind='data/command-receipt path collision in create-only capture',failed_script='complete-canary-candidate-v1.py',failed_script_actual_exit=1,exception='AssertionError selected-compiled-dependencies-v1.json already exists; exporter wrote data before capture receipt.',retained_data_sha256=sha(RUN/'selected-compiled-dependencies-v1.json'),exporter_exit_not_durably_captured=True,not_a_Lean_theorem_failure=True,repair='Reexecute same exporter into a distinct data path, distinct command-receipt label; do not overwrite old data or rerun successful unrelated kernel/fences.',source_or_header_or_body_change=False))
capture('selected-compiled-dependencies-command-v2','lake','env','lean','--run',RUN/'export-selected-dependencies-v1.lean',RUN/'selected-compiled-dependencies-data-v2.json')
graph=load(RUN/'selected-compiled-dependencies-data-v2.json');nodes={n['name']:n for n in graph['nodes']}
p=load(CONTRACT/'stabilized-v1.json')['targets'][0]['declaration']
pairs=[[t['declaration'],p] for t in targets]+[[p,n] for n in ['IsLocalMinOn.hasFDerivWithinAt_nonneg','sub_mem_posTangentConeAt_of_segment_subset','HasFDerivAt.comp_hasDerivAt_of_eq']]
for a,b in pairs:assert b in nodes[a]['value_dependencies'],(a,b)
write(RUN/'canary-complete-body-v2.raw',test.read_bytes())
write(RUN/'complete-candidate-inspected-v2.json',dict(production_sha256=sha(PUBLIC),test_sha256=sha(test),focused_production_actual_exit=0,focused_canary_actual_exit=0,focused_canary_cached_inclusive_jobs=2395,canary_linter_warnings='Two unnecessarySeqFocus style warnings; no suppression or semantic mutation.',canary_public_kernel_actual_exit=0,actual_axiom_outputs=found,standard_only=True,one_production_plus3canary_frozen_headers=True,selected_graph_sha256=sha(RUN/'selected-compiled-dependencies-data-v2.json'),selected_nodes=len(nodes),coalesced_direct_TYPE_VALUE_presences=len(graph['edges']),required_VALUE_pairs=pairs,retained_failed_export_capture_sha256=sha(RUN/'candidate-artifact-collision-v1.json'),source_container_closed=False,package_accepted=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
event('candidate-native-v2','candidate',dict(production_sha256=sha(PUBLIC),test_sha256=sha(test),evidence_sha256=sha(RUN/'complete-candidate-inspected-v2.json'),status='One production terminal and3canary fullvalues/standardaxioms/6actualVALUEpairs/frozen guards verified. Canary BODY/publication/combined/FINAL review pending.',source_container_closed=False,chapter_complete=False,goal_complete=False))
write(RUN/'memory-digest-candidate-v2.md','TASK '+TASK+'\nOne reusable real comparison lemma BODYaccepted,3canary families focusedcompiled onfirstattempt and full publicVALUE/6standardaxiom outputs/frozen guards/6actualVALUE pairs inspected. Convex loss may be nonsmooth; regularizer need not be convex; boundary minimum does not imply unconstrained minimum. Actual minima and derivatives proved ineach instance, every-comparator results use samepublichelper. Two teststylewarnings retained, no suppression. Actual exporter output/capture namingcollision retained; rerun withdistinct data/receipt paths actual0, not a mathematics failure. Canary BODYandpublication review pending, roots/Tests/fullharness/site/registry/FINAL/nativeacceptance/delivery unrun. Full sourcegeneralBregman/EReal/recursivefixedvariable andall8Ch2forwardsrequiredopen; wholeGoalACTIVE.')
paths=[PUBLIC,test]+[p for p in RUN.iterdir() if p.is_file() and p.name not in ['lifecycle-state.json','lifecycle-sessions.jsonl','own-artifact-journal.md','trials.jsonl']]+list(CONTRACT.glob('*'))
write(RUN/'canary-BODY-review-inputs-v2.json',dict(rows=rows(paths),allowed_new_outputs=['canary-BODY-review-v1.md','canary-BODY-review-v1.json'],no_existing_inputs_changed=True))
fixed();print('Actual full VALUE/standard axioms/frozen headers/6compiled VALUE pairs verified; distinct canary BODY/combined integration remain pending.')
