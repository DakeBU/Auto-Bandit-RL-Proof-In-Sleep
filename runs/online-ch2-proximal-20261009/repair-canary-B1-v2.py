from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
import re
fixed();test=ROOT/'Tests/OnlineProximalComparisonCanary.lean'
r=load(RUN/'canary-BODY-review-v1.json');assert sha(RUN/'canary-BODY-review-v1.json')=='8d093f7dd6ca6bd946b16d512d152d099f55409bdc07a3bb20e76ad625bd1dde'
assert r['verdict']=='rejected' and [x['id'] for x in r['required_repairs']]==['B1']
old=(RUN/'canary-complete-body-v2.raw').read_bytes();assert hashlib.sha256(old).hexdigest()==r['test_sha256']
oldtext=old.decode('utf8');newtext=test.read_text(encoding='utf8')
expected=oldtext.replace('  have hh := hb (1 / 4)\n  norm_num at hh ⊢','  have hh := hb (1 / 4)\n  have hl : -|(1 / 4 : ℝ)| = -1 / 4 := by norm_num\n  have hr : -(1 / 4 : ℝ) / 2 = -1 / 8 := by norm_num\n  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh',1).replace('  have hh := hb 0\n  norm_num at hh ⊢','  have hh := hb 0\n  have hl : (1 : ℝ) - 0 ^ 2 = 1 := by norm_num\n  have hr : (2 : ℝ) * (0 + 1) = 2 := by norm_num\n  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh',1)
assert expected==newtext
for row in load(RUN/'canary-BODY-review-inputs-v2.json')['rows']:
    if Path(row['path'])!=test:assert sha(row['path'])==row['sha256'],row['path']
targets=load(CONTRACT/'canary-stabilized-v1.json')['targets']
for t in targets:assert statement_hash(lean_declaration_header(test,t['declaration']))==t['statement_hash']
write(RUN/'canary-B1-repaired-body-v2.raw',test.read_bytes())
event('repair-canary-B1-native-v2','repair',dict(rejected_review_sha256=sha(RUN/'canary-BODY-review-v1.json'),repair='B1: Only two numeric tails now Eq.mp of expression equality and actual hb instance. All3headers andotherbodyspans unchanged.',source_or_statement_change=False,source_container_closed=False,chapter_complete=False,goal_complete=False))
code,out=capture('focused-canary-build-v2','lake','build','Tests.OnlineProximalComparisonCanary')
assert 'Build completed successfully' in out
code,values=capture('canary-public-VALUE-kernel-v2','lake','env','lean',RUN/'CompleteCanaryPublicValues.lean')
axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',values)
assert len(axioms)==6 and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for a in axioms) and 'sorryAx' not in values
for i,t in enumerate(targets):capture('canary-safe-%d-v2'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',(CONTRACT/('canary-fence-%d-v1.json'%i)).relative_to(ROOT).as_posix(),'--lean-file',test.relative_to(ROOT).as_posix())
capture('selected-compiled-dependencies-command-v3','lake','env','lean','--run',RUN/'export-selected-dependencies-v1.lean',RUN/'selected-compiled-dependencies-data-v3.json')
graph=load(RUN/'selected-compiled-dependencies-data-v3.json');nodes={n['name']:n for n in graph['nodes']}
pairs=load(RUN/'complete-candidate-inspected-v2.json')['required_VALUE_pairs']
for a,b in pairs:assert b in nodes[a]['value_dependencies'],(a,b)
capture('numeric-new-tail-command-v2','lake','env','lean','--run',RUN/'audit-numeric-tail-v1.lean',RUN/'numeric-new-tail-data-v2.json')
oldtails=load(RUN/'numeric-old-tail-data-v1.json')['rows'];newtails=load(RUN/'numeric-new-tail-data-v2.json')['rows']
assert len(oldtails)==len(newtails)==2
assert all(not x['public_helper_in_selected_tail'] for x in oldtails)
assert all(x['public_helper_in_selected_tail'] for x in newtails)
write(RUN/'canary-B1-repair-inspected-v2.json',dict(rejected_review_sha256=sha(RUN/'canary-BODY-review-v1.json'),production_sha256=sha(PUBLIC),old_test_sha256=hashlib.sha256(old).hexdigest(),test_sha256=sha(test),only_two_exact_numeric_tail_spans_changed=True,all3frozen_headers_unchanged=True,actual_focused_exit=0,actual_public_VALUE_kernel_exit=0,actual_axiom_outputs=axioms,standard_only=True,selected_graph_sha256=sha(RUN/'selected-compiled-dependencies-data-v3.json'),required_VALUE_pairs=pairs,old_numeric_tails=[dict(declaration=x['declaration'],head=x['selected_tail_head'],helper_present=x['public_helper_in_selected_tail']) for x in oldtails],new_numeric_tails=[dict(declaration=x['declaration'],head=x['selected_tail_head'],helper_present=x['public_helper_in_selected_tail']) for x in newtails],numeric_tail_extractor_sha256=sha(RUN/'audit-numeric-tail-v1.lean'),old_tail_data_sha256=sha(RUN/'numeric-old-tail-data-v1.json'),new_tail_data_sha256=sha(RUN/'numeric-new-tail-data-v2.json'),selection_scope='Compiled final numeric conjunct expression with top-level lets substituted and rightmost And.intro selected; no whole-conjunction-only inference or proof-irrelevance normalization.',distinct_repair_review_pending=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
paths=[PUBLIC,test]+[p for p in RUN.iterdir() if p.is_file() and p.name not in ['lifecycle-state.json','lifecycle-sessions.jsonl','own-artifact-journal.md','trials.jsonl']]+list(CONTRACT.glob('*'))
write(RUN/'canary-B1-repair-review-inputs-v2.json',dict(rows=rows(paths),allowed_new_outputs=['canary-BODY-review-v2.md','canary-BODY-review-v2.json'],no_existing_inputs_changed=True))
fixed();print('B1 exact2tails repaired; actual compiled selected numeric VALUE now retains public helper inboth. Distinct repair review pending.')
