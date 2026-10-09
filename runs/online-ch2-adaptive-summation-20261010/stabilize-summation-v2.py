from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
review=RUN/'contract-source-review-v2.json'
assert sha(review)=='4f80aebe22be93073d4d7214ca186d83f90adb51773e24fbcc696eed73c73222'
d=load(review)
assert d['verdict']=='accepted-with-explicit-delta' and d['required_repairs']==[]
assert sha(d['report'])==d['report_sha256'] and sha(d['input_manifest'])==d['input_manifest_sha256']
inputs=load(d['input_manifest'])['rows']
assert len(inputs)==105
for r in inputs: assert sha(r['path'])==r['sha256'],r['path']
headers=load(CONTRACT/'frozen-headers-draft-v2.json')['rows']
assert len(headers)==1 and headers[0]==d['target']
assert lifecycle.statement_hash(headers[0]['exact_header'])==headers[0]['normalized_header_sha256']
assert sha(CONTRACT/'definition-context-v2.lean.txt')==d['definition_context_sha256']
assert not PUBLIC.exists()
mutable=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
write(RUN/'pre-stabilization-native-RAW-v2.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mutable],historical_review_inputs='Exact reviewed pre-transition bytes, not a claim that live native files stay unchanged after authorized events.'))
write(CONTRACT/'stabilized-v2.json',dict(state='stabilized',review=rows([review,d['report'],d['input_manifest']]),frozen_inputs=inputs,public_headers=headers,definition_context_sha256=d['definition_context_sha256'],first_leaf=headers[0]['declaration'],permitted_proof_window=d['permitted_proof_window'],BODY_accepted=False,canary='separate draft contract/reconstruction/source review pending',chapter_complete=False,whole_Goal='active'))
event('summation-stabilized-event-v2','stabilized',dict(leaf=headers[0]['declaration'],evidence=(CONTRACT/'stabilized-v2.json').as_posix(),evidence_sha256=sha(CONTRACT/'stabilized-v2.json'),boundary='OWN native journal records reviewed stabilization; it does not enforce all paper-level workflow rules.'))
event('summation-proving-event-v2','proving',dict(current_leaf=headers[0]['declaration'],statement_hash=headers[0]['normalized_header_sha256'],route='cumulative nonnegative intervals, continuity-derived integrability, constant endpoint comparison, finite sum, adjacent integral telescope',allowed_edits=['NEW frozen production BODY and necessary private helpers','NEW OWN proof attempt/lifecycle evidence'],BODY='not authored at event time',chapter_complete=False,whole_Goal='active'))
write(RUN/'stabilization-inspected-v2.json',dict(review_input_count=105,pretransition_all_input_RAW_matched=True,frozen_header_sha256=headers[0]['normalized_header_sha256'],stabilized=rows([CONTRACT/'stabilized-v2.json']),prospective_native_deltas=rows(mutable),reviewed_old_native_RAW=(RUN/'pre-stabilization-native-RAW-v2.json').as_posix(),other_reviewed_inputs_unchanged=all(sha(r['path'])==r['sha256'] for r in inputs if Path(r['path']) not in mutable),BODY_accepted=False))
fixed()
print('Exact one terminal stabilized; proving window active.',flush=True)
