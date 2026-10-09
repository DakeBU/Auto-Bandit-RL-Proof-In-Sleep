from common import *
fixed()
review=RUN/'body-and-canary-contract-review-v1.json'
assert sha(review)=='12fa9c1eae11caa4622217b5efb826509a7eb57fbd91e9fb88b811eb8ba922b4'
d=load(review)
assert not d['required_repairs'] and d['production_BODY_verdict']=='accepted-with-explicit-delta' and d['canary_contract_verdict']=='accepted-with-explicit-delta'
assert sha(d['report'])==d['report_sha256'] and sha(d['input_manifest'])==d['input_manifest_sha256']
inputs=load(d['input_manifest'])['rows']
assert len(inputs)==118
for r in inputs: assert sha(r['path'])==r['sha256'],r['path']
assert sha(PUBLIC)==d['production_sha256']
canary=CONTRACT/'canary-v1'
assert load(canary/'frozen-headers-draft-v1.json')['rows']==d['approved_canary_headers']
assert sha(canary/'definition-context-draft-v1.lean.txt')==d['canary_context_sha256']
mutable=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
write(RUN/'pre-canary-proving-native-RAW-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mutable]))
write(canary/'stabilized-v1.json',dict(state='stabilized',review=rows([review,d['report'],d['input_manifest']]),frozen_inputs=inputs,public_headers=d['approved_canary_headers'],permitted_proof_window=d['allowed_new_Test_scope'],production_sha256=d['production_sha256'],BODY_accepted=False,chapter_complete=False,whole_Goal='active'))
event('canary-stabilized-event-v1','stabilized',dict(leaf='two-complete-canary-types',evidence=(canary/'stabilized-v1.json').as_posix(),BODY_accepted=False))
event('canary-proving-event-v1','proving',dict(current_leaf='two-complete-canaries',required_public_lemma_applications=3,scope='NEW exact Test headers/context/private arithmetic helpers and OWN evidence only',chapter_complete=False))
fixed()
