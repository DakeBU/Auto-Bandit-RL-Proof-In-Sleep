from common import *
fixed()
r=load(RUN/'BODY-canary-contract-review-v1.json')
assert sha(RUN/'BODY-canary-contract-review-v1.json')=='06feae01fa803781b419dcc26ee221a184581c829ea828c4ea8d685fe19f7f13'
assert r['BODY_verdict']=='accepted-with-explicit-delta' and r['canary_contract_verdict']=='accepted' and not r['required_repairs']
for row in load(RUN/'BODY-canary-contract-review-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
assert not (ROOT/'Tests/OnlineProximalComparisonCanary.lean').exists()
d=load(CONTRACT/'canary-targets-draft-v1.json')
write(CONTRACT/'canary-stabilized-v1.json',dict(stage='stabilized',targets=d['targets'],context_sha256=d['context_sha256'],draft_sha256=sha(CONTRACT/'canary-targets-draft-v1.json'),review_sha256=sha(RUN/'BODY-canary-contract-review-v1.json'),production_sha256=sha(PUBLIC),allowed_file=d['allowed_file'],allowed_scope=d['allowed_scope'],actual_VALUE_dependency_required=d['actual_VALUE_dependency_required'],source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
event('proving-canaries-native-v1','proving',dict(contract_sha256=sha(CONTRACT/'canary-stabilized-v1.json'),review_sha256=sha(RUN/'BODY-canary-contract-review-v1.json'),frozen_hashes=[t['statement_hash'] for t in d['targets']],scope='Only exact3 new Test bodies/imports; no production or old baseline changes',source_container_closed=False,chapter_complete=False,goal_complete=False))
print('Exact3 canary types stabilized; public helper BODY accepted, not package acceptance.')
