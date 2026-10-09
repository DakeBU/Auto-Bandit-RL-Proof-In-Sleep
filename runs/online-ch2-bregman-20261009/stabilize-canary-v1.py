from common import *
import copy
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash
fixed()
rp=RUN/'BODY-canary-contract-review-v1.json'
assert sha(rp)=='7d4088545f5fedec3569914dab852d138c97b040764d15fe0810ce210059788c'
r=load(rp)
assert r['BODY_verdict']==r['canary_contract_verdict']=='accepted' and not r['required_repairs']
for row in load(RUN/'BODY-canary-contract-review-inputs-v1.json')['rows']:
    assert sha(row['path'])==row['sha256'],row['path']
d=load(CONTRACT/'canary-targets-draft-v1.json')
assert d['targets']==r['approved_canary_types']
assert sha(PUBLIC)==r['production_sha256'] and not (ROOT/'Tests/OnlineBregmanProximalCanary.lean').exists()
targets=copy.deepcopy(d['targets'])
for t,approved in zip(targets,r['approved_canary_scope']['fingerprints']):
    t['header_raw_sha256']=t['statement_hash']
    t['statement_hash']=statement_hash(t['exact_proposed_header'])
    assert t['header_raw_sha256']==approved['header_raw_sha256']
    assert t['statement_hash']==approved['native_normalized_statement_hash']
write(CONTRACT/'canary-stabilized-v1.json',dict(stage='stabilized',targets=targets,context_sha256=d['neutral_sha256'],draft_sha256=sha(CONTRACT/'canary-targets-draft-v1.json'),review_sha256=sha(rp),production_sha256=sha(PUBLIC),allowed_scope=r['approved_canary_scope'],fingerprint_convention='Exact raw header SHA retained separately; statement_hash is the native normalized hash as independently approved. No header/context/semantics revision.',source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
event('proving-canaries-native-v1','proving',dict(contract_sha256=sha(CONTRACT/'canary-stabilized-v1.json'),review_sha256=sha(rp),frozen_hashes=[t['statement_hash'] for t in targets],scope='Only two exact public Test conjunctions and necessary local polynomial/minimum/arithmetic helpers; no extra named declaration/old files',source_container_closed=False,chapter_complete=False,goal_complete=False))
fixed()
print('Two complete canary types frozen; raw/native fingerprint conventions explicitly distinguished.')
