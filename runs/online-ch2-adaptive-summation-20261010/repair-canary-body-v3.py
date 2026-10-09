from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
canary=CONTRACT/'canary-v1';test=ROOT/'Tests/OnlineAdaptiveSummationCanary.lean'
frozen=load(canary/'stabilized-v1.json')
assert sha(PUBLIC)==frozen['production_sha256']
assert load(RUN/'canary-focused-build-v2.json')['actual_exit']==1
assert test.read_bytes()==(RUN/'canary-attempt-v2.lean.txt').read_bytes()
capture('canary-integral-API-type-probe-v3','lake','env','lean',RUN/'CanaryIntegralAPIProbeV3.lean')
old=(RUN/'canary-main-body-attempt-v2.txt').read_text(encoding='utf8')
assert old.count('intervalIntegral.integral_id')==1
body=old.replace('intervalIntegral.integral_id','integral_id')
write(RUN/'canary-main-body-attempt-v3.txt',body)
write(RUN/'canary-body-repair-v3.json',dict(failure_receipt=rows([RUN/'canary-focused-build-v2.json']),failed_snapshot=rows([RUN/'canary-attempt-v2.lean.txt']),obstruction='API qualification error, not mathematical failure: the pinned Integrals.Basic namespace intervalIntegral ends at line108; integral_id at line201 is global.',fresh_API_elaboration=rows([RUN/'canary-integral-API-type-probe-v3.json']),repair='Use the actual global integral_id theorem in the unchanged exact integral computation.',header_context_unchanged=True,production_unchanged=True,route_changed=False,chapter_complete=False))
event('canary-body-repair-event-v3','repair',dict(leaf='nonconstant_zero_increment_canary',evidence=(RUN/'canary-body-repair-v3.json').as_posix(),target_changed=False,route_changed=False))
context=(canary/'definition-context-draft-v1.lean.txt').read_text(encoding='utf8')
bodies=[body,(RUN/'canary-zero-body-attempt-v1.txt').read_text(encoding='utf8')]
source=context.replace('end Tests.OnlineAdaptiveSummationCanary\n','\n'.join(r['exact_header']+' := by\n'+b for r,b in zip(frozen['public_headers'],bodies))+'\nend Tests.OnlineAdaptiveSummationCanary\n')
test.write_bytes(source.encode('utf8'))
for r in frozen['public_headers']:
    assert lifecycle.statement_hash(lifecycle.lean_declaration_header(test,r['declaration']))==r['normalized_header_sha256']
write(RUN/'canary-attempt-v3.lean.txt',test.read_bytes())
code,out=capture('canary-focused-build-v3','lake','build','Tests.OnlineAdaptiveSummationCanary',required=False)
write(RUN/'canary-attempt-inspected-v3.json',dict(Test=rows([test]),snapshot=rows([RUN/'canary-attempt-v3.lean.txt']),frozen_statements_unchanged=True,actual_build_exit=code,compiled=code==0,BODY_semantic_review='pending',chapter_complete=False))
print(out,flush=True)
fixed()
