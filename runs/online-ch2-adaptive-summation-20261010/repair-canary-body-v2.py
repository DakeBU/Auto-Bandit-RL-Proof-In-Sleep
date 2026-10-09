from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
canary=CONTRACT/'canary-v1';test=ROOT/'Tests/OnlineAdaptiveSummationCanary.lean'
frozen=load(canary/'stabilized-v1.json')
assert sha(PUBLIC)==frozen['production_sha256']
assert load(RUN/'canary-focused-build-v1.json')['actual_exit']==1
assert test.read_bytes()==(RUN/'canary-attempt-v1.lean.txt').read_bytes()
old=(RUN/'canary-main-body-attempt-v1.txt').read_text(encoding='utf8')
pattern='rw [intervalIntegral.integral_sub intervalIntegrable_const'
assert old.count(pattern)==1
body=old.replace(pattern,'rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun x : ℝ => x)\n          intervalIntegrable_const')
write(RUN/'canary-main-body-attempt-v2.txt',body)
write(RUN/'canary-body-repair-v2.json',dict(failure_receipt=rows([RUN/'canary-focused-build-v1.json']),failed_snapshot=rows([RUN/'canary-attempt-v1.lean.txt']),obstruction='Lean rewrite representation mismatch: continuous_id inferred integrand id, while target uses identity lambda. No mathematical or source-assumption defect.',repair='Specify the two functions f:=constant1,g:=identity-lambda in the existing integral_sub rewrite, preserving the same route and every frozen public conjunct.',header_context_unchanged=True,production_unchanged=True,chapter_complete=False))
event('canary-body-repair-event-v2','repair',dict(leaf='nonconstant_zero_increment_canary',evidence=(RUN/'canary-body-repair-v2.json').as_posix(),target_changed=False,route_changed=False))
context=(canary/'definition-context-draft-v1.lean.txt').read_text(encoding='utf8')
bodies=[body,(RUN/'canary-zero-body-attempt-v1.txt').read_text(encoding='utf8')]
source=context.replace('end Tests.OnlineAdaptiveSummationCanary\n','\n'.join(r['exact_header']+' := by\n'+b for r,b in zip(frozen['public_headers'],bodies))+'\nend Tests.OnlineAdaptiveSummationCanary\n')
test.write_bytes(source.encode('utf8'))
for r in frozen['public_headers']:
    assert lifecycle.statement_hash(lifecycle.lean_declaration_header(test,r['declaration']))==r['normalized_header_sha256']
write(RUN/'canary-attempt-v2.lean.txt',test.read_bytes())
code,out=capture('canary-focused-build-v2','lake','build','Tests.OnlineAdaptiveSummationCanary',required=False)
write(RUN/'canary-attempt-inspected-v2.json',dict(Test=rows([test]),snapshot=rows([RUN/'canary-attempt-v2.lean.txt']),frozen_statements_unchanged=True,actual_build_exit=code,compiled=code==0,BODY_semantic_review='pending',chapter_complete=False))
print(out,flush=True)
fixed()
