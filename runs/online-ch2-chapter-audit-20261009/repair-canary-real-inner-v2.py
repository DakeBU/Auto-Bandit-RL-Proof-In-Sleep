from lower_common_v1 import *

reviewed(); headers(3)
test=ROOT/'Tests/OnlineNonsmoothExamplesCanary.lean'
r=load(RUN/'nonsmooth-canaries-focused-build-v1.json')
out=base64.b64decode(r['stdout_base64']).decode('utf8')
assert r['actual_exit']==1 and out.count('unsolved goals')==2
assert 'case refine_1' in out and 'case refine_2' in out
assert test.read_bytes()==(RUN/'nonsmooth-canaries-attempt-v1.lean').read_bytes()
write(RUN/'nonsmooth-canaries-failure-classification-v1.json',dict(
    actual_build_exit=1, failed_build_sha256=sha(RUN/'nonsmooth-canaries-focused-build-v1.json'),
    classification='representation normalization: two real inner-product rational margin equalities remain after norm_num; every other canary branch elaborated without reported error',
    repair='Use the definitionally equal scalar inner product w*3 in the two concrete margin equalities, then norm_num. No proposition or production proof change.',
    frozen_canary_contract_sha256=sha(CONTRACT/'nonsmooth-canary-contracts-v2.json'),
    goal_blocked=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
event('nonsmooth-canaries-repair-event-v1','repair',dict(
    leaf='five complementary canaries', actual_compiler_exit=1,
    failed_attempt_sha256=sha(RUN/'nonsmooth-canaries-attempt-v1.lean'),
    unchanged_terminal_hashes=True, classification='two scalar-inner normalization subgoals'))
s=test.read_text(encoding='utf8')
old='''    have h := (hp.2.1 (1 / 6)).mp hd
    norm_num [RCLike.inner_apply] at h'''
new='''    have h := (hp.2.1 (1 / 6)).mp hd
    apply h
    change (2 : ℝ) * ((1 / 6) * 3) = 1
    norm_num'''
assert s.count(old)==1;s=s.replace(old,new)
old='''    have h := (hn.2.1 (-1 / 6)).mp hd
    norm_num [RCLike.inner_apply] at h'''
new='''    have h := (hn.2.1 (-1 / 6)).mp hd
    apply h
    change (-2 : ℝ) * ((-1 / 6) * 3) = 1
    norm_num'''
assert s.count(old)==1;s=s.replace(old,new)
test.write_bytes(s.encode('utf8'))
for t in load(CONTRACT/'nonsmooth-canary-contracts-v2.json')['targets']:
    assert statement_hash(lean_declaration_header(test,t['declaration']))==t['statement_hash']
write(RUN/'nonsmooth-canaries-attempt-v2.lean',test.read_bytes())
capture('nonsmooth-canaries-focused-build-v2','lake','build','Tests.OnlineNonsmoothExamplesCanary',required=False)
reviewed(); headers(3)
print('Only two concrete proof normalization steps repaired; inspect actual build v2.')
