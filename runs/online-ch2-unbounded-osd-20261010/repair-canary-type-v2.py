from leaf_driver import *
guard()
assert load(RUN/'canary-type-probe-v1.json')['actual_exit']==1
draft=load(CONTRACT/'canary-headers-draft-v1.json')
old='PiLp.single 0 1';new='PiLp.single 2 0 1'
assert draft['prefix'].count(old)==1
draft['prefix']=draft['prefix'].replace(old,new)
write(CONTRACT/'canary-headers-draft-v2.json',draft)
source=(RUN/'CanaryTypeProbeV1.lean').read_text(encoding='utf8')
assert source.count(old)==1
write(RUN/'CanaryTypeProbeV2.lean',source.replace(old,new))
write(RUN/'canary-type-repair-v2.json',dict(failure='PiLp.single has explicit Lp exponent argument; omitted2 incorrectly supplied0 as exponent',actual_primary_api='.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:149',repair='Set explicit p=2 for the same2D first-coordinate unit vector',headers_unchanged=True,production_definitions_unchanged=True,unfrozen_test_context_version=2))
code,out=capture('canary-type-probe-v2','lake','env','lean',RUN/'CanaryTypeProbeV2.lean',required=False)
write(RUN/'canary-type-probe-inspected-v2.json',dict(actual_exit=code,raw_stdout=out,types_only=True,bodies_lowered=False))
assert code==0
script=(RUN/'prepare-full-body-and-canary-v1.py').read_text(encoding='utf8')
exec(compile(script[:script.index("write(RUN/'FullPublicAuditV1.lean'")],str(RUN/'prepare-full-body-and-canary-v1.py')+':preflight','exec'))
tail=script[script.index("write(RUN/'full-body-obligations-v1.json'"):]
for old,new in [('canary-headers-draft-v1.json','canary-headers-draft-v2.json'),('CanaryTypeProbeV1.lean','CanaryTypeProbeV2.lean'),('canary-type-probe-v1.json','canary-type-probe-v2.json'),('canary-type-probe-inspected-v1.json','canary-type-probe-inspected-v2.json')]:
    tail=tail.replace(old,new)
exec(compile(tail,str(RUN/'prepare-full-body-and-canary-v1.py')+':repaired-type-tail-v2','exec'))
guard()
