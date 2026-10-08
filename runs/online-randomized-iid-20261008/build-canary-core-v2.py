from common_reviewed_v2 import *

headers_fixed(7)
assert load(RUN/'R007-focused-build-v2-exit.json')['exit_code']==0
write(RUN/'leaves'/'canary-core-v2.lean',CANARY.read_bytes())
gate('canary-core-focused-build-v2','lake','build','Tests.OnlineGuessingRandomizedIIDCanary')
print('Core nondegenerate seeded infinite IID canary built; XOR joint-dependence boundary remains required.')
