from common_v1 import *
fixed()
assert load(RUN/'causal-attempt-v2-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'snapshots/public-moments-v1.lean.raw').read_bytes()
PUBLIC.write_bytes((RUN/'leaves/causal-v2.lean').read_bytes())
write(RUN/'snapshots/public-causal-v1.lean.raw',PUBLIC.read_bytes())
gate('public-causal-build-v1','lake','build','BanditRLProof.OnlineGuessingLogLower')
fixed()
