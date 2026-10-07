from common_v1 import *
fixed()
assert load(RUN/'deterministic-attempt-v2-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'snapshots/public-loss-bridge-v1.lean.raw').read_bytes()
PUBLIC.write_bytes((RUN/'leaves/deterministic-v2.lean').read_bytes())
write(RUN/'snapshots/public-deterministic-v1.lean.raw',PUBLIC.read_bytes())
gate('public-deterministic-build-v1','lake','build','BanditRLProof.OnlineGuessingLogLower')
fixed()
