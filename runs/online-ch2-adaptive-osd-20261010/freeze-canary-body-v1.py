from common import *
public=ROOT/'Tests/OnlineAdaptiveOSDCanary.lean'
write(RUN/'algorithm-canary-BODY-frozen-v1.lean.txt',public.read_bytes())
files=[public,RUN/'algorithm-canary-BODY-frozen-v1.lean.txt',CONTRACT/'algorithm-canary-stabilized-v1.json',CONTRACT/'algorithm-canary-context-draft-v2.lean.txt',CONTRACT/'algorithm-canary-neutral-packet-v1.lean.txt',CONTRACT/'algorithm-canary-source-card-draft-v1.md',RUN/'benchmark-BODY-canary-CONTRACT-review-v1.json']
files += list(RUN.glob('algorithm-canary-*-focused-build-v*.json'))
files += list(RUN.glob('algorithm-canary-*-body-attempt-v*.lean.txt'))
write(RUN/'algorithm-canary-BODY-proof-context-v1.json',dict(files=rows(files),scope='All seven frozen complete canaries; distinct BODY review pending; original verifier running separately; no native acceptance/full chapter assertion'))
print(sha(public))
