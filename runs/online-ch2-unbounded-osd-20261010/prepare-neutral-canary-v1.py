from common import *
fixed()
assert load(RUN/'canary-type-probe-v2.json')['actual_exit']==0
draft=load(CONTRACT/'canary-headers-draft-v2.json')
defs=(CONTRACT/'definitions-draft-v1.lean').read_text(encoding='utf8')
shared=(ROOT/'BanditRLProof/OnlineSubgradientDescent.lean').read_text(encoding='utf8')
shared=shared[shared.index('def currentSubgradient'):shared.index('theorem lemma_2_31')]
def neutral(s):
    return s.replace('BanditRL.OnlineUnboundedOSDCanary','NeutralProbe').replace('BanditRL.OnlineUnboundedOSD','NeutralContext')
packet=dict(kind='Exact source-withheld canary type/context reconstruction, no proof',inputs_allowed='Only this packet; no source or source review or live new theorem bodies',producer_definitions=neutral(defs),shared_algorithm_definitions=shared,canary_context=neutral(draft['prefix']),claims=[dict(name='claim'+str(i+1),statement=neutral(row['header']).replace(row['name'].rsplit('.',1)[1],'claim'+str(i+1))) for i,row in enumerate(draft['targets'])],scope_note='Reused staged decoder with related earlier type reconstruction history. No source theorem identity, prior verdict or actual proof is supplied. Reconstruct all conjuncts and causal/update scoring semantics. Do not infer mathematical truth from typing; no proof/lifecycle acceptance.')
write(RUN/'canary-neutral-packet-v1.json',packet)
write(RUN/'canary-neutral-inputs-v1.json',dict(packet=rows([RUN/'canary-neutral-packet-v1.json']),actual_typed_context=rows([CONTRACT/'canary-headers-draft-v2.json',RUN/'CanaryTypeProbeV2.lean',RUN/'canary-type-probe-v2.json']),decoder_read_only='canary-neutral-packet-v1.json ONLY',allowed_output=['canary-blind-reconstruction-v1.md','canary-blind-reconstruction-v1.json']))
fixed()
