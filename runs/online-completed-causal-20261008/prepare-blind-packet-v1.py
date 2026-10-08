from common_v1 import *

assert load(RUN/'draft-typecheck-v1-exit.json')['actual_exit']==0
write(RUN/'blind-targets-v1.lean.txt',(CONTRACT/'targets-v1.lean.txt').read_bytes())
context='Neutral scoped context only; no source title/pages/identity, proof, proposed route or prior verdict. Reused decoder history disclosed; this is a statement-only staged reconstruction, not absolute historical blindness.\n\n'
p=ROOT/'BanditRLProof/OnlineGuessingRandomizedIID.lean'
s=p.read_text(encoding='utf8');a=s.index('def privateSeedPastInformation');b=s.index('\n\n',a)
context+='```lean\n'+s[a:b]+'\n```\n\n'
p=ROOT/'BanditRLProof/OnlineGuessingIIDBenchmark.lean'
s=p.read_text(encoding='utf8');a=s.index('noncomputable def expectedFixedMinimum');b=s.index('\n/--',a)
context+='```lean\n'+s[a:b].rstrip()+'\n```\n\n'
context+='eventuallyMeasurableSpace F (ae mu) has exactly the sets A with some F-measurable B and A =^ae(mu) B. Measurable[F] means measurability for the explicitly supplied sigma field; mu keeps its ambient sigma field. Natural time0 has empty Finset.range0 history. Reconstruct all four full types and seven semantic slots, quantifier order, assumptions and degeneracies. Do not prove them or issue source acceptance. Write only blind-reconstruction-v1.md and blind-receipt-v1.json with exact input RAW before/after/reportSHA, actual reconstructed count and ambiguities.\n'
write(RUN/'blind-context-v1.md',context)
write(RUN/'blind-inputs-v1.json',dict(rows=raw_index([RUN/'blind-targets-v1.lean.txt',RUN/'blind-context-v1.md']),
    actor='/root/osd_blind',requested_model='GPT-6 Astra',requested_reasoning_effort='medium',runtime_attested=False,
    reused_actor_history_disclosed=True,source_identity_supplied=False,proof_supplied=False,prior_verdict_supplied=False))
print('Neutral decoder packet: two actual fixed RAW inputs; four statements, no proofs or source identity.',flush=True)
