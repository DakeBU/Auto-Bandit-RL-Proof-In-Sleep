from common import *
context='''import BanditRLProof.OnlinePrescientBregmanRegret
import Tests.OnlinePrescientBregmanCanary
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregmanRegretCanary
'''
text=(CONTRACT/'canary-targets-draft-v1.txt').read_text(encoding='utf8')
targets=[]; probe=context+'\n'
for part in text.split('-- TARGET ')[1:]:
    name,h=part.split('\n',1); h=h.strip()
    targets.append(dict(name=name,declaration='BanditRL.OnlinePrescientBregmanRegretCanary.'+name,exact_header=h,statement_sha256=hashlib.sha256(h.encode('utf8')).hexdigest(),file='Tests/OnlinePrescientBregmanRegretCanary.lean'))
    probe+=h.replace('theorem '+name+' :','#check',1)+'\n\n'
probe+='end BanditRL.OnlinePrescientBregmanRegretCanary\n'
write(CONTRACT/'canary-targets-draft-v1.json',dict(stage='draft',context=context,targets=targets,whole_Goal_status='ACTIVE'))
write(ROOT/'tmp/online-ch2-prescient-cumulative-canary-types-v1.lean',probe)
code,out=capture('canary-type-probe-command-v1','lake','env','lean','tmp/online-ch2-prescient-cumulative-canary-types-v1.lean',required=False)
assert code==0,(code,out)
defs=load(RUN/'neutral-statement-packet-v2.json')['canonical_definitions']
write(RUN/'canary-neutral-packet-v1.json',dict(context=context,targets=targets,canonical_definitions=defs,production_headers=load(CONTRACT/'stabilized-v1.json')['targets'],instruction='Reconstruct complete two proposed concrete conjunctions from exact statements only, no source identity/proof/verdict. Report all numeric/source-condition/actual-run/max and residual semantics; separate draft arithmetic from actual minimum proof. Related actor history disclosed, not absolute blindness.',requested_model='GPT-6 Astra',requested_effort='medium',runtime_attested=False))
write(RUN/'canary-plan-draft-v1.md','''# Two nondegenerate full public canary contracts, no bodies yet

Fixed actualtwo-currentlossrun reuses parent public canary facts, not its old regret conclusion. New sharedsum/sharpfixed/printedfixed values must actually occur in corresponding publicconjunction branches; numericaltails must retain new sharp/printed fixed values by Eq.mp or explicit normalization rather than standalone norm_num. Negative terminal at u=-1/2 is5/8; ordered movements11/64,9/64, sum5/16. Sourcepsi strict/closed/differentiableglobal and properrestrictedlosses/global supports explicitly audited; topoutsideV retained.

Decreasing actualsteps1,1/2 and changedsecondcurrentloss -5z/4 produce same distinctstates1/2,0,1/2. Must prove currentERealminima and uniquely selectedstates, not assume them; parentactualfirststep may be reused. Weightedmovements29/64, u=-1/2 terminal5/8/lasteta nonzero, finitepreviousMAX5/8; u=1/2 initial0 but previousMAX9/64, distinguishing initial-only and wrongindices. Fullvariable sharp usesexactfiniteMAX as M; printedboundsameMAX; numericaltail1 -7/4<=-29/64 must retain new sharpvalue, tail2 -1/2<=-11/64 must retain new printedvalue. No pointwise movement omitted. Sourceclosedpsi andglobal differentiability/proper/global supports included. All extrema/statements/pointvalues exact in frozen fullheaders, not counts.

No new named production/Testhelper definitions/theorems beyond two conjunctions. Local proof facts allowed. CompletecanaryVALUE graph plus independentlyselectednumericbranches required; root/Tests/harness/sourceFINAL/site/registry separate. Need distinct neutral decoder/sourcecanaryCONTRACTreview before bodies. Current production containsfirstleafonly; canarytypeprobe only Prop elaboration. Sourcecontainer/chapter/Goal OPEN.
''')
print('Two full canary draft headers elaborated; no bodies or acceptance.')
