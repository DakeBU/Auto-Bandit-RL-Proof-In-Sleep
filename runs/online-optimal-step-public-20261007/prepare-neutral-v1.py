"""Closed source-neutral Props plus actual full type equality; no body acceptance."""
from common_v1 import *
fixed()
gate('actual-API-retrieval-v1','rg','-n','theorem (sq_sqrt|sqrt_sq|sqrt_pos|sqrt_mul)|theorem (gap_identity|source_argmin|diameter_argmin)|upperBound|optimalStep','.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean',PUBLIC,CANARY)
context='''import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
namespace NeutralScalar
noncomputable def F (A B z : ℝ) : ℝ := A / (2 * z) + z * B / 2
noncomputable def S (A B : ℝ) : ℝ := Real.sqrt A / Real.sqrt B
'''
defs=[];mapping=[]
for k,(n,h) in enumerate(load(CONTRACT/'headers-v1.json').items(),1):
 tail=h[len('theorem '+n):];depth=0;index=None
 for j,ch in enumerate(tail):
  if ch=='(':depth+=1
  elif ch==')':depth-=1
  elif ch==':' and depth==0:index=j;break
 assert index is not None and depth==0,n
 args=tail[:index].strip();prop=tail[index+1:].strip();neutral=prop.replace('upperBound','F').replace('optimalStep','S')
 q='Q'+str(k).zfill(2);defs.append('def '+q+' : Prop := ∀ '+args+',\n  '+neutral)
 mapping.append(dict(neutral=q,actual=PRE+n,raw_header_sha256=hashlib.sha256(h.encode()).hexdigest(),args=args))
scratch=context+'\n\n'.join(defs)+'\n'+'\n'.join('#check '+x['neutral'] for x in mapping)+'\nend NeutralScalar\n'
write(RUN/'leaves/neutral-closed-props-v1.lean',scratch)
gate('neutral-closed-props-v1','lake','env','lean',RUN/'leaves/neutral-closed-props-v1.lean')
actual='import BanditRLProof.OnlineOptimalStep\n'+scratch
for x in mapping:
 actual+='example : '+x['neutral'].join(['NeutralScalar.',''])+' := '+x['actual']+'\n'
 # FULL actual theorem type proposition is certified by rfl after neutral aliases unfold.
 actual+='example : NeutralScalar.'+x['neutral']+' = (∀ '+x['args']+', '+load(CONTRACT/'headers-v1.json')[x['actual'].removeprefix(PRE)].split(' :',1)[0]+') := by rfl\n' if False else ''
# Avoid theorem bodies in the true closed-type identity certificate: construct the actual quantified proposition directly.
identities='import BanditRLProof.OnlineOptimalStep\n'+scratch
for x,(n,h) in zip(mapping,load(CONTRACT/'headers-v1.json').items()):
 tail=h[len('theorem '+n):];depth=0
 for j,ch in enumerate(tail):
  if ch=='(':depth+=1
  elif ch==')':depth-=1
  elif ch==':' and depth==0:break
 prop=tail[j+1:].strip().replace('upperBound',PRE+'upperBound').replace('optimalStep',PRE+'optimalStep')
 identities+='example : NeutralScalar.'+x['neutral']+' = (∀ '+x['args']+', '+prop+') := by rfl\n'
write(RUN/'leaves/full-type-identities-v1.lean',identities)
gate('full-type-identities-v1','lake','env','lean',RUN/'leaves/full-type-identities-v1.lean')
write(RUN/'neutral-map-v1.json',mapping)
write(RUN/'blind-packet-v1.md','''# Source-blind reconstruction packet
Requested GPT-6 Astra/medium; no model/effort runtime attestation or prior source identity. Reused prior neutral-decoder history must be disclosed. Read ONLY this packet. Reconstruct EACH Q01-Q11 as a universally quantified mathematical statement in natural language and LaTeX, with all seven semantic slots: objects; quantifiers; assumptions; conclusion; constants/indices; operation/information; boundaries. These are CLOSED Props, not proofs; do not infer a named source, theorem identity, prior verdict or body acceptance. F,S are total real functions. Distinguish nonnegative coefficients versus strict positive regimes, admissible z>0 versus total division at0, fixed coefficients versus data dependence and scalar objects versus any unspecified algorithm. Do not invent domain/loss/learner/probability hypotheses absent from the terms.

```lean
'''+scratch+'''```

Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this packet's run. Receipt actor.task=/root/osd_blind, packet path/rawSHA, report path/rawSHA, Q01-Q11 covered, prior_history_disclosure and requested/runtime boundary. No source identity search or proof/review verdict. No other file edits.''')
write(RUN/'neutral-type-bindings-v1.json',dict(status='actual11closedProps-and-fulltype-rfl-passed',packet_sha256=sha(RUN/'blind-packet-v1.md'),mapping_sha256=sha(RUN/'neutral-map-v1.json'),source_public_sha256=sha(PUBLIC),new_proofs=0,new_definitions=0,source_review_pending=True,not_proof_body_or_fidelity_evidence=True))
fixed();print('Actual11 closed neutral Props/full type identities rfl compiled; distinct decoder/source review pending.')
