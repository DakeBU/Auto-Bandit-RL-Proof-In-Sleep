"""Actual declaration searches and twelve closed neutral propositions; no theorem-body productivity."""
from common_v1 import *
fixed();targets=load(CONTRACT/'headers-v1.json')
gate('local-API-search-v1-01','rg','-n','SourceSubdifferential|currentSubgradient|iterate_prefix|regret_tuned|loss_subgradient|example_2_32','BanditRLProof','-g','OnlineGuessing*.lean','-g','OnlineSubgradientDescent.lean','-g','OnlineSubgradientAbsolute.lean','-g','OnlineSubgradientBasic.lean')
gate('mathlib-API-search-v1-01','rg','-n','tendsto_sqrt_atTop|tendsto_inv_atTop_zero|abs_le','.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean','.lake/packages/mathlib/Mathlib/Topology/Algebra/Order/Field.lean')
write(RUN/'reuse-decision-v1.md','Actual scoped local/Mathlib API search plus typed closed-target probe: reuse all twelve existing canonical absolute-loss proofs/one definition and their shared current-choice producer/true projection/whole support equalities. New arbitrary played-legal history-policy family is already accepted PR182; do not create duplicate wrappers. Current publication audit adds zero proofs/definitions/source-mathematical closures. Mathlib sqrt and reciprocal limit APIs are actual pinned dependencies. Lean/mathlib4.29.1 pins unchanged; no compatible pinned LML/Optlib dependency or externally rebuilt theorem is certified.')
def split(h,n):
 s=h[len('theorem '+n):];depth=0
 for i,ch in enumerate(s):
  if ch in '([{':depth+=1
  elif ch in ')]}':depth-=1
  elif ch==':' and depth==0:return s[:i].rstrip(),s[i+1:].strip()
 raise ValueError(n)
def rename(s):
 s=s.replace('BanditRL.OnlineGradientDescent.unitInterval','A')
 for a,b in [('SourceSubdifferential','S'),('SubdifferentiableOn','W'),('currentSubgradient','q'),('iterate','z'),('step','s'),('loss','b')]:s=re.sub(r'\b'+a+r'\b',b,s)
 return s
context='''import BanditRLProof.OnlineSubgradientDescent
import BanditRLProof.OnlineSubgradientAbsolute
import BanditRLProof.OnlineGuessingOGD
noncomputable section
open Set Finset Filter
namespace NeutralRealLoss
abbrev S (f : ℝ → EReal) (x : ℝ) : Set ℝ := BanditRL.OnlineConvex.SourceSubdifferential f x
abbrev A := BanditRL.OnlineGradientDescent.unitInterval
abbrev W (V : BanditRL.OnlineGradientDescent.Domain ℝ) (f : ℝ → EReal) : Prop := BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f
abbrev q (f : ℝ → EReal) (x : ℝ) : ℝ := BanditRL.OnlineSubgradientDescent.currentSubgradient f x
abbrev s (V : BanditRL.OnlineGradientDescent.Domain ℝ) (η : ℝ) (f : ℝ → EReal) (x : ℝ) : ℝ := BanditRL.OnlineSubgradientDescent.step V η f x
abbrev z (V : BanditRL.OnlineGradientDescent.Domain ℝ) (η : ℕ → ℝ) (f : ℕ → ℝ → EReal) (x₁ : ℝ) (t : ℕ) : ℝ := BanditRL.OnlineSubgradientDescent.iterate V η f x₁ t
def b (y x : ℝ) : EReal := ((|x - y| : ℝ) : EReal)
'''
neutral=[];actual=[];mapping={}
for i,(n,h) in enumerate(targets.items(),1):
 args,c=split(h,n);neutral.append(f'def Q{i:02d} : Prop :=\n  ∀'+rename(args)+',\n  '+rename(c));actual.append(f'def S{i:02d} : Prop :=\n  ∀'+args+',\n  '+c);mapping[f'Q{i:02d}']=PRE+n
neutraltext=context+'\n\n'.join(neutral)+'\n'+''.join(f'#check Q{i:02d}\n' for i in range(1,13))+'end NeutralRealLoss\n'
write(RUN/'leaves/neutral-propositions-v1.lean',neutraltext)
gate('neutral-propositions-v1-01','lake','env','lean',RUN/'leaves/neutral-propositions-v1.lean')
# Imports are deliberately all first. These are proposition identities under an
# explicit definition map, not closed proofs of the twelve source targets.
lines=neutraltext.splitlines();imports=[s for s in lines if s.startswith('import ')];imports.append('import BanditRLProof.OnlineGuessingSubgradient')
body='\n'.join(s for s in lines if not s.startswith('import '))
actualtext='noncomputable section\nopen Set Finset Filter BanditRL.OnlineConvex BanditRL.OnlineSubgradientDescent\nnamespace CurrentClosedTypes\nopen BanditRL.OnlineGuessingSubgradient (loss)\n'+'\n\n'.join(actual)+'\nend CurrentClosedTypes\n'
bridge='\n'.join(imports)+'\n'+body+'\n'+actualtext+''.join(f'example : NeutralRealLoss.Q{i:02d} = CurrentClosedTypes.S{i:02d} := rfl\n' for i in range(1,13))
write(RUN/'leaves/closed-type-comparison-v1.lean',bridge)
gate('closed-type-comparison-v1-01','lake','env','lean',RUN/'leaves/closed-type-comparison-v1.lean')
write(RUN/'neutral-map-v1.json',mapping)
write(RUN/'closed-type-comparison-v1.json',dict(status='all12 full closed propositions definitionally equal under explicit map',actual_command_receipt=RUN.joinpath('closed-type-comparison-v1-01-exit.json').as_posix(),neutral_file_sha256=sha(RUN/'leaves/neutral-propositions-v1.lean'),bridge_file_sha256=sha(RUN/'leaves/closed-type-comparison-v1.lean'),actual_target_proofs=False,source_fidelity_not_implied=True,public_headers_unchanged=True))
semantics='''Complete mathematical alias context for decoding (source identity deliberately withheld): ℝ is a real Euclidean scalar, EReal extended reals; b(y,x) is finite |x-y|. S(f,x)={g | ∀v:ℝ, f(x)+(inner ℝ g(v-x):EReal)≤f(v)} is a GLOBAL support set. A is the nonempty closed convex Domain with carrier[0,1]; projection selects the unique norm-distance minimizer via existing complete-convex projection existence. Proper(f)=(∀x,f(x)≠bottom) ∧ ∃x∃r:ℝ,f(x)=(r:EReal). W(V,f)=Proper(f) ∧ ∀x∈V.carrier,S(f,x).Nonempty. q(f,x)=if the whole support set is nonempty then Classical.choose a membership witness else0. s(V,eta,f,x)=project(V,x-eta•q(f,x)). z(V,eta,F,x1,0)=x1; z(...,t+1)=s(V,eta(t),F(t),z(...,t)). These are exact aliases of supplied compiled project definitions, not independent axioms or theorem premises. Current q receives only the whole current function and point; explicit recursion contains no future loss or comparator input. Externally chosen eta/x1 remain parameters, no selection-independence certificate. EReal.toReal is a totalization; finite abs embedding prevents infinite-value fallback here. Zero-based finite range and eventual natural atTop filters are literal.
'''
write(RUN/'blind-packet-v1.md','Decode only this complete neutral packet; no source identity/theorem-number/original theorem-name/prior verdict supplied. Requested GPT-6 Astra/medium, no runtime attestation. Disclose any prior neutral-decoder history. Do not inspect repository/source/search/network/other packets. Return all12 Q01..Q12 full natural-language and LaTeX reconstruction, all quantifiers/assumptions/seven slots, exact whole-set/one-sided/family/input-order/initial-value/degenerate boundaries; neutral semantics only, no claimed source fidelity or acceptance.\n\n'+semantics+'\n```lean\n'+neutraltext+'```\n')
fixed();print('Actual API retrieval and twelve full closed type identities pass; neutral source-blind packet frozen, source fidelity separate.')
