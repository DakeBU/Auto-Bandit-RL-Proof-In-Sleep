from common_v2 import *
fixed();targets=load(CONTRACT/'headers-v2.json')
gate('local-API-search-v3','rg','-n','lemma_2_31|SourceSubdifferential|support_value_finite|finite_loss|history_selected|output_linear_run|regret_comparison|regret_transfer|canonical_feedback|inner_sub_right','BanditRLProof/OnlineLinearization.lean','BanditRLProof/OnlineSubgradientDescent.lean','BanditRLProof/OnlineSubgradientPolicy.lean','BanditRLProof/OnlineSubgradientBasic.lean')
gate('mathlib-API-search-v3','rg','-n','theorem inner_sub_right|theorem sum_le_sum|snoc_castSucc|snoc_last','.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean','.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean','.lake/packages/mathlib/Mathlib/Data/Fin/VecNotation.lean')
write(RUN/'reuse-decision-v3.md','Actual scoped project/mathlib declaration search and full closed-proposition probes. Reuse existing18 public proofs/9defs/3abbr and whole25canary proofs/8defs/2abbr; zero new mathematical results/definitions/registry nodes. Shared actual support_gap eta1, causal Nat.rec/Fin.snoc, same learner run, global proper finite support and optional/canonical legality producers. No compatible pinned LML/Optlib dependency or externally rebuilt theorem is certified; unchanged Lean/mathlib4.29.1.')
def split(h,n):
 s=h[len('theorem '+n):];depth=0
 for i,ch in enumerate(s):
  if ch in '([{':depth+=1
  elif ch in ')]}':depth-=1
  elif ch==':' and depth==0:return s[:i].rstrip(),s[i+1:].strip()
 raise ValueError(n)
def rename(s):
 for a,b in [('BanditRL.OnlineSubgradientDescent.SubdifferentiableOn','Regular'),('BanditRL.OnlineSubgradientPolicy.OracleLaw','Law'),('BanditRL.OnlineSubgradientPolicy.canonicalPolicy','Default'),('BanditRL.OnlineLearning.comparatorRegret','Comparator'),('SourceSubdifferential','Supports')]:s=s.replace(a,b)
 return s
actualcontext=(CONTRACT/'actual-context-v1.txt').read_text(encoding='utf-8');actualcontext=re.sub(r'/-![\s\S]*?-/', '',actualcontext)
neutralcontext=actualcontext.replace('namespace BanditRL.OnlineLinearization','namespace NeutralPacket')
neutralcontext=rename(neutralcontext)
at=neutralcontext.index('variable {E : Type*}');head=neutralcontext[:at];rest=neutralcontext[at:]
aliases='''abbrev Supports {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (x : E) := BanditRL.OnlineConvex.SourceSubdifferential f x
abbrev Regular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (V : BanditRL.OnlineGradientDescent.Domain E) (f : E → EReal) := BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f
abbrev Law {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (V : BanditRL.OnlineGradientDescent.Domain E) (p : BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)) := BanditRL.OnlineSubgradientPolicy.OracleLaw V p
abbrev Default {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] := BanditRL.OnlineSubgradientPolicy.canonicalPolicy (E := E)
abbrev Comparator {E : Type*} (loss : ℕ → E → ℝ) (prediction : ℕ → E) (u : E) (T : ℕ) := BanditRL.OnlineLearning.comparatorRegret loss prediction u T
'''
neutralcontext=head+aliases+rest
neutral=[];actual=[];mapping={}
for i,(n,h) in enumerate(targets.items(),1):
 args,c=split(h,n);neutral.append(f'def Q{i:02d} : Prop :=\n  ∀'+rename(args)+',\n  '+rename(c));actual.append(f'def S{i:02d} : Prop :=\n  ∀'+args+',\n  '+c);mapping[f'Q{i:02d}']=PRE+n
neutraltext=neutralcontext+'\n\n'.join(neutral)+'\n'+''.join(f'#check Q{i:02d}\n' for i in range(1,19))+'end NeutralPacket\n'
write(RUN/'leaves/neutral-propositions-v3.lean',neutraltext)
gate('neutral-propositions-v3','lake','env','lean',RUN/'leaves/neutral-propositions-v3.lean')
lines=neutraltext.splitlines();imports=[s for s in lines if s.startswith('import ')];body='\n'.join(s for s in lines if not s.startswith('import '))
act=actualcontext.replace('namespace BanditRL.OnlineLinearization','namespace CurrentClosedTypes');act='\n'.join(s for s in act.splitlines() if not s.startswith('import '))+'\n'+'\n\n'.join(actual)+'\nend CurrentClosedTypes\n'
bridge='\n'.join(imports)+'\n'+body+'\n'+act+'\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]\n'+''.join(f'example : NeutralPacket.Q{i:02d} (E := E) = CurrentClosedTypes.S{i:02d} (E := E) := rfl\n' for i in range(1,19))
write(RUN/'leaves/closed-type-comparison-v3.lean',bridge);gate('closed-type-comparison-v3','lake','env','lean',RUN/'leaves/closed-type-comparison-v3.lean')
write(RUN/'neutral-map-v3.json',mapping)
write(RUN/'closed-type-comparison-v3.json',dict(status='all eighteen full closed propositions definitionally equal under explicit map',actual_command_receipt=RUN.joinpath('closed-type-comparison-v3-exit.json').as_posix(),neutral_file_sha256=sha(RUN/'leaves/neutral-propositions-v3.lean'),bridge_sha256=sha(RUN/'leaves/closed-type-comparison-v3.lean'),actual_target_proofs=False,source_fidelity_not_implied=True))
semantics='''Complete semantic context: E finite-dimensional real Euclidean space. Domain is shared nonempty closed convex set with carrier field, no boundedness. Proper(f) = (forall x, f(x) != bottom) and (exists x exists r:Real, f(x)=(r:EReal)). Supports(f,x) means forall v:E, f(x)+(inner g(v-x):EReal)<=f(v). Regular(V,f)=Proper(f) and every x in V has a nonempty global support set. SupportPolicy p: t -> finite t past whole functions -> finite (t+1) reconstructed outputs -> whole current function -> vector. Law(V,p) states forall t,past,h,f, Regular(V,f) and h(last t) in V -> p(t,past,h,f) in Supports(f,h(last t)); it is an optional off-path law. Default p ignores past and chooses from nonempty current global Supports by Classical.choose, otherwise0. Comparator(loss,prediction,u,T) is the difference of played and comparator sums over range T. A fixed finite-vector learner reads only strict past vectors. All supplied recursion definitions are literal and complete below. EReal.toReal is totalized, so finite-value derivation must not be omitted. No comparator/future functions queried by A/p; external construction of A/p has no independent stochastic-law guarantee. T0 empty extension; indexing0based. Decode only mathematics, no claimed source fidelity/acceptance.'''
write(RUN/'blind-packet-v3.md','Decode ONLY this neutral complete packet. Source identity/theorem names/prior source verdict withheld. Requested GPT-6 Astra/medium, runtime not attested; disclose any prior neutral-decoder history. Do not inspect repository/source/search/network/other packets. Return allQ01..Q18 full NL and LaTeX reconstruction with seven semantic slots, quantifiers/regularity/current and past inputs/full actual recursion/comparator and finite conversion/universal guarantee boundary/degeneracies. No source acceptance claim.\n\n'+semantics+'\n```lean\n'+neutraltext+'```\n')
fixed();print('Actual API search and eighteen full closed-type identities pass; source-blind packet frozen; source fidelity remains separate.')
