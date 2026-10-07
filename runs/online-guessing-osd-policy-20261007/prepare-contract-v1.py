from common_v1 import *
fixed()
context='''import BanditRLProof.OnlineGuessingSubgradient
import BanditRLProof.OnlineSubgradientPolicy

noncomputable section
open Set Finset Filter BanditRL.OnlineConvex
open BanditRL.OnlineSubgradientPolicy
open BanditRL.OnlineGuessingSubgradient (loss loss_subgradient_bound loss_on_unitInterval)
open BanditRL.OnlineGradientDescent (unitInterval)
namespace BanditRL.OnlineGuessingSubgradientPolicy
'''
targets={
'selected_bound':'''theorem selected_bound (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : SupportPolicy (E := ℝ)) (T : ℕ)
    (hlegal : LegalFeedback unitInterval η (fun s => loss (y s)) x₁ p T)
    (t : ℕ) (ht : t < T) :
    ‖selected unitInterval η (fun s => loss (y s)) x₁ p t‖ ≤ 1''',
'step_clamp':'''theorem step_clamp (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : SupportPolicy (E := ℝ)) (t : ℕ) :
    output unitInterval η (fun s => loss (y s)) x₁ p (t + 1) =
      min (max (output unitInterval η (fun s => loss (y s)) x₁ p t -
        η t * selected unitInterval η (fun s => loss (y s)) x₁ p t) 0) 1''',
'example_2_32':'''theorem example_2_32 (y : ℕ → ℝ) (x₁ : ℝ) (p : SupportPolicy (E := ℝ))
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : LegalFeedback unitInterval (fun _ => 1 / Real.sqrt T)
      (fun s => loss (y s)) x₁ p T) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|output unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ p t - y t| - |u - y t|)) ≤ Real.sqrt T''',
'example_2_32_average_eventually':'''theorem example_2_32_average_eventually (y : ℕ → ℝ) (x₁ : ℝ)
    (p : SupportPolicy (E := ℝ)) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : ∀ T : ℕ, 0 < T → LegalFeedback unitInterval
      (fun _ => 1 / Real.sqrt T) (fun s => loss (y s)) x₁ p T)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|output unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ p t - y t| - |u - y t|)) / T < ε'''
}
write(CONTRACT/'headers-v1.json',targets)
write(CONTRACT/'raw-statement-fingerprints-v1.json',{n:hashlib.sha256(v.encode()).hexdigest() for n,v in targets.items()})
write(CONTRACT/'public-context-v1.txt',context)
write(CONTRACT/'draft-statements-v1.lean.txt',context+'\n\n'.join(targets.values())+'\nend BanditRL.OnlineGuessingSubgradientPolicy')
write(CONTRACT/'contract-v1.md','''# Example2.32 legal history-policy contract v1
Source pinned to Orabona arXiv1912.13213v10,21June2026, SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Example2.32 printed20/PDF32 states the absolute-loss support branches {1}/[-1,1]/{-1} and O(sqrtT) regret using OSD. The original guessing game printed1-3/PDF13-15 supplies predictions/labels/comparators in [0,1], loss revealed after current prediction. Algorithm2.2 permits any actual global support; printed19/PDF31 transfers Theorem2.13/eq2.1. Exact finite sqrtT with eta=1/sqrtT is the D=G=1 specialization of that transfer; the source example itself prints asymptotic upper growth, not this finite inequality verbatim.
Existing shifted absolute loss and all-support norm<=1 results, nonempty properness, [0,1] domain/projection, canonical12 declarations and full-history policy21/recursion are byte-frozen reused dependencies. No loss/history/policy/domain/projection definition is duplicated. New4 exact types in headers-v1.json: played-support norm producer; actual arbitrary-rate clamp identity; generic finite-horizon all-comparator sqrtT terminal; explicitly derived one-sided eventual-average horizon-family corollary.
The policy p is fixed exogenous deterministic full-information: t, exactly Fin t past whole loss functions, Fin(t+1) past/current played outputs, current whole loss. Nat.rec appends actual nearest projection. Current loss does not enter the current output. LegalFeedback means true global support membership only at the played queries of THIS SAME eta=1/sqrtT run, not a supplied regret/stability/trajectory certificate. No universal off-path OracleLaw requirement. Every choice factoring through these finite inputs is covered; p may close over external parameters whose selection is not certified by prefix lemmas. No probability/measurability/filtration/finite-query-execution/parameter-independence inference.
selected_bound needs neither feasible initial state nor bounded labels nor positive rates, because the reused absolute global-support bound holds at every real point. step_clamp is an unconditional actual update identity at all rates/labels/initial values; these are explicit algebraic generalizations, not performance claims. Performance keeps source x1,played y,u in [0,1], T>0 and legal played supports. hy is intentionally retained although norm<=1 holds for every real label; it does not get deleted as unused. T0/division-zero is excluded for tuned performance. Same fixed p/x1, each horizon has its separately prescribed constant rate and potentially different path; eventual upper-average <epsilon is NOT signed Tendsto0, absolute BigO, or one common anytime sequence. Uniform all-comparator bound uses one common run independent of u. Source round1 is Lean0, output T is x_(T+1).
Single lower route: existing absolute norm producer -> selected norm on played path; output_succ/project_unitInterval -> clamp; existing regret_tuned same-run D=G=1 plus actual norm and true diameter -> finite real loss conversion -> terminal; reciprocal sqrt limit -> one-sided average corollary. Core fixed/variable bounds retain negative endpoint; this source example upper bound may drop it through the reviewed tuned core. No strengthened smoothness/Lipschitz-boundary hypothesis.
Conversion window fixed: extended-real finite real embedding; scalar global support; zero-based finite history; actual projected deterministic policy; fixed comparator; finite versus eventual conclusion; denominator/positive-horizon boundary. Headers/source/math signature immutable after stabilization; any change gets new version and separate review. Draft/architect/worker may be staged ROOT medium; blind decoder/source reviewer distinct mandatory actors with prior-context disclosure, no independent human/external review claim.
Allowed mutations: OWN newrun/contract/task/conversion/obligations/retrieval/manifest and OWN native journal rows; new public module/canary and additive exact imports; online-guessing-osd reader route only after gates. Existing module bodies/old evidence/contracts, other Book subtrees/old IDs+URLs, pins/SGB/shared junctions, generated _site/private papers/anonymous snapshots protected. Exact OPEN draft PR181 base8ce8cc58, not canonical main integration. Chapter1/2 total incomplete and mandatory gaps retained;3-16 unenumerated; whole Goal active. New closed family terminal is progress, helper counts are not. Existing canonical public migration remains a distinct publication obligation unless independently discharged by actual evidence.
''')
write(CONTRACT/'dependency-DAG-v1.json',dict(ready_dependencies=['BanditRL.OnlineGuessingSubgradient.loss','BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound','BanditRL.OnlineGuessingSubgradient.loss_on_unitInterval','BanditRL.OnlineSubgradientPolicy.output_succ','BanditRL.OnlineSubgradientPolicy.regret_tuned','BanditRL.OnlineGradientDescent.project_unitInterval'],leaves=[dict(id='selected_bound',depends_on=['loss_subgradient_bound'],ready=True),dict(id='step_clamp',depends_on=['output_succ','project_unitInterval'],ready=True),dict(id='example_2_32',depends_on=['selected_bound','loss_on_unitInterval','regret_tuned'],ready_after=['selected_bound']),dict(id='example_2_32_average_eventually',depends_on=['example_2_32','Real.tendsto_sqrt_atTop','tendsto_inv_atTop_zero'],ready_after=['example_2_32'])],chapter_complete=False,goal_complete=False))
write(RUN/'director-v1.md','Source theorem-sized delta is missing arbitrary played-legal history-policy Example2.32 terminal, not fresh creation of old canonical12 proofs. Prioritize same-run finite regret, then its dependent one-sided horizon-family corollary. One lower route, no other chapter proof writes; chapter/whole Goal remains active. ROOT staged role, requested medium, runtime unverified.')
write(RUN/'architect-v1.md','Reuse scalar absolute global supports, true unit interval projection and causal finite-history recurrence. Norm uses actual selected membership and proves <=1; no assumed regret. Existing regret_tuned consumes this producer with D=G=1 on the same eta run. Clamp supports nondegenerate public trajectory test. Terminal feeds eventual upper-average via reciprocal sqrt. No separate per-book tree, no toolchain/Optlib changes. Exact types/source fingerprints and ready DAG frozen before body work. ROOT staged role, requested medium.')
write(Path('conversion-windows')/(TASK+'.md'),(CONTRACT/'contract-v1.md').read_bytes())
write(Path('proof-obligations')/(TASK+'.json'),dict(task=TASK,contract=CONTRACT.as_posix(),stage='draft',leaves=[dict(id=n,status='pending',header_sha256=hashlib.sha256(v.encode()).hexdigest()) for n,v in targets.items()],required_remaining=['canonical Example2.32 publication migration','linearization and unit-analysis current publication gates','remaining Chapter1/2 obligations and nine OTHERChapter1 main-relative contracts','necessary appendix dependencies','Chapters3-16 enumeration and proof gates'],chapter_complete=False,goal_complete=False))
# Typed neutral descriptions reuse the exact shared causal definitions; no source title,
# source theorem number, proof body or prior source verdict enters the decoder packet.
neutral_context='''import BanditRLProof.OnlineSubgradientPolicy
noncomputable section
open Set Finset Filter BanditRL.OnlineConvex
namespace NeutralScalarHistory
abbrev W := BanditRL.OnlineGradientDescent.unitInterval
abbrev F := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := ℝ)
abbrev X := BanditRL.OnlineSubgradientPolicy.output
abbrev A := BanditRL.OnlineSubgradientPolicy.selected
abbrev L := BanditRL.OnlineSubgradientPolicy.LegalFeedback
def b (y x : ℝ) : EReal := ((|x-y| : ℝ) : EReal)
'''
rename={'unitInterval':'W','SupportPolicy (E := ℝ)':'F','LegalFeedback':'L','selected':'A','output':'X','loss':'b'}
neutral=[]
for i,(name,h) in enumerate(targets.items(),1):
 args,conclusion=h[len('theorem '+name):].rsplit(' :\n',1)
 text='def Q%02d : Prop :=\n  ∀'%i+args+',\n'+conclusion
 for old,new in rename.items():text=re.sub(r'\b'+re.escape(old)+r'\b',new,text) if old.isidentifier() else text.replace(old,new)
 neutral.append(text)
neutral_text=neutral_context+'\n\n'.join(neutral)+'\nend NeutralScalarHistory\n'
write(RUN/'leaves/neutral-types-v1.lean',neutral_text)
shared=Path('BanditRLProof/OnlineSubgradientPolicy.lean').read_text(encoding='utf-8').split('\ntheorem history_zero')[0]
shared=shared[shared.index('noncomputable section'):]
support=Path('BanditRLProof/OnlineSubgradientBasic.lean').read_text(encoding='utf-8')
start=support.index('def SourceSubdifferential') if 'def SourceSubdifferential' in support else -1
support_excerpt=support[start:start+420] if start>=0 else 'Global supports compare the loss at every z in ambient real space, not only feasible points.'
write(RUN/'blind-packet-v1.md','''Restricted source-blind packet. Read ONLY this packet. No source/proof/prior verdict/repo search. Requested GPT6Astra/medium, runtime attestation unavailable. Reconstruct Q01-Q04 individually in natural language and LaTeX and all seven semantic slots. Disclose inherited neutral-decoder context; do not infer source identity or acceptance. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json beside this file; raw packet/report SHA256 and actor.task=/root/osd_blind. The displayed definitions are mathematical context, not assumed performance results.
W is the nonempty closed convex [0,1] real domain and its project is actual nearest projection. b is a finite-real-to-EReal embedding. EReal.toReal sends both infinities to zero, but b is finite everywhere. F/X/A/L are abbreviations of the exact following common definitions at E=real. A deterministic exogenous fixed policy uses finite past whole losses and outputs plus current whole loss. Global support tests every ambient point. No source label is supplied.
Shared context:
```lean
'''+shared+'\n'+support_excerpt+'\n```\nTyped proposition descriptions (no proofs):\n```lean\n'+neutral_text+'\n```\n')
write(RUN/'neutral-to-actual-map-v1.json',dict(map={f'Q{i:02d}':'BanditRL.OnlineGuessingSubgradientPolicy.'+n for i,n in enumerate(targets,1)},definition_map=rename,blind_learned_source_identity=False))
probe='''import BanditRLProof.OnlineGuessingSubgradient
import BanditRLProof.OnlineSubgradientPolicy
set_option pp.universes true
'''
for name in ['BanditRL.OnlineGuessingSubgradient.loss','BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound','BanditRL.OnlineGuessingSubgradient.loss_on_unitInterval','BanditRL.OnlineSubgradientPolicy.output_succ','BanditRL.OnlineSubgradientPolicy.regret_tuned','BanditRL.OnlineSubgradientPolicy.regret_fixed','BanditRL.OnlineSubgradientPolicy.canonical_output','BanditRL.OnlineGradientDescent.project_unitInterval','Real.tendsto_sqrt_atTop','tendsto_inv_atTop_zero']:probe+='#check @'+name+'\n'
write(RUN/'leaves/retrieval-probe-v1.lean',probe)
gate('retrieval-probe-v1-01','lake','env','lean',RUN/'leaves/retrieval-probe-v1.lean')
gate('neutral-types-v1-01','lake','env','lean',RUN/'leaves/neutral-types-v1.lean')
native('retrieval-record-v1-01','retrieval-record','--task',TASK,'--query','absolute loss actual finite-history played legal policy same-run horizon sqrtT','--candidate','BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound','--candidate','BanditRL.OnlineSubgradientPolicy.regret_tuned','--compiled-scratch',str(RUN/'leaves/retrieval-probe-v1.lean'),'--provenance','Exact compiled public API types in pinned shared project; no unchecked external Optlib or upgraded dependency','--output',str(RUN/'retrieval-v1.json'))
fixed();print('Four complete targets and neutral proposition types frozen and elaborated; source contract review pending, no theorem body authored.')
