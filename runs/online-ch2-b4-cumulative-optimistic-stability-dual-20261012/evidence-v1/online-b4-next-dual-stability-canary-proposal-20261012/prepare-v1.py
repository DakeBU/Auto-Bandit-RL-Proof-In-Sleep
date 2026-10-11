from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parent.parent
def put(name,text):
    with (P/name).open('x',encoding='utf-8',newline='\n') as f:f.write(text)
def bind(p):return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
context='''import BanditRLProof.OnlineCumulativeOptimisticStabilityDual

noncomputable section
open Set Finset
namespace BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary
open BanditRL.OnlineConvex

namespace Tight
def feasible : Set ℝ := Set.Icc (-2 : ℝ) 2
def regularizer (x : ℝ) : ℝ := x ^ 2 / 2
def hint (_ : ℝ) : ℝ := 0
def losses (_ : ℕ) (x : ℝ) : EReal := ((2 * x : ℝ) : EReal)
def predictionObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 0, losses i x + (hint x : EReal)
def currentObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 1, losses i x + extendedIndicator feasible x
def support : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
end Tight

namespace ZeroCurvature
def feasible : Set ℝ := Set.Icc (-1 : ℝ) 1
def regularizer (_ : ℝ) : ℝ := 0
def hint (_ : ℝ) : ℝ := 0
def losses (_ : ℕ) (x : ℝ) : EReal := (x : EReal)
def predictionObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 0, losses i x + (hint x : EReal)
def currentObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 1, losses i x + extendedIndicator feasible x
def support : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
end ZeroCurvature

'''
tight='''namespace Tight
theorem tight_dual_stability_at_nonminimizer :
    (currentObjective 0).toReal - (currentObjective (-2)).toReal ≤
      ‖support‖ ^ 2 / (2 * (1 : ℝ)) ∧
    IsMinOn predictionObjective feasible 0 ∧
    ¬ IsMinOn currentObjective feasible 0 ∧
    (∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z) ∧
    support ≠ 0 ∧ ‖support‖ = (2 : ℝ) ∧
    (0 : ℝ) ∈ feasible ∧ (-2 : ℝ) ∈ feasible ∧ (3 : ℝ) ∉ feasible ∧
    currentObjective 0 = (0 : EReal) ∧
    currentObjective (-2) = ((-2 : ℝ) : EReal) ∧
    currentObjective 3 = ⊤ ∧
    (currentObjective 0).toReal - (currentObjective (-2)).toReal = (2 : ℝ) ∧
    ‖support‖ ^ 2 / (2 * (1 : ℝ)) = (2 : ℝ)
end Tight

'''
zero='''namespace ZeroCurvature
theorem zero_curvature_division_is_false :
    Convex ℝ feasible ∧
    (∀ i < (0 : ℕ) + 1, ∀ x, losses i x ≠ ⊥) ∧
    (∀ i < (0 : ℕ) + 1, feasible ⊆ effectiveDomain (losses i)) ∧
    (∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      currentObjective (a • x + (1 - a) • y) ≤
        (a : EReal) * currentObjective x + ((1 - a : ℝ) : EReal) * currentObjective y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ∧
    IsMinOn predictionObjective feasible 0 ∧
    (∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z) ∧
    (0 : ℝ) ∈ feasible ∧ (-1 : ℝ) ∈ feasible ∧
    ‖support‖ = (1 : ℝ) ∧
    currentObjective 0 = (0 : EReal) ∧
    currentObjective (-1) = ((-1 : ℝ) : EReal) ∧
    (currentObjective 0).toReal - (currentObjective (-1)).toReal = (1 : ℝ) ∧
    ‖support‖ ^ 2 / (2 * (0 : ℝ)) = (0 : ℝ) ∧
    ¬ ((currentObjective 0).toReal - (currentObjective (-1)).toReal ≤
      ‖support‖ ^ 2 / (2 * (0 : ℝ)))
end ZeroCurvature

'''
end='end BanditRL.Tests.OnlineCumulativeOptimisticStabilityDualCanary\n'
for name,text in [('canonical-context-v1.txt',context),('tight-header-v1.txt',tight),('zero-header-v1.txt',zero),('canonical-context-and-statements-v1.txt',context+tight+zero+end),('scratch-context-and-statements-v1.txt',(context+tight+zero+end).replace('import BanditRLProof.OnlineCumulativeOptimisticStabilityDual','import CumulativeOptimisticStabilityDualCandidate',1))]:put(name,text)
contract={'status':'PROPOSAL_ONLY_PENDING_BLIND_SOURCE_REVIEW_AND_PARENT_FREEZE','proof_body_authorized':False,'Lean_executed':False,'canonical_import':'BanditRLProof.OnlineCumulativeOptimisticStabilityDual is a future dependency, not claimed installed','scratch_transport':'Proposed sole import substitution to actual accepted CumulativeOptimisticStabilityDualCandidate; no binary copying/relabeling','source_pdf':{'path':'E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf','sha256':'cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'},'anchors':['Lemma7.5 printed101-102/PDF113-114 numerical dual-norm inequality','Theorem7.47 printed130/PDF142 Young/operator-norm step'],'source_body_verdict':bind(R/'tmp/online-b4-next-dual-stability-source-review-20261012/body-source-verdict-v1.json'),'tight':{'binders':[],'E':'Real with its usual norm','V':'[-2,2]','psi':'x^2/2','hint':'0','loss_i':'2*x, real-coerced EReal everywhere for every i','n':0,'lambda':1,'p':0,'q':-2,'g':'2 times continuous identity','required_genuine_provider':'First conjunction must be obtained by cumulative_optimistic_stability_dual_bound on these exact operands, not arithmetic alone or an assumed output inequality.','internal_premises':['Convex interval','Global no-bottom for i<1','V subset effectiveDomain of each included loss; derive both separately, never infer no-bottom from below-top','Strict positivity 0<1','Actual extended cumulative G interpolation at lambda1 in original Real norm','Prediction objective minimum on V at0','Local support of loss0-hint by actual g for every feasible z','Actual p,q membership'],'discrimination':['G0=0, G(-2)=-2, actual gap2 and operator norm squared/(2lambda)=2','p minimizes prediction objective but does not minimize current G','Operator norm support=2 is independently established; no supplied norm/performance premise','Out-of-domain G3=top checks indicator remains in actual G','Wrong smaller coefficient or omission of squaring can fail; a looser upper bound can still pass, so this example does not reject every constant error','Scalar Real fixture does not discriminate arbitrary coordinates or non-Euclidean norms']},'zero':{'binders':[],'V':'[-1,1]','psi_hint':'0','loss_i':'x, real-coerced EReal everywhere','n':0,'lambda':0,'p':0,'q':-1,'g':'continuous identity','statement_role':'Explicit counterexample to removing strict positivity from the divided conclusion; not an invocation of the positive-lambda theorem.','other_premises':'Convexity, global no-bottom, feasible below-top domain, zero-curvature interpolation, actual prediction minimum, local difference support and p/q membership are explicit conjunctions and must all be proved internally.','arithmetic':'G0=0; G(-1)=-1; signed gap1; operator norm1; Lean real division by0 gives0; hence1<=0 is false.','boundary':'lambda0 remains allowed in the sharp parent; this does not invalidate or modify that theorem.'},'audit_requirements':['Exact first-conjunction provider on all actual n0/lambda1/p0/q-2/function/set operands, with every premise internal','Imported actual TYPE/VALUE, standard axioms and truthful canonical/scratch module origins if later authorized','No target call in zero branch under invalid lambda0; verify all other premises and false conclusion numerals','Preserve header/context bytes after reviewed freeze; no public performance hypotheses or dummy wrappers'],'open_boundaries':['No trajectory, attainment, source-global support existence, fullLemma7.5/full7.47/full15.31 or terminal ghost cancellation','General total-objective curvature premise remains; examples do not replace it with a universal regularizer-only assumption','Global no-bottom and below-top domain are distinct; bottom satisfies below-top but fails no-bottom','Seven open-forward and six future claims unchanged; mandatory denominator null; all hard targets retained','Canonical/sharedroot/Tests/fullharness/site/reader acceptance separate and pending'],'C2_open_forward':7,'C2_future_claims':6,'C2_mandatory_denominator':None,'chapter_accepted':False,'global_goal_complete':False}
put('source-contract-proposal-v1.json',json.dumps(contract,indent=2)+'\n')
ledger={'public_binders':[],'closed_statements':2,'tight_conjunctions':14,'zero_conjunctions':14,'performance_premise_binders':0,'helper_theorems':0,'internal_goal':'All hypotheses of the actual positive-lambda provider supplied from closed fixture definitions; zero case states all remaining hypotheses explicitly','neutral_files':['canonical-context-v1.txt','tight-header-v1.txt','zero-header-v1.txt','canonical-context-and-statements-v1.txt']}
put('binder-ledger-v1.json',json.dumps(ledger,indent=2)+'\n')
manifest={'status':'PROPOSAL_ONLY_NOT_FROZEN_NOT_ELABORATED','files':[bind(p) for p in sorted(P.iterdir()) if p.is_file()],'no_BODY_or_Lean':True}
put('manifest-v1.json',json.dumps(manifest,indent=2)+'\n')
print(json.dumps(bind(P/'manifest-v1.json')))
