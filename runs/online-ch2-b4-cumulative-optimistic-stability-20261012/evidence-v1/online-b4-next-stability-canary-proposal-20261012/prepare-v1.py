from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
ctx='''import BanditRLProof.OnlineCumulativeOptimisticStability

noncomputable section
open Set Finset
namespace BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary
open BanditRL.OnlineConvex

def feasible : Set ℝ := Set.Icc (-1 : ℝ) 1
def regularizer (x : ℝ) : ℝ := x ^ 2 / 2
def hint (_ : ℝ) : ℝ := 0
def losses (_ : ℕ) (x : ℝ) : EReal := (x : EReal)
def predictionObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 0, losses i x + (hint x : EReal)
def currentObjective (x : ℝ) : EReal :=
  (regularizer x : EReal) + ∑ i ∈ range 1, losses i x + extendedIndicator feasible x
def support : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

'''
header='''theorem tight_stability_at_nonminimizer :
    (currentObjective 0).toReal - (currentObjective (-1)).toReal ≤
      support ((0 : ℝ) - (-1)) - (1 / 2 : ℝ) * ‖(0 : ℝ) - (-1)‖ ^ 2 ∧
    IsMinOn predictionObjective feasible 0 ∧
    ¬ IsMinOn currentObjective feasible 0 ∧
    (∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z) ∧
    support ≠ 0 ∧
    (0 : ℝ) ∈ feasible ∧ (-1 : ℝ) ∈ feasible ∧ (2 : ℝ) ∉ feasible ∧
    currentObjective 0 = (0 : EReal) ∧
    currentObjective (-1) = ((-(1 / 2 : ℝ) : ℝ) : EReal) ∧
    currentObjective 2 = ⊤ ∧
    (currentObjective 0).toReal - (currentObjective (-1)).toReal = (1 / 2 : ℝ) ∧
    support ((0 : ℝ) - (-1)) - (1 / 2 : ℝ) * ‖(0 : ℝ) - (-1)‖ ^ 2 = (1 / 2 : ℝ)
'''
suffix='\nend BanditRL.Tests.OnlineCumulativeOptimisticStabilityCanary\n'
def put(n,b):
 if isinstance(b,str):b=b.encode()
 with (P/n).open('xb') as f:f.write(b)
put('canonical-context-v1.txt',ctx);put('theorem-header-v1.txt',header);put('canonical-context-and-statement-v1.txt',ctx+header+suffix)
put('scratch-context-and-statement-v1.txt',(ctx+header+suffix).replace('import BanditRLProof.OnlineCumulativeOptimisticStability','import CumulativeOptimisticStabilityCandidate',1))
contract=dict(status='NEUTRAL_STATEMENT_PROPOSAL_ONLY_UNFROZEN_NO_CANARY_BODY',source_scope='Bounded finite-branch per-round optimistic stability consumer; no full7.47 or terminal claim.',parameters='Closed scalar instance, n0,lambda1,V[-1,1],psi=x²/2,hint0,loss0=x,p0,q-1,g=id.',binder_ledger={'context':'Concrete definitions only, original scalar norm, ordinary EReal sums and indicator. All losses real globally; V bounds membership only.','public_premises':'None. Actual component no-bottom/domain, total curvature, prediction minimizer and local difference support must all be proved internally.','quantified_output':'Only local support tests z in V; no local-to-global inference is made.'},required_first_provider='Direct cumulative_optimistic_stability feasible hV regularizer hint losses 0 1 internally_proved_hbot hdom hlam hstrong 0 hp internally_proved_hprediction support internally_proved_hdifference (-1) hq. First conjunct must genuinely use this theorem at exact operands.',discriminating='Prediction p0 minimizes only psi, while G(-1)=-1/2<G0=0. Nonzero support gives tight performance difference1/2. A proof replacing prediction minimization with IsMinOn G cannot satisfy this instance. Indicator top outsideV is tested at2.',not_covered=['lambda0/empty prefix beyond this n0 instance','non-Euclidean norm','local support that fails globally','attainment producer or terminal ghost correction'],minimality='One closed consumer combines nonminG, nonzero support, tight value and top-outside discrimination. Separate local-vs-global canary deferred; no extra helper or wrapper proposed.',forbidden=['Canary BODY or Lean before independent review/freeze/resource release','Supplied returned-G curvature/support/performance assumptions','Changing p to G minimizer or claiming global support from local predicate'])
put('contract-proposal-v1.json',json.dumps(contract,ensure_ascii=False,indent=2)+'\n')
rows=[dict(path=p.name,bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(P.iterdir()) if p.is_file()]
put('manifest-v1.json',json.dumps(dict(status='PROPOSAL_ONLY',artifacts=rows),indent=2)+'\n')
print(json.dumps(next(x for x in rows if x['path']=='canonical-context-and-statement-v1.txt')))
