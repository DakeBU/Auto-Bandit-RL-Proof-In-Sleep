from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parent.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def bind(p):return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))
def write(name,s):
 with (P/name).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
def put(name,j):write(name,json.dumps(j,indent=2)+'\n')
old=R/'tmp/online-b4-next-stability-freeze-20261012/neutral-frozen-header-v1.txt'
s=old.read_text(encoding='utf-8');s=s[s.index('noncomputable section'):]
s='import BanditRLProof.OnlineCumulativeOptimisticStability\n\n'+s
s=s.replace('theorem cumulative_optimistic_stability','theorem cumulative_optimistic_stability_dual_bound')
s=s.replace('(hlam : 0 ≤ lam)','(hlam : 0 < lam)')
s=s.replace('      g (p - q) - (lam / 2) * ‖p - q‖ ^ 2','      ‖g‖ ^ 2 / (2 * lam)')
write('neutral-header-proposal-v1.txt',s)
put('binder-ledger-v1.json',dict(status='PROPOSAL_ONLY_NOT_ELABORATED_OR_FROZEN',binders=[
 ['E,NormedAddCommGroup,NormedSpace','Arbitrary original real normed space; no coordinate norm or Hilbert structure'],
 ['V,hV','Feasible convex set; p with hp supplies nonemptiness, no closedness/compactness assumption'],
 ['psi,hint','Real ambient functions used only on V'],['loss,n','Ordinary EReal current prefix range(n+1); n=0 allowed'],
 ['lam,hlam','Strict positive curvature for division; changed explicitly from sharp parent nonnegative curvature'],
 ['hbot','Each included loss excludes bottom globally'],['hdom','Each included loss below top on V; independently needed with hbot'],
 ['hstrong','Actual current cumulative G has lambda curvature on V; not only regularizer'],
 ['p,hp,hprediction','Actual prior-prefix-plus-hint feasible minimizer; never assumed current G minimum'],
 ['g,hdifference','Continuous real dual supporting loss_n-hint locally on V; g=0 allowed'],
 ['q,hq','Arbitrary feasible comparison point, no attainment premise']],
 conclusion='Actual G difference bounded by squared operator norm of g divided by 2 lambda',
 hidden_premises=[],preserved_boundaries=['No global support existence','No attainment','No performance sum or ghost cancellation']))
paths=[old,R/'tmp/online-b4-next-stability-body-20261012/candidate-v1.lean',
 R/'tmp/online-b4-next-stability-body-20261012/compiled-core-report-v1.json',
 R/'tmp/online-b4-next-stability-canary-source-review-20261012/body-source-verdict-v1.json',
 R/'docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json',
 R/'BanditRLProof/OnlineCumulativePotential.lean',R/'BanditRLProof/OnlineStrongConvexMinimum.lean',
 R/'.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean',
 Path('E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf')]
paths += [R/('tmp/online-b4-next-stability-planning-20261012/'+n) for n in ['source-pages113-114-v1.txt','source-pages141-142-v1.txt','source-pages278-279-v1.txt','frozen-B4-selected-rows-v1.json']]
put('input-bindings-v1.json',dict(observed_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R).decode().strip(),tracked_status=subprocess.check_output(['git','status','--short'],cwd=R).decode(),note='Observed snapshot only, not an installation base or freeze; parent installation is ongoing.',inputs=[bind(p) for p in paths]))
put('manifest-v1.json',dict(status='DEPENDENCY_READY_MATHEMATICAL_PROPOSAL_ONLY',Lean_processes=0,header_elaborated=False,header_frozen=False,source_accepted=False,files=[bind(p) for p in sorted(P.iterdir()) if p.is_file()]))
print(json.dumps(dict(header=bind(P/'neutral-header-proposal-v1.txt'),manifest=bind(P/'manifest-v1.json'))))
