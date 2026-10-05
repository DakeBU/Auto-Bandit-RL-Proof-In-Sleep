"""Prepare actual API probes and a bounded comparative target before source review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-guessing-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='25c77a837c849eb78832673063483db5f663a73a'
runner=run/'run-command.py';assert not runner.exists()
runner.write_bytes(Path('runs/online-jensen-migration-20261005/run-command.py').read_bytes())
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
reader=PdfReader(source)
write(run/'source-printed15-pdf27.txt',reader.pages[26].extract_text())
write(run/'source-chapter1-pdf13-19.txt','\n\n'.join('PHYSICAL PAGE '+str(i+1)+'\n'+reader.pages[i].extract_text() for i in range(12,19)))
modules=['BanditRLProof/OnlineGuessingOGD.lean','BanditRLProof/OnlineGuessingLower.lean']
canaries=['Tests/OnlineGuessingOGDCanary.lean','Tests/OnlineGuessingLowerCanary.lean']
headers={};oldnames=[]
for p in modules:
 text=Path(p).read_text(encoding='utf-8')
 for name in re.findall(r'(?m)^theorem\s+(\S+)',text):
  h=lean_declaration_header(Path(p),name);headers[name]=dict(file=p,statement=h,statement_hash=hashlib.sha256(h.encode()).hexdigest(),state='retained-public-body-not-currently-source-accepted')
  oldnames.append('BanditRL.OnlineGradientDescent.'+name)
 for p0 in [p]:(run/('original-'+Path(p0).name+'.txt')).write_bytes(Path(p0).read_bytes())
assert len(headers)==9
for p in canaries:(run/('original-'+Path(p).name+'.txt')).write_bytes(Path(p).read_bytes())
new=[
'''theorem meanPredict_zero_cumulativeLoss (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ range T,
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) = 1/4 := by''',
'''theorem guessing_vs_mean_lower (n : ℕ) (hn : 0 < n) :
    (n : ℝ)/4 - 1/4 ≤
      regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by''',
'''theorem guessing_vs_mean_unbounded (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      C < regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by''']
write(run/'planned-comparison-headers-v1.json',dict(status='planned-exact-terminals-no-body-or-compilation-claim',headers=new,public_module='BanditRLProof/OnlineGuessingComparison.lean',new_proofs=3,new_definitions=0))
write(run/'retained-headers-v1.json',headers)
context='import BanditRLProof\nimport Mathlib.Algebra.Order.Archimedean.Basic\n\nopen Set Finset BanditRL.OnlineGradientDescent\n'
probe=context+'\n'.join('#check @'+n for n in oldnames)+'\n'
for n in ['BanditRL.OnlineGradientDescent.unitInterval','BanditRL.OnlineGradientDescent.iterate_prefix','BanditRL.OnlineGradientDescent.equation_2_1','BanditRL.OnlineLearning.meanPredict','BanditRL.OnlineLearning.meanPredict_prefix','BanditRL.OnlineLearning.theorem_1_3','BanditRL.OnlineLearning.empiricalMean','exists_nat_gt','Finset.sum_ite_eq','Finset.sum_ite_eq\'','Finset.mem_range']:
 probe+='#check @'+n+'\n'
probe+='''
#check (∀ T : ℕ, 0 < T →
  (∑ t ∈ range T, (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) = (1/4 : ℝ))
#check (∀ n : ℕ, 0 < n → (n : ℝ)/4 - 1/4 ≤
  regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
    (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
  (∑ t ∈ range ((2*n)^2), (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2))
#check (∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N < n ∧
  C < regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
    (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
  (∑ t ∈ range ((2*n)^2), (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2))
'''
write(run/'leaves/actual-types-v1.lean',probe)
write(run/'00_context.md','''Persistent real Orabona Chapters1–16 Goal ACTIVE/unbudgeted. Current Example2.14 bounded package is based on exact OPEN draft PR163 final25c77a837c849eb78832673063483db5f663a73a, not main. Canonical origin/main freshly fetched6847b678a73db68dee5101d6f05c2453c1405afc, canonical clean; shared Git E:/ABRL/research/.git, existing research-online-book checkout reused on codex/research-online-guessing-migration. Other worktrees preserved (extended-topics now6193afc..., independently changing). No merge/deploy/retirement, generated_site/private/anonymous/stores/junctions untouched. GPT-6 Astra/medium requested for all roles; model/runtime attestation not claimed.

Source v10 exact cached SHA freshly verified, printed15/PDF27 plus read-only Chapter1 source dependency. Nine retained proofs/one interval-domain definition, two whole retained canaries/five proofs/two definitions. Proposed NEW bounded terminal is actual unbounded cumulative-loss gap between this horizon-tuned OGD (initial1) and the actual strict-prefix mean predictor (initial1/2), on the SAME all-zero label sequence and arbitrarily large square horizons. Three explicit planned proof targets, no new algorithm or definitions. This derived strengthening supports source suboptimality prose; no attribution of a printed numerical comparison theorem, every-initial-value claim, all-algorithm lower bound, Chapter4 optimality or chapter/book completion. Current new targets have no theorem body and no named-public compilation claim; actual type expressions are separately checked before contract freeze/review.

Required repo read order/skills/source/route inspected. Three distinct automated roles required by .agents/skills/bandit-semantic-roundtrip/SKILL.md; existing actors reused with restricted current packets, history not erased. Pipeline command gates and prompt/file conventions distinguished. Global reference-index rewrite not run because it mutates unrelated indices outside this bounded scope; actual read-only retrieval and compiled API/type probes used. Earlier read-only guessed paths statement-fingerprints.json and a separate lower run directory were absent; rg found headers.json and the actual combined online-guessing-ogd-20260914 run. These are retrieval errors, not Lean failures or target repairs.

Legacy13 before current package, Chapter2 mandatory total null/incomplete, Chapter1 source migration remains distinct, Chapters3–16 unenumerated mandatory. Source review, new proof work, combined root/Tests/full harness/axiom/site and PR delivery pending. Do not accept this package or advance Chapter3 from a plan.''')
write(run/'bootstrap-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [runner,run/'leaves/actual-types-v1.lean',run/'planned-comparison-headers-v1.json']],stage='before-first-child-use'))
print('Actual API/three planned type expressions prepared; nine retained headers and source cached bytes preserved.')
