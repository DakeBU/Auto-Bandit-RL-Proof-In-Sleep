"""Require the distinct contract verdict before any new diagnostic proof body."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
r=load(run/'source-contract-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[]))
report=Path(r['report']);report=report if report.exists() else run/report
assert sha(report)==r['report_sha256']
reviewed={p['path']:p['sha256'] for p in r['reviewed_files']}
for row in load(run/'contract-source-inputs-v3.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
for p,h in reviewed.items():assert sha(p)==h,p
assert {n.rsplit('.',1)[-1] for n in r['target_verdicts']}==set(freeze['headers'])
for group in ['module','whole_old_canary','fixed_shared_files']:
 for p,h in freeze[group].items():assert sha(p)==h,p
assert sha('Tests.lean')==freeze['Tests_root_raw_prefix']
write('contract-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],verdict=r['verdict'],required_reader_corrections=r.get('required_reader_corrections',[]),retained_proofs=11,retained_definitions=1,new_production_proofs=0,new_canary_proofs=3,source_body_accepted=False,source_terminal_accepted=False))
for event in ['stabilized','proving']:
 gate(event+'-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=freeze['headers'],source_contract_receipt=str(run/'source-contract-receipt-v1.json'),route='single lower retained full equivalence/gradient body revalidation plus diagnostic boundary canaries',first_ready_leaf='singleton_toReal_differentiable',terminal='T2.22 fulliff and everylocalrepresentative gradient identity',allowed_edits='ALL11originalproofs/definition frozen; only new3frozen diagnostic testbodies; comment/selectedreader after BODY',retained_proofs=11,new_production_proofs=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False)))
ob=load(run/'proof-obligations-v1.json');ob['stage']='proving'
for row in ob['required']:row['state']='source-stabilized-retained-body-revalidation-pending'
write('proof-obligations-proving-v1.json',ob)
write('30_lower_worker-body-audit-v1.md','Actual original11proofs1definition retained. Reverse singleton→nonzero normal contradiction at originaldomain boundary→ambientinterior/noBottom/proper→actual nearby-support localbounds/compactness/nontrivialfilterlimit→actual support selection convergence→two global inequalities/normbound/littleO→Frechet gradient→true localfinitegerm. Forward true localfinitegerm/convex→finite-neighborhood affinecontact→globalnoBottom/interior→accepted2.7globalgradient inequality; local minimum derivativezero/Rieszinjectivity uniqueness; eventualrepresentative gradient equality. Full iff uses both directions, no extra supplied proper/interior/closedness. Everyrealrepresentative exactgradient identity remains separatepublicterminal. DefinitionactualnoFD vs11proofsFD, zero dimension permitted; no algorithm/measurable selection. Test-only singleton diagnostic proves toRealzero smooth, genuinegerm impossible and everyglobalsupport. Newproductionmathgain0/one numberedsourceanchor; nextT2.23 remainsmandatory; Goalactive.')
newcanary='''import BanditRLProof
namespace Tests.OnlineDifferentiabilityBoundary
open BanditRL.OnlineConvex Set Filter
open scoped Topology

theorem singleton_toReal_differentiable :
    DifferentiableAt ℝ (fun y : ℝ => (extendedIndicator ({1} : Set ℝ) y).toReal) 1 := by
  have hzero : (fun y : ℝ => (extendedIndicator ({1} : Set ℝ) y).toReal) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ ({1} : Set ℝ)
    · simp [extendedIndicator, hy]
    · simp [extendedIndicator, hy]
  rw [hzero]
  exact differentiableAt_const 0

theorem singleton_not_sourceDifferentiable :
    ¬ SourceDifferentiableAt (extendedIndicator ({1} : Set ℝ)) 1 := by
  intro hd
  have hi := (sourceDifferentiableAt_regular _ _ hd).2.1
  rw [effectiveDomain_indicator, interior_singleton] at hi
  exact not_mem_empty 1 hi

theorem singleton_global_supports (g : ℝ) :
    g ∈ SourceSubdifferential (extendedIndicator ({1} : Set ℝ)) 1 := by
  intro y
  have hx : (1 : ℝ) ∈ ({1} : Set ℝ) := mem_singleton 1
  by_cases hy : y ∈ ({1} : Set ℝ)
  · have hey : y = 1 := mem_singleton_iff.mp hy
    subst y
    simp [extendedIndicator]
  · simp only [extendedIndicator, if_pos hx, if_neg hy]
    exact le_top

end Tests.OnlineDifferentiabilityBoundary
'''
scratch=run/'leaves/new-boundary-canary-v1.lean';write('leaves/new-boundary-canary-v1.lean',newcanary)
headers=load('docs/contracts/online-subgradient-differentiability-migration-v1/new-canary-terminals-v1.json')['headers']
for n,row in headers.items():assert lean_declaration_header(scratch,n)==row['statement'],n
write('canary-worker-before-use-v1.json',dict(path=scratch.as_posix(),sha256=sha(scratch),headers_unchanged_before_first_compile=True,new_production_proofs=0,source_body_accepted=False))
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(set(names))==17
write('leaves/retained-public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientDifferentiabilityCanary\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write('proving-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [scratch,run/'leaves/retained-public-axioms-v1.lean']],before_first_use=True))
print('Distinct contract actually bound; threefrozen diagnostic scratchbodies and17retained kernel axes ready, no proof yet accepted.')
