"""Freeze genuine canary terminals before integrating actual two new public proofs."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-subgradient-interior-migration-v1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'relative-vector-producer-v1-01-exit.json')['exit_code']==0
for group in ['retained_module','fixed_shared_modules','fixed_old_canary']:
 for p,h in load(run/'draft-freeze-v1.json')[group].items():assert sha(p)==h,p
headers=[('ray_relative_contact','''theorem ray_relative_contact :
    ∃ x ∈ intrinsicInterior ℝ (effectiveDomain Tests.OnlineConvexMinorant.loss),
      ∃ (a : (ℝ × ℝ) →L[ℝ] ℝ) (b : ℝ),
        ((a x + b : ℝ) : EReal) = Tests.OnlineConvexMinorant.loss x ∧
        ∀ y, ((a y + b : ℝ) : EReal) ≤ Tests.OnlineConvexMinorant.loss y'''),('singleton_relative_support','''theorem singleton_relative_support :
    (SourceSubdifferential (extendedIndicator ({1} : Set ℝ)) 1).Nonempty'''),('singleton_boundary','''theorem singleton_boundary :
    extendedIndicator ({1} : Set ℝ) 1 = 0 ∧
    extendedIndicator ({1} : Set ℝ) 0 = ⊤ ∧
    interior (effectiveDomain (extendedIndicator ({1} : Set ℝ))) = ∅''')]
prefix='import BanditRLProof\nimport Tests.OnlineConvexMinorantCanary\n\nnoncomputable section\nopen Set BanditRL.OnlineConvex\nopen scoped Topology\nnamespace Tests.OnlineRelativeSubgradient\n\n'
preview=prefix+'\n\n'.join(h+' := by\n' for n,h in headers)+'\nend Tests.OnlineRelativeSubgradient\n'
pp=contract/'planned-canary-headers-only-v1.lean.txt';write(pp,preview)
rows={}
for n,h in headers:
 actual=lean_declaration_header(pp,n);assert actual==h
 fp=run/'native-canary-draft-fences'/(n+'.json')
 gate('canary-draft-fence-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','Tests.OnlineRelativeSubgradient.'+n,'--file',str(pp),'--output',str(fp))
 rows[n]=dict(statement=h,statement_hash=hashlib.sha256(h.encode()).hexdigest(),fence_sha256=sha(fp),preview_not_compiled=True)
write(contract/'canary-headers-v1.json',rows)
write(run/'canary-terminal-freeze-before-bodies-v1.json',dict(stage='proving',headers={n:x['statement_hash'] for n,x in rows.items()},preview_sha256=sha(pp),preview_not_compiled=True,new_canary_proofs=3,new_canary_definitions=0,old_canary_fixed=True,canary_compiled=False))
new_bodies=[ ''' := by
  have hne : (effectiveDomain Tests.OnlineConvexMinorant.loss).Nonempty := by
    rw [Tests.OnlineConvexMinorant.loss_domain]
    exact ⟨(1, 0), by norm_num [Tests.OnlineConvexBarycenter.ray]⟩
  obtain ⟨x, hx⟩ := hne.intrinsicInterior
    (convex_effectiveDomain _ Tests.OnlineConvexMinorant.loss_convex)
  obtain ⟨a, b, htouch, hminor⟩ := affine_support_of_relative_domain_interior
    Tests.OnlineConvexMinorant.loss Tests.OnlineConvexMinorant.loss_noBot
    Tests.OnlineConvexMinorant.loss_convex x hx
  exact ⟨x, hx, a, b, htouch, hminor⟩
''', ''' := by
  apply subgradient_exists_of_relative_domain_interior
  · exact (sourceProper_indicator_iff _).mpr ⟨1, by simp⟩
  · exact (convex_indicator_iff _).mpr (convex_singleton (1 : ℝ))
  · rw [effectiveDomain_indicator, intrinsicInterior_singleton]
    simp
''', ''' := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [extendedIndicator]
  · norm_num [extendedIndicator]
  · rw [effectiveDomain_indicator, interior_singleton]
''']
canary=prefix+'\n\n'.join(h+b for (n,h),b in zip(headers,new_bodies))+'\nend Tests.OnlineRelativeSubgradient\n'
cp=Path('Tests/OnlineRelativeSubgradientCanary.lean');write(cp,canary)
original=(run/'original-OnlineSubgradientInterior.lean.txt').read_bytes();p=Path('BanditRLProof/OnlineSubgradientInterior.lean');assert p.read_bytes()==original
scratch=(run/'leaves/relative-vector-producer-v1.lean').read_text(encoding='utf-8');body=scratch.split('namespace BanditRL.OnlineConvex\n\n',1)[1].split('\n#print axioms',1)[0]
p.write_bytes(original+b'\n\nnamespace BanditRL.OnlineConvex\n\n'+body.encode('utf-8')+b'\nend BanditRL.OnlineConvex\n')
for n,row in load(contract/'headers.json').items():assert lean_declaration_header(p,n)==row['statement'],n
tr=Path('Tests.lean');assert tr.read_bytes()==(run/'original-Tests.lean.txt').read_bytes();tr.write_bytes(tr.read_bytes()+b'\nimport Tests.OnlineRelativeSubgradientCanary\n')
for n,row in rows.items():assert lean_declaration_header(cp,n)==row['statement'],n
names=['BanditRL.OnlineConvex.'+n for n in load(contract/'headers.json')]+['BanditRL.OnlineConvex.affine_support_of_domain_interior','InteriorSupportProbe.interval_center_support']+['Tests.OnlineRelativeSubgradient.'+n for n,h in headers]
assert len(names)==len(set(names))==8
write(run/'public-named-declarations-v1.json',dict(package_proofs=3,retained_package_proofs=1,new_package_proofs=2,shared_dependency_proofs=1,old_canary_proofs=1,new_canary_proofs=3,new_definitions=0,axiom_probe=names,named_axiom_count=8))
write(run/'leaves/public-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientInteriorCanary\nimport Tests.OnlineRelativeSubgradientCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
write(run/'public-integration-before-build-v1.json',dict(status='actual canonical two new proof bodies integrated, gates pending',module_sha256=sha(p),new_canary_sha256=sha(cp),Tests_sha256=sha(tr),original_module_bytes_contiguous=original in p.read_bytes(),headers=load(run/'draft-freeze-v1.json')['headers'],new_proofs_compiled_public=False,source_package_accepted=False,chapter_complete=False,goal_complete=False,generated_before_use=[dict(path=str(run/'leaves/public-axioms-v1.lean'),sha256=sha(run/'leaves/public-axioms-v1.lean'))]))
print('Three canary headers actually frozen before bodies; two exact canonical proofs/3 genuine canary bodies integrated; public gates pending.')
