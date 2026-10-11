from pathlib import Path
import json,hashlib,ast
P=Path(__file__).resolve().parent;R=P.parent.parent
Q=R/'tmp/online-b4-next-dual-stability-canary-proposal-20261012'
F=R/'tmp/online-b4-next-dual-stability-canary-freeze-20261012'
D=R/'tmp/online-b4-next-dual-stability-body-20261012'
def put(n,s):
    with (P/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
def bind(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
frozen=(F/'scratch-frozen-context-and-statements-v1.txt').read_text(encoding='utf-8')
assert hashlib.sha256(frozen.encode()).hexdigest()=='857eb5086f0e224daad0d72d758b73619f8cd717a31d4aeb70bad4ea61f24509'
tight=(Q/'tight-header-v1.txt').read_text(encoding='utf-8');zero=(Q/'zero-header-v1.txt').read_text(encoding='utf-8')
old=(R/'tmp/online-b4-next-stability-canary-body-20261012/candidate-v2.lean').read_text(encoding='utf-8')
body=old.split(' := by\n',1)[1].split('\n\n\nend BanditRL.Tests.',1)[0]
body=body.replace('hm1','hm2').replace('(-1 : ℝ)','(-2 : ℝ)').replace('(-1)','(-2)').replace('convex_Icc (-2 : ℝ) 1','convex_Icc (-2 : ℝ) 2')
body=body.replace('x ^ 2 / 2 + x','x ^ 2 / 2 + 2 * x').replace('EReal.coe_ne_bot x','EReal.coe_ne_bot (2 * x)').replace('EReal.coe_lt_top x','EReal.coe_lt_top (2 * x)')
body=body.replace('cumulative_optimistic_stability feasible (convex_Icc _ _)','cumulative_optimistic_stability_dual_bound feasible hV')
body=body.replace('hbot hdom (by norm_num) hstrong','hbot hdom hlam hstrong')
body=body.replace('  have bound :=','  have hV : Convex ℝ feasible := convex_Icc _ _\n  have hlam : 0 < (1 : ℝ) := by norm_num\n  have bound :=')
body=body.replace('((-(1 / 2 : ℝ) : ℝ) : EReal)','((-2 : ℝ) : EReal)')
body=body[:body.index('  refine ⟨bound,')]+'''  have hnorm : ‖support‖ = (2 : ℝ) := by
    norm_num [support, norm_smul, ContinuousLinearMap.norm_id]
  refine ⟨bound, hprediction, ?_, hdifference, ?_, hnorm, h0, hm2, ?_, hzero, hminus, ?_, ?_, ?_⟩
  · intro hm
    have h := hm hm2
    change currentObjective 0 ≤ currentObjective (-2) at h
    rw [hzero, hminus] at h
    norm_num at h
  · intro h
    have hh := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) h
    norm_num [support] at hh
  · norm_num [feasible]
  · norm_num [currentObjective, regularizer, losses, extendedIndicator, feasible]
  · rw [hzero, hminus]
    norm_num
  · rw [hnorm]
    norm_num
'''
zeroBody='''  have h0 : (0 : ℝ) ∈ feasible := by norm_num [feasible]
  have hm1 : (-1 : ℝ) ∈ feasible := by norm_num [feasible]
  have hvalue (x : ℝ) (hx : x ∈ feasible) : currentObjective x = (x : EReal) := by
    simp [currentObjective, regularizer, losses, extendedIndicator, hx]
  have hprediction : IsMinOn predictionObjective feasible 0 := by
    intro z hz
    simp [predictionObjective, regularizer, hint]
  have hdifference : ∀ z ∈ feasible,
      (losses 0 0).toReal - hint 0 + support (z - 0) ≤
        (losses 0 z).toReal - hint z := by
    intro z hz
    simp [losses, hint, support]
  have hbot : ∀ i < (0 : ℕ) + 1, ∀ x, losses i x ≠ ⊥ := by
    intro i hi x
    exact EReal.coe_ne_bot x
  have hdom : ∀ i < (0 : ℕ) + 1, feasible ⊆ effectiveDomain (losses i) := by
    intro i hi x hx
    exact EReal.coe_lt_top x
  have hstrong : ∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      currentObjective (a • x + (1 - a) • y) ≤
        (a : EReal) * currentObjective x + ((1 - a : ℝ) : EReal) * currentObjective y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz := (convex_Icc (-1 : ℝ) 1) hx hy (le_of_lt ha)
      (by linarith : 0 ≤ 1 - a) (by ring : a + (1 - a) = 1)
    rw [hvalue _ hz, hvalue x hx, hvalue y hy]
    simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff,
      smul_eq_mul]
    ring_nf
  have hzero := hvalue 0 h0
  have hminus := hvalue (-1) hm1
  have hnorm : ‖support‖ = (1 : ℝ) := by simp [support, ContinuousLinearMap.norm_id]
  refine ⟨convex_Icc _ _, hbot, hdom, hstrong, hprediction, hdifference,
    h0, hm1, hnorm, hzero, hminus, ?_, ?_, ?_⟩
  · rw [hzero, hminus]
    norm_num
  · norm_num
  · rw [hzero, hminus]
    norm_num
'''
candidate=frozen.replace(tight,tight.replace('\nend Tight',' := by\n'+body+'\nend Tight')).replace(zero,zero.replace('\nend ZeroCurvature',' := by\n'+zeroBody+'\nend ZeroCurvature'))
put('candidate-v1.lean',candidate)
probe=frozen.replace('theorem tight_dual_stability_at_nonminimizer :','#check').replace('theorem zero_curvature_division_is_false :','#check')
put('HeaderElaboration-v1.lean',probe)
# Preserve the previously discovered complete actual scratch-dual import closure.
closure=json.loads((D/'closure-manifest-v1.json').read_text(encoding='utf-8'))
closure['inputs'] += [bind(D/'candidate-v1.lean'),bind(D/'CumulativeOptimisticStabilityDualCandidate.olean')]
closure['origins'] += [dict(module='CumulativeOptimisticStabilityDualCandidate',source=str(D/'candidate-v1.lean'),olean=str(D/'CumulativeOptimisticStabilityDualCandidate.olean'))]
closure['scope']='Previously imported actual dual module closure, sealed again before header/BODY/import. Full RAW equality required; current imported audit must confirm exact closure plus own canary.'
put('closure-manifest-v1.json',json.dumps(closure,indent=2)+'\n')
cap=(D/'capture-v3.py').read_text(encoding='utf-8').replace("pinfile=P/'capture-pins-v3.json'","pinfile=P/'capture-pins-v1.json'")
cap=cap.replace("if a.stage in ['body','import']:","if a.stage in ['header','body','import']:")
cap=cap.replace("assert src.read_bytes().split(b' := by\\n',1)[0]+suffix==frozen", "extracted=re.sub(rb' := by\\n.*?(?=\\nend (?:Tight|ZeroCurvature))',b'',src.read_bytes(),flags=re.S);assert extracted==frozen")
cap=cap.replace("CumulativeOptimisticStabilityDualCandidate.olean","CumulativeOptimisticStabilityDualCanary.olean")
cap=cap.replace("[pins['scratch_parent_root']]","pins['scratch_parent_roots']")
ast.parse(cap);put('capture-v1.py',cap)
pins=json.loads((D/'capture-pins-v3.json').read_text(encoding='utf-8'))
pins['release']=bind(F/'ignored-Lean-resource-release-v1.json');assert pins['release']['sha256']=='921efceaf739514da573bdea4dd84979bcaa4267f0ac0d220f64f0ee91bd86b9'
pins['freeze']=bind(F/'local-header-freeze-v1.json');pins['frozen_header']=bind(F/'scratch-frozen-context-and-statements-v1.txt');pins['canonical_header']=bind(F/'canonical-frozen-context-and-statements-v1.txt');pins['header_probe']=bind(P/'HeaderElaboration-v1.lean');pins['capture']=bind(P/'capture-v1.py');pins['closure_manifest_sha256']=bind(P/'closure-manifest-v1.json')['sha256'];pins['scratch_parent_roots']=[str(D),pins.pop('scratch_parent_root')]
pins['parents'] += [bind(D/'candidate-v1.lean'),bind(D/'CumulativeOptimisticStabilityDualCandidate.olean')]
pins['project']=[bind(R/n) for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','BanditRLProof.lean','Tests.lean']]
put('capture-pins-v1.json',json.dumps(pins,indent=2)+'\n')
print(json.dumps(dict(pins=bind(P/'capture-pins-v1.json'),candidate=bind(P/'candidate-v1.lean'))))
