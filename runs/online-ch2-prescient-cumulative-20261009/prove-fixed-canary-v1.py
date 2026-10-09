from common import *
fixed()
st=load(CONTRACT/'canary-stabilized-v1.json'); t=st['targets'][0]
assert load(RUN/'variable-printed-focused-inspected-v1.json')['compiled']
assert sha(PUBLIC)==load(RUN/'variable-printed-focused-inspected-v1.json')['module_sha256']
test=ROOT/t['file']; assert not test.exists()
write(RUN/'pre-fixed-canary-native-exact-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md'] if p.exists()]))
event('native-fixed-canary-proving-v1','proving',dict(leaf=t['declaration'],statement_sha256=t['statement_sha256'],canary_CONTRACT_review_sha256=st['CONTRACT_review_sha256'],whole_Goal_status='ACTIVE'))
body='''  dsimp only
  let V : Set ℝ := Icc (-1) 1
  let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
  let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
  let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 8 : ℝ) : EReal) else ⊤
  let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
  let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1 / 2
  obtain ⟨hf0, hf1, hs0, hs1, hstrict, _, _, _, h0, h1, h2, _, hD10, hD01, _, _⟩ :=
    BanditRL.OnlinePrescientBregmanCanary.two_distinct_current_losses
  have hd (z : ℝ) : HasDerivAt ψ (z ^ 3 + z) z := by
    convert (((hasDerivAt_id z).pow 4).div_const 4).add
      (((hasDerivAt_id z).pow 2).div_const 2) using 1
    dsimp [ψ, id]
    ring
  have hD (a b : ℝ) : divergence ψ a b = ψ a - ψ b - (b ^ 3 + b) * (a - b) := by
    rw [divergence, fderiv_eq_deriv_mul, (hd b).deriv]
  have hdiff : DifferentiableOn ℝ ψ (interior (univ : Set ℝ)) := by
    simp only [interior_univ]
    intro z _
    exact (hd z).differentiableAt.differentiableWithinAt
  have hcont : Continuous ψ := (show Differentiable ℝ ψ from fun z => (hd z).differentiableAt).continuous
  have hclosed : SourceClosed (fun z => ((ψ z : ℝ) : EReal)) := by
    intro r
    change IsClosed {z : ℝ | (ψ z : EReal) ≤ (r : EReal)}
    simpa only [EReal.coe_le_coe_iff] using
      (isClosed_le hcont (continuous_const : Continuous (fun _ : ℝ => r)))
  have hseq : ∀ t ≤ 2, iterate V ψ (fun _ => 1) loss (1 / 2) t = some (x t) := by
    intro t ht
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases ht' with rfl | rfl | rfl
    · simpa [x] using h0
    · simpa [x] using h1
    · simpa [x] using h2
  have hi : ∀ t ≤ 2, x t ∈ interior (univ : Set ℝ) := by simp
  have hf (t : ℕ) (_ : t < 2) : SourceProper (loss t) := by
    by_cases h : t = 0
    · simpa [loss, h] using hf0
    · simpa [loss, h] using hf1
  have hs (t : ℕ) (_ : t < 2) : ∀ z ∈ V, (SourceSubdifferential (loss t) z).Nonempty := by
    by_cases h : t = 0
    · simpa [loss, h] using hs0
    · simpa [loss, h] using hs1
  have hshared : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        (∑ t ∈ range 2, (divergence ψ u (x t) - divergence ψ u (x (t + 1))) / 1) -
        ∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / 1 := by
    intro u hu
    exact iterate_divergence_sum V univ (convex_Icc (-1 : ℝ) 1) ψ hdiff
      (fun _ => 1) loss (1 / 2) x 2 hseq hi (by intros; norm_num) hf hs u hu
  have hsharp : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 - divergence ψ u (x 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1 := by
    intro u hu
    exact iterate_fixed_sharp V univ (convex_Icc (-1 : ℝ) 1) ψ hdiff
      1 (by norm_num) loss (1 / 2) x 2 hseq hi hf hs u hu
  have hprinted : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1 := by
    intro u hu
    exact iterate_fixed_regret V univ (convex_Icc (-1 : ℝ) 1) (fun _ _ => mem_univ _)
      ψ hstrict hdiff 1 (by norm_num) loss (1 / 2) x 2 hseq hi hf hs u hu
  have hterminal : divergence ψ (-1 / 2) (x 2) = 5 / 8 := by
    rw [hD]
    norm_num [ψ, x]
  have hnumSharp : (-9 / 8 : ℝ) ≤ -5 / 16 := by
    convert hsharp (-1 / 2) (by norm_num [V]) using 1 <;>
      norm_num [sum_range_succ, loss, f0, f1, V, x, hD, ψ]
  have hnumPrinted : (-9 / 8 : ℝ) ≤ 5 / 16 := by
    convert hprinted (-1 / 2) (by norm_num [V]) using 1 <;>
      norm_num [sum_range_succ, loss, f0, f1, V, x, hD, ψ]
  refine ⟨hf0, hf1, hs0, hs1, hclosed, hstrict, ?_, hseq, hterminal, ?_, ?_,
    hshared, hsharp, hprinted, hnumSharp, hnumPrinted⟩
  · simpa only [interior_univ] using hdiff
  · simpa [x] using hD10
  · simpa [x] using hD01
'''
write(test,st['context']+'\n'+t['exact_header']+' := by\n'+body+'\nend BanditRL.OnlinePrescientBregmanRegretCanary\n')
write(RUN/'fixed-canary-source-attempt-v1.lean',test.read_bytes())
capture('fixed-canary-statement-fence-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['declaration'],'--file',test.relative_to(ROOT),'--output',CONTRACT/'fixed-canary-fence-v1.json')
code,out=capture('fixed-canary-focused-build-v1','lake','build','Tests.OnlinePrescientBregmanRegretCanary',required=False)
passed=code==0 and 'Built Tests.OnlinePrescientBregmanRegretCanary' in out and 'Build completed successfully' in out
write(RUN/'fixed-canary-focused-inspected-v1.json',dict(actual_exit=code,compiled=passed,new_Test_Built_marker='Built Tests.OnlinePrescientBregmanRegretCanary' in out,canary_sha256=sha(test),production_sha256=sha(PUBLIC),full_conjunctions=1,numeric_VALUE_audit='pending',source_container_closed=False,whole_Goal_status='ACTIVE'))
if passed:
    capture('fixed-canary-safe-verify-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/'fixed-canary-fence-v1.json')
else:
    print(out[-4000:])
    event('native-fixed-canary-repair-v1','repair',dict(leaf=t['declaration'],actual_exit=code,frozen_header_unchanged=True,evidence='fixed-canary-focused-build-v1.json'))
fixed()
assert passed
print('One full actual fixed16conjunct canary focused compiled; numeric VALUE/second canary/full gates pending.')
