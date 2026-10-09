from common import *
fixed()
st=load(CONTRACT/'canary-stabilized-v1.json'); t=st['targets'][1]; test=ROOT/t['file']
assert load(RUN/'fixed-canary-focused-inspected-v2.json')['compiled']
assert sha(test)==load(RUN/'fixed-canary-focused-inspected-v2.json')['canary_sha256']
assert sha(PUBLIC)==load(RUN/'all-five-public-inspected-v1.json')['module_sha256']
old=test.read_bytes(); write(RUN/'pre-decreasing-canary-public-v1.lean',old)
write(RUN/'pre-decreasing-canary-native-exact-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md'] if p.exists()]))
event('native-decreasing-canary-proving-v1','proving',dict(leaf=t['declaration'],statement_sha256=t['statement_sha256'],canary_CONTRACT_review_sha256=st['CONTRACT_review_sha256'],whole_Goal_status='ACTIVE'))
body='''  dsimp only
  let V : Set ℝ := Icc (-1) 1
  let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
  let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
  let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 4 : ℝ) : EReal) else ⊤
  let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
  let η : ℕ → ℝ := fun t => if t = 0 then 1 else 1 / 2
  let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1 / 2
  obtain ⟨hf0, _, hs0, _, hclosed, hstrict, hdiffAll, hseqOld, _, _, _, _, _, _, _, _⟩ :=
    fixed_signed_run
  have hzero : (0 : ℝ) ∈ V := by norm_num [V]
  have hhalf : (1 / 2 : ℝ) ∈ V := by norm_num [V]
  have hf1 : SourceProper f1 := by
    refine ⟨?_, 0, 0, ?_⟩
    · intro z
      by_cases hz : z ∈ V <;> simp [f1, hz]
    · simp [f1, hzero]
  have hs1 : ∀ z ∈ V, (SourceSubdifferential f1 z).Nonempty := by
    intro z hz
    refine ⟨-5 / 4, ?_⟩
    intro y
    change f1 z + (inner ℝ (-5 / 4 : ℝ) (y - z) : EReal) ≤ f1 y
    by_cases hy : y ∈ V
    · simp only [f1, if_pos hz, if_pos hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      change -5 * z / 4 + (y - z) * (-5 / 4) ≤ -5 * y / 4
      linarith
    · simp only [f1, if_pos hz, if_neg hy]
      exact le_top
  have hd (z : ℝ) : HasDerivAt ψ (z ^ 3 + z) z := by
    convert (((hasDerivAt_id z).pow 4).div_const 4).add
      (((hasDerivAt_id z).pow 2).div_const 2) using 1
    dsimp [ψ, id]
    ring
  have hD (a b : ℝ) : divergence ψ a b = ψ a - ψ b - (b ^ 3 + b) * (a - b) := by
    rw [divergence, fderiv_eq_deriv_mul, (hd b).deriv]
  have hD0 (z : ℝ) : divergence ψ z 0 = z ^ 4 / 4 + z ^ 2 / 2 := by
    rw [hD]
    simp [ψ]
  have hdiff : DifferentiableOn ℝ ψ (interior (univ : Set ℝ)) := by
    simpa only [interior_univ] using hdiffAll
  have h1 : iterate V ψ η loss (1 / 2) 1 = some 0 := by
    change advance V ψ 1 f0 (1 / 2) = some 0
    exact hseqOld 1 (by norm_num)
  have hfact (z : ℝ) : z ^ 4 / 2 + z ^ 2 - 5 * z / 4 + 11 / 32 =
      (z - 1 / 2) ^ 2 * ((z + 1 / 2) ^ 2 / 2 + 5 / 4) := by ring
  have hfin1 : ∀ z ∈ V, f1 z ≠ ⊤ ∧ f1 z ≠ ⊥ := by
    intro z hz
    simp only [f1, if_pos hz]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hm1real : IsMinOn (fun z => (f1 z).toReal + (1 / 2 : ℝ)⁻¹ * divergence ψ z 0)
      V (1 / 2) := by
    intro z hz
    change (f1 (1 / 2)).toReal + (1 / 2 : ℝ)⁻¹ * divergence ψ (1 / 2) 0 ≤
      (f1 z).toReal + (1 / 2 : ℝ)⁻¹ * divergence ψ z 0
    simp only [f1, if_pos hhalf, if_pos hz, EReal.toReal_coe]
    rw [hD0, hD0]
    norm_num
    have hq : 0 ≤ (z - 1 / 2) ^ 2 * ((z + 1 / 2) ^ 2 / 2 + 5 / 4) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    nlinarith only [hq, hfact z]
  have hm1 : IsMinOn (fun z => f1 z + (((1 / 2 : ℝ)⁻¹ * divergence ψ z 0 : ℝ) : EReal))
      V (1 / 2) :=
    (proximal_finitePart_minimizer_iff f1 V ψ (1 / 2) 0 (1 / 2) hhalf hfin1).mpr hm1real
  have huniq1 (p : ℝ) (hp : p ∈ V)
      (hm : IsMinOn (fun z => f1 z + (((1 / 2 : ℝ)⁻¹ * divergence ψ z 0 : ℝ) : EReal)) V p) :
      p = 1 / 2 := by
    have hh := hm hhalf
    change f1 p + (((1 / 2 : ℝ)⁻¹ * divergence ψ p 0 : ℝ) : EReal) ≤
      f1 (1 / 2) + (((1 / 2 : ℝ)⁻¹ * divergence ψ (1 / 2) 0 : ℝ) : EReal) at hh
    simp only [f1, if_pos hp, if_pos hhalf, ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
    rw [hD0, hD0] at hh
    norm_num at hh
    have hlow : (5 / 4 : ℝ) * (p - 1 / 2) ^ 2 ≤
        p ^ 4 / 2 + p ^ 2 - 5 * p / 4 + 11 / 32 := by
      rw [hfact]
      nlinarith only [mul_nonneg (sq_nonneg (p - 1 / 2)) (sq_nonneg (p + 1 / 2))]
    have hsq : (p - 1 / 2) ^ 2 = 0 := by
      apply le_antisymm ?_ (sq_nonneg _)
      nlinarith only [hlow, hh]
    have he : p - 1 / 2 = 0 := sq_eq_zero_iff.mp hsq
    linarith
  have ha1 : advance V ψ (1 / 2) f1 0 = some (1 / 2) := by
    cases h : advance V ψ (1 / 2) f1 0 with
    | none => exact ((advance_none_iff V ψ (1 / 2) f1 0).mp h ⟨1 / 2, hhalf, hm1⟩).elim
    | some p =>
        obtain ⟨hp, hm⟩ := advance_some_spec V ψ (1 / 2) f1 0 p h
        exact congrArg some (huniq1 p hp hm)
  have h2 : iterate V ψ η loss (1 / 2) 2 = some (1 / 2) := by
    change (iterate V ψ η loss (1 / 2) 1).bind (advance V ψ (η 1) (loss 1)) = some (1 / 2)
    rw [h1]
    change advance V ψ (1 / 2) f1 0 = some (1 / 2)
    exact ha1
  have hseq : ∀ t ≤ 2, iterate V ψ η loss (1 / 2) t = some (x t) := by
    intro t ht
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases ht' with rfl | rfl | rfl
    · rfl
    · simpa [x] using h1
    · simpa [x] using h2
  have hi : ∀ t ≤ 2, x t ∈ interior (univ : Set ℝ) := by simp
  have hη : ∀ t < 2, 0 < η t := by
    intro t _
    by_cases h : t = 0 <;> norm_num [η, h]
  have hmono : ∀ t, t + 1 < 2 → η (t + 1) ≤ η t := by
    intro t ht
    have he : t = 0 := by omega
    subst t
    norm_num [η]
  have hf (t : ℕ) (_ : t < 2) : SourceProper (loss t) := by
    by_cases h : t = 0
    · simpa [loss, h, V, f0, f1] using hf0
    · simpa [loss, h, V, f0, f1] using hf1
  have hs (t : ℕ) (_ : t < 2) : ∀ z ∈ V, (SourceSubdifferential (loss t) z).Nonempty := by
    by_cases h : t = 0
    · simpa [loss, h, V, f0, f1] using hs0
    · simpa [loss, h, V, f0, f1] using hs1
  have hmaxNeg : ((range 2).sup' (by decide) (fun t => divergence ψ (-1 / 2) (x t))) = 5 / 8 := by
    apply le_antisymm
    · apply Finset.sup'_le_iff.mpr
      intro t ht
      have he : t = 0 ∨ t = 1 := by have := mem_range.mp ht; omega
      rcases he with rfl | rfl <;> norm_num [x, hD, ψ]
    · calc
        (5 / 8 : ℝ) = divergence ψ (-1 / 2) (x 0) := by rw [hD]; norm_num [ψ, x]
        _ ≤ _ := Finset.le_sup' _ (by decide : 0 ∈ range 2)
  have hmaxPos : ((range 2).sup' (by decide) (fun t => divergence ψ (1 / 2) (x t))) = 9 / 64 := by
    apply le_antisymm
    · apply Finset.sup'_le_iff.mpr
      intro t ht
      have he : t = 0 ∨ t = 1 := by have := mem_range.mp ht; omega
      rcases he with rfl | rfl <;> norm_num [x, hD, ψ]
    · calc
        (9 / 64 : ℝ) = divergence ψ (1 / 2) (x 1) := by rw [hD]; norm_num [ψ, x]
        _ ≤ _ := Finset.le_sup' _ (by decide : 1 ∈ range 2)
  have hsharp : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        ((range 2).sup' (by decide) (fun t => divergence ψ u (x t))) / η 1 -
        divergence ψ u (x 2) / η 1 -
        ∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / η t := by
    intro u hu
    exact iterate_variable_sharp V univ (convex_Icc (-1 : ℝ) 1) ψ hdiff η loss (1 / 2) x 2
      (by norm_num) hseq hi hη hmono hf hs u hu
      ((range 2).sup' (by decide) (fun t => divergence ψ u (x t)))
      (fun t ht => Finset.le_sup' _ (mem_range.mpr ht))
  have hprinted : ∀ u ∈ V,
      (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        ((range 2).sup' (by decide) (fun t => divergence ψ u (x t))) / η 1 -
        ∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / η t := by
    intro u hu
    exact iterate_variable_regret V univ (convex_Icc (-1 : ℝ) 1) (fun _ _ => mem_univ _)
      ψ hstrict hdiff η loss (1 / 2) x 2 (by norm_num) hseq hi hη hmono hf hs u hu
  have hnumSharp : (-7 / 4 : ℝ) ≤ -29 / 64 := by
    have h := hsharp (-1 / 2) (by norm_num [V])
    rw [hmaxNeg] at h
    convert h using 1 <;> norm_num [sum_range_succ, loss, f0, f1, V, x, η, hD, ψ]
  have hnumPrinted : (-1 / 2 : ℝ) ≤ -11 / 64 := by
    have h := hprinted (1 / 2) hhalf
    rw [hmaxPos] at h
    convert h using 1 <;> norm_num [sum_range_succ, loss, f0, f1, V, x, η, hD, ψ]
  refine ⟨hf0, hf1, hs0, hs1, hclosed, hstrict, hdiffAll, by norm_num [η], by norm_num [η],
    hη, hmono, hseq, ?_, ?_, ?_, hmaxNeg, hmaxPos, ?_, hsharp, hprinted, hnumSharp, hnumPrinted⟩
  · rw [hD]
    norm_num [ψ, x]
  · rw [hD]
    norm_num [ψ, x]
  · norm_num [sum_range_succ, η, x, hD, ψ]
  · simp [x, divergence_self]
'''
footer='end BanditRL.OnlinePrescientBregmanRegretCanary\n'
text=old.decode('utf8'); assert text.endswith(footer)
test.write_bytes((text[:-len(footer)]+t['exact_header']+' := by\n'+body+'\n'+footer).encode('utf8'))
assert test.read_bytes().startswith(old[:-len(footer.encode())])
write(RUN/'decreasing-canary-source-attempt-v1.lean',test.read_bytes())
capture('decreasing-canary-statement-fence-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['declaration'],'--file',test.relative_to(ROOT),'--output',CONTRACT/'decreasing-canary-fence-v1.json')
code,out=capture('decreasing-canary-focused-build-v1','lake','build','Tests.OnlinePrescientBregmanRegretCanary',required=False)
passed=code==0 and 'Built Tests.OnlinePrescientBregmanRegretCanary' in out and 'Build completed successfully' in out
write(RUN/'decreasing-canary-focused-inspected-v1.json',dict(actual_exit=code,compiled=passed,new_Test_Built_marker='Built Tests.OnlinePrescientBregmanRegretCanary' in out,canary_sha256=sha(test),production_sha256=sha(PUBLIC),full_conjunctions=2,first_conjunction_preserved=True,numeric_VALUE_audit='pending',source_container_closed=False,whole_Goal_status='ACTIVE'))
if passed:
    capture('decreasing-canary-safe-verify-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/'decreasing-canary-fence-v1.json')
else:
    print(out[-6000:])
    event('native-decreasing-canary-repair-v1','repair',dict(leaf=t['declaration'],actual_exit=code,frozen_header_unchanged=True,evidence='decreasing-canary-focused-build-v1.json'))
fixed()
assert passed
print('Two full concrete canaries compiled; exact numeric proof VALUE audits and all combined/integration gates pending.')
