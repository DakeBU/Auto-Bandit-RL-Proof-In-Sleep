from common import *
fixed()
d=load(CONTRACT/'canary-stabilized-v1.json')
assert sha(PUBLIC)==d['production_sha256']
bodies=[r'''by
  let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
  have hs : StrictConvexOn ℝ univ ψ := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have h2 := (Even.strictConvexOn_pow (𝕜 := ℝ) (by decide : Even 2)
      (by decide : 2 ≠ 0)).2 hx hy hxy ha hb hab
    have h4 := (Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 4)).2 hx hy ha.le hb.le hab
    dsimp [ψ]
    simp only [smul_eq_mul] at h2 h4 ⊢
    nlinarith only [h2, h4]
  have hd : ∀ z : ℝ, HasDerivAt ψ (z ^ 3 + z) z := by
    intro z
    convert (((hasDerivAt_id z).pow 4).div_const 4).add
      (((hasDerivAt_id z).pow 2).div_const 2) using 1 <;> ring
  have hD : ∀ a b : ℝ, divergence ψ a b = ψ a - ψ b - (b ^ 3 + b) * (a - b) := by
    intro a b
    have hg : gradient ψ b = b ^ 3 + b := by simpa using (hd b).hasGradientAt.gradient
    rw [divergence_eq_gradient ψ a b (hd b).differentiableAt, hg]
    simp [RCLike.inner_apply']
  have hm : IsMinOn (fun z : ℝ => |z| + divergence ψ z (1 / 2)) univ 0 := by
    intro z hz
    change |(0 : ℝ)| + divergence ψ 0 (1 / 2) ≤ |z| + divergence ψ z (1 / 2)
    rw [hD, hD]
    dsimp [ψ]
    norm_num
    by_cases hz' : 0 ≤ z
    · rw [abs_of_nonneg hz']
      nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]
    · rw [abs_of_nonpos (le_of_not_ge hz')]
      nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]
  have hf : ConvexOn ℝ (univ : Set ℝ) (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using
      (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℝ)))
  have hb : ∀ u : ℝ, -|u| ≤ divergence ψ u (1 / 2) -
      divergence ψ u 0 - divergence ψ 0 (1 / 2) := by
    intro u
    have hh := proximal_one_step univ abs ψ 1 (by norm_num) (1 / 2) 0
      (mem_univ 0) hf (hd (1 / 2)).differentiableAt (hd 0).differentiableAt
      (by simpa only [inv_one, one_mul] using hm) u (mem_univ u)
    simpa only [one_mul, abs_zero, zero_sub] using hh
  have hv : divergence ψ (1 / 2) 0 = 9 / 64 := by rw [hD]; norm_num [ψ]
  have hmoving : divergence ψ 0 (1 / 2) = 11 / 64 := by rw [hD]; norm_num [ψ]
  refine ⟨hs, hm, not_differentiableAt_abs_zero, hv, hmoving, hb, ?_⟩
  have hh := hb (1 / 2)
  have hl : -|(1 / 2 : ℝ)| = -1 / 2 := by norm_num
  have hr : divergence ψ (1 / 2) (1 / 2) - divergence ψ (1 / 2) 0 -
      divergence ψ 0 (1 / 2) = -5 / 16 := by
    rw [divergence_self, hv, hmoving]
    norm_num
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh
''',r'''by
  let ψ : ℝ → ℝ := fun z => z ^ 2 / 2
  have hs : StrictConvexOn ℝ univ ψ := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have h2 := (Even.strictConvexOn_pow (𝕜 := ℝ) (by decide : Even 2)
      (by decide : 2 ≠ 0)).2 hx hy hxy ha hb hab
    dsimp [ψ]
    simp only [smul_eq_mul] at h2 ⊢
    nlinarith only [h2]
  have hd : ∀ z : ℝ, HasDerivAt ψ z z := by
    intro z
    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;> ring
  have hD : ∀ a b : ℝ, divergence ψ a b = (a - b) ^ 2 / 2 := by
    intro a b
    have hg : gradient ψ b = b := by simpa using (hd b).hasGradientAt.gradient
    rw [divergence_eq_gradient ψ a b (hd b).differentiableAt, hg]
    simp only [RCLike.inner_apply', conj_trivial]
    dsimp [ψ]
    ring
  have hm : IsMinOn (fun z : ℝ => |z| + divergence ψ z (-1)) (Icc 0 1) 0 := by
    intro z hz
    change |(0 : ℝ)| + divergence ψ 0 (-1) ≤ |z| + divergence ψ z (-1)
    rw [hD, hD, abs_of_nonneg hz.1]
    norm_num only [abs_zero]
    nlinarith [sq_nonneg z, hz.1]
  have hf : ConvexOn ℝ (Icc (0 : ℝ) 1) (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using
      (convexOn_norm (convex_Icc (0 : ℝ) 1))
  have hb : ∀ u ∈ Icc (0 : ℝ) 1, -|u| ≤ divergence ψ u (-1) -
      divergence ψ u 0 - divergence ψ 0 (-1) := by
    intro u hu
    have hh := proximal_one_step (Icc 0 1) abs ψ 1 (by norm_num) (-1) 0
      (by simp) hf (hd (-1)).differentiableAt (hd 0).differentiableAt
      (by simpa only [inv_one, one_mul] using hm) u hu
    simpa only [one_mul, abs_zero, zero_sub] using hh
  have hmoving : divergence ψ 0 (-1) = 1 / 2 := by rw [hD]; norm_num
  refine ⟨hs, by norm_num, hm, hmoving, hb, ?_⟩
  have hh := hb (1 / 2) (by norm_num)
  have hl : -|(1 / 2 : ℝ)| = -1 / 2 := by norm_num
  have hr : divergence ψ (1 / 2) (-1) - divergence ψ (1 / 2) 0 -
      divergence ψ 0 (-1) = 1 / 2 := by
    rw [hD, hD, hD]
    norm_num
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh
''']
text='/- Two concrete instances, not additional source results or a causal algorithm. -/\nimport BanditRLProof.OnlineBregmanProximal\nimport Mathlib.Analysis.Calculus.Deriv.Abs\nimport Mathlib.Analysis.Calculus.Deriv.Pow\nimport Mathlib.Analysis.Convex.Mul\nimport Mathlib.Tactic.NormNum\nopen Set BanditRL.OnlineBregman\nnamespace BanditRL.OnlineBregmanCanary\n\n'
for t,b in zip(d['targets'],bodies):text+=t['exact_proposed_header']+' := '+b+'\n'
text+='end BanditRL.OnlineBregmanCanary\n'
p=ROOT/'Tests/OnlineBregmanProximalCanary.lean'
write(p,text)
write(RUN/'canary-first-attempt-v1.lean',p.read_bytes())
write(RUN/'canary-local-helper-inventory-v1.json',dict(named_new_declarations=[t['declaration'] for t in d['targets']],local_helpers=['ψ polynomial','hs strict convexity via strict square and convex quartic','hd actual polynomial derivative','hD exact ordered divergence via public gradient conversion','hm actual domain minimum','hf abs convexity','hb public proximal comparison','hv/hmoving exact nonzero divergence values','hl/hr expression equalities, final Eq.mp universal specialization'],production_VALUE_required=['proximal_one_step','divergence_eq_gradient'],planned_nonnegative_use='No concrete canary VALUE use claimed; full generic public VALUE witness covers divergence_nonneg. Original planned-consumer list is prospective only.',extra_named_helpers=[]))
rc,out=capture('focused-canary-build-v1','lake','build','Tests.OnlineBregmanProximalCanary',required=False)
print(out[-12000:],flush=True)
fixed()
