from common import *
fixed()
d = load(CONTRACT / 'canary-stabilized-v1.json')
assert sha(PUBLIC) == d['production_sha256']
bodies = [r'''by
  dsimp only
  let V : Set ℝ := Icc (-1) 1
  let f : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
  let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
  have hp : (0 : ℝ) ∈ V := by norm_num [V]
  have hf : SourceProper f := by
    refine ⟨?_, 0, 0, ?_⟩
    · intro z
      by_cases hz : z ∈ V <;> simp [f, hz]
    · simp [f, hp]
  have hs : ∀ z ∈ V, (SourceSubdifferential f z).Nonempty := by
    intro z hz
    have ha : (SourceSubdifferential (fun y : ℝ => ((|y| : ℝ) : EReal)) z).Nonempty := by
      by_cases hzpos : 0 < z
      · rw [abs_subgradient_positive z hzpos]
        exact ⟨1, rfl⟩
      · by_cases hz0 : z = 0
        · subst z
          rw [abs_subgradient_zero]
          exact ⟨0, by norm_num⟩
        · rw [abs_subgradient_negative z (lt_of_le_of_ne (le_of_not_gt hzpos) hz0)]
          exact ⟨-1, rfl⟩
    obtain ⟨g, hg⟩ := ha
    refine ⟨g, ?_⟩
    intro y
    change f z + (inner ℝ g (y - z) : EReal) ≤ f y
    by_cases hy : y ∈ V
    · simpa only [f, if_pos hz, if_pos hy] using hg y
    · simp only [f, if_pos hz, if_neg hy]
      exact le_top
  have hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥ := by
    intro z hz
    simp only [f, if_pos hz]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hc := finitePart_convex_of_subdifferentiable f V (convex_Icc (-1 : ℝ) 1) hf hs
  have hn : ¬ ConvexOn ℝ (univ : Set ℝ) (fun z => (f z).toReal) := by
    intro h
    have hh := h.2 (mem_univ (0 : ℝ)) (mem_univ (2 : ℝ))
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (by norm_num)
    norm_num [f, V, smul_eq_mul] at hh
  obtain ⟨hstrict, hmin, hnondiff, hv, hmoving, _, _⟩ :=
    BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth
  have hd : ∀ z : ℝ, HasDerivAt ψ (z ^ 3 + z) z := by
    intro z
    convert (((hasDerivAt_id z).pow 4).div_const 4).add
      (((hasDerivAt_id z).pow 2).div_const 2) using 1 <;> dsimp [ψ, id] <;> ring
  have hmreal : IsMinOn (fun z => (f z).toReal + (1 : ℝ)⁻¹ * divergence ψ z (1 / 2)) V 0 := by
    intro z hz
    simpa only [f, if_pos hp, if_pos hz, EReal.toReal_coe, inv_one, one_mul] using
      hmin (mem_univ z)
  have hm : IsMinOn (fun z => f z + ((divergence ψ z (1 / 2) : ℝ) : EReal)) V 0 := by
    simpa only [inv_one, one_mul] using
      (proximal_finitePart_minimizer_iff f V ψ 1 (1 / 2) 0 hp hfin).mpr hmreal
  have hb : ∀ u ∈ V, -|u| ≤ divergence ψ u (1 / 2) - divergence ψ u 0 - divergence ψ 0 (1 / 2) := by
    intro u hu
    have hh := proximal_one_step_extended f V (convex_Icc (-1 : ℝ) 1) hf hs ψ 1
      (by norm_num) (1 / 2) 0 hp (hd (1 / 2)).differentiableAt (hd 0).differentiableAt
      (by simpa only [inv_one, one_mul] using hm) u hu
    simpa only [f, if_pos hp, if_pos hu, EReal.toReal_coe, abs_zero, one_mul, zero_sub] using hh
  refine ⟨hf, hs, by norm_num [f, V], hc, hn, hstrict, hm, hnondiff, hv, hmoving, hb, ?_⟩
  have hh := hb (1 / 2) (by norm_num [V])
  have hl : -|(1 / 2 : ℝ)| = -1 / 2 := by norm_num
  have hr : divergence ψ (1 / 2) (1 / 2) - divergence ψ (1 / 2) 0 -
      divergence ψ 0 (1 / 2) = -5 / 16 := by
    rw [divergence_self, hv, hmoving]
    norm_num
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh
''', r'''by
  dsimp only
  let V : Set ℝ := Icc 0 1
  let f : ℝ → EReal := fun z => if z ∈ V then (z : EReal) else ⊤
  let ψ : ℝ → ℝ := fun z => z ^ 2 / 2
  have hp : (0 : ℝ) ∈ V := by norm_num [V]
  have hf : SourceProper f := by
    refine ⟨?_, 0, 0, ?_⟩
    · intro z
      by_cases hz : z ∈ V <;> simp [f, hz]
    · simp [f, hp]
  have hs : ∀ z ∈ V, (SourceSubdifferential f z).Nonempty := by
    intro z hz
    refine ⟨1, ?_⟩
    intro y
    change f z + (inner ℝ (1 : ℝ) (y - z) : EReal) ≤ f y
    by_cases hy : y ∈ V
    · simp only [f, if_pos hz, if_pos hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      rw [show inner ℝ (1 : ℝ) (y - z) = y - z from by simp [RCLike.inner_apply']]
      linarith
    · simp only [f, if_pos hz, if_neg hy]
      exact le_top
  have hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥ := by
    intro z hz
    simp only [f, if_pos hz]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hc := finitePart_convex_of_subdifferentiable f V (convex_Icc (0 : ℝ) 1) hf hs
  have hn : ¬ ConvexOn ℝ (univ : Set ℝ) (fun z => (f z).toReal) := by
    intro h
    have hh := h.2 (mem_univ (0 : ℝ)) (mem_univ (2 : ℝ))
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (by norm_num)
    norm_num [f, V, smul_eq_mul] at hh
  obtain ⟨hstrict, _, hmin, hmoving, _, _⟩ :=
    BanditRL.OnlineBregmanCanary.boundary_outside_initial
  have hd : ∀ z : ℝ, HasDerivAt ψ z z := by
    intro z
    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;> dsimp [ψ, id] <;> ring
  have hD : ∀ a b : ℝ, divergence ψ a b = (a - b) ^ 2 / 2 := by
    intro a b
    have hg : gradient ψ b = b := by simpa using (hd b).hasGradientAt.gradient
    rw [divergence_eq_gradient ψ a b (hd b).differentiableAt, hg]
    rw [show inner ℝ b (a - b) = b * (a - b) from RCLike.inner_apply' b (a - b)]
    dsimp [ψ]
    ring
  have hmreal : IsMinOn (fun z => (f z).toReal + (1 : ℝ)⁻¹ * divergence ψ z (-1)) V 0 := by
    intro z hz
    have hh := hmin hz
    simpa only [f, if_pos hp, if_pos hz, EReal.toReal_coe, inv_one, one_mul,
      abs_zero, abs_of_nonneg hz.1] using hh
  have hm : IsMinOn (fun z => f z + ((divergence ψ z (-1) : ℝ) : EReal)) V 0 := by
    simpa only [inv_one, one_mul] using
      (proximal_finitePart_minimizer_iff f V ψ 1 (-1) 0 hp hfin).mpr hmreal
  have hb : ∀ u ∈ V, -u ≤ divergence ψ u (-1) - divergence ψ u 0 - divergence ψ 0 (-1) := by
    intro u hu
    have hh := proximal_one_step_extended f V (convex_Icc (0 : ℝ) 1) hf hs ψ 1
      (by norm_num) (-1) 0 hp (hd (-1)).differentiableAt (hd 0).differentiableAt
      (by simpa only [inv_one, one_mul] using hm) u hu
    simpa only [f, if_pos hp, if_pos hu, EReal.toReal_coe, one_mul, zero_sub] using hh
  refine ⟨hf, hs, by norm_num [f, V], by norm_num [V], hc, hn, hstrict, hm, hmoving, hb, ?_⟩
  have hh := hb (1 / 2) (by norm_num [V])
  have hl : -(1 / 2 : ℝ) = -1 / 2 := by norm_num
  have hr : divergence ψ (1 / 2) (-1) - divergence ψ (1 / 2) 0 -
      divergence ψ 0 (-1) = 1 / 2 := by
    rw [hD, hD, hD]
    norm_num
  exact Eq.mp (congrArg₂ (fun a b : ℝ => a ≤ b) hl hr) hh
''']
text = '''/- Infinity-domain concrete instances, not new source results or a causal trajectory. -/
import BanditRLProof.OnlineBregmanExtended
import BanditRLProof.OnlineSubgradientAbsolute
import Tests.OnlineBregmanProximalCanary

noncomputable section
open Set BanditRL.OnlineConvex BanditRL.OnlineBregman
namespace BanditRL.OnlineBregmanExtendedCanary

'''
for t, b in zip(d['targets'], bodies):
    text += t['exact_proposed_header'] + ' := ' + b + '\n'
text += 'end BanditRL.OnlineBregmanExtendedCanary\n'
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
write(p, text)
write(RUN / 'canary-first-attempt-v1.lean', p.read_bytes())
write(RUN / 'canary-local-helper-inventory-v1.json', dict(
    named_new_declarations=[t['declaration'] for t in d['targets']], extra_named_helpers=[],
    local_helpers=['Exact V/f/psi lets', 'Properness with finite zero witness',
      'Global supports lifted from absolute-value supports or actual linear slope one',
      'Feasible finiteness', 'Public finitePart convexity', 'Global nonconvexity at endpoints zero/two',
      'Reused exact prior strict/minimum/divergence facts', 'Actual psi derivatives',
      'EReal minimum via public bridge', 'Universal comparison via extended helper',
      'Both individual numeric tails via Eq.mp of extended comparison'],
    production_VALUE_required=['finitePart_convex_of_subdifferentiable',
      'proximal_finitePart_minimizer_iff', 'proximal_one_step_extended'],
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
rc, out = capture('focused-canary-build-v1', 'lake', 'build', 'Tests.OnlineBregmanExtendedCanary', required=False)
print(out[-14000:], flush=True)
fixed()
