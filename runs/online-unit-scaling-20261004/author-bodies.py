from pathlib import Path
import json, sys
run = Path(__file__).resolve().parent
headers = json.loads((run / 'draft-headers-v1.json').read_text(encoding='utf-8'))
context = (run / 'leaves/context-v1.lean.txt').read_text(encoding='utf-8').split('end BanditRL.OnlineUnitScaling')[0]
bodies = {
    'unit_exponents': '''  calc
    H = (H + (L - X)) - (L - X) := by abel
    _ = X - (L - X) := by rw [h]
    _ = X + X - L := by abel''',
    'regret_unit_exponents': '''  constructor <;> abel''',
    'inverse_loss': '''  funext y
  simp only [scaledLoss, smul_inv_smul₀ hc.ne']''',
    'proper_scaled_loss': '''  rcases hf with ⟨hbot, x, r, hr⟩
  constructor
  · intro y
    exact hbot (c • y)
  · refine ⟨c⁻¹ • x, r, ?_⟩
    simpa only [scaledLoss, smul_inv_smul₀ hc.ne'] using hr''',
    'subgradient_scaled': '''  let A : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  have ha : A.adjoint g = c • g := by
    apply ext_inner_right ℝ
    intro z
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_smul_right]
  have hs := theorem_2_28 f hf A 0 y
    (show c • g ∈ A.adjoint '' SourceSubdifferential f (A y + 0) from
      ⟨g, by simpa only [A, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, add_zero] using hg, ha⟩)
  simpa only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    add_zero, scaledLoss] using hs''',
    'subdifferentiable_scaled': '''  refine ⟨proper_scaled_loss c hc f hf.1, ?_⟩
  intro y hy
  obtain ⟨g, hg⟩ := hf.2 (c • y) (show c • y ∈ V.carrier from Set.mem_univ _)
  exact ⟨c • g, subgradient_scaled c hc f hf.1 y g hg⟩''',
    'hasGradientAt_scaled': '''  let A : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  have hd : HasFDerivAt (fun z => f (c • z))
      ((InnerProductSpace.toDual ℝ E g).comp A) y := by
    simpa only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] using
      hf.hasFDerivAt.comp y A.hasFDerivAt
  have he : InnerProductSpace.toDual ℝ E (c • g) =
      (InnerProductSpace.toDual ℝ E g).comp A := by
    ext z
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
      A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_smul_right]
  rw [hasGradientAt_iff_hasFDerivAt, he]
  exact hd''',
    'gradient_scaled': '''  exact (hasGradientAt_scaled c f y (gradient f (c • y))
    hf.hasGradientAt).gradient''',
    'step_scaling': '''  have hs : c⁻¹ * η = (η / c ^ 2) * c := by
    field_simp
  simp only [smul_sub, smul_smul, hs]''',
    'wrong_step_scaling': '''  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  congr 1
  congr 1
  ring''',
    'scaled_eta_positive': '''  exact div_pos hη (sq_pos_of_pos hc)''',
    'history_scaling': '''  induction t with
  | zero => rfl
  | succ t ih =>
    rw [history_succ, history_succ]
    simp only [output, selected, ih, scaledPolicy, inverse_loss c hc,
      smul_inv_smul₀ hc.ne', V, BanditRL.OnlineHuber.project_fullSpace, scaledEta]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      simpa only [output, selected] using
        (step_scaling c hc (η t) (output V η loss x₁ p t)
          (selected V η loss x₁ p t)).symm
    · simp only [Fin.snoc_castSucc]''',
    'output_scaling': '''  exact congrArg (fun h : Fin (t + 1) → E => h (Fin.last t))
    (history_scaling c hc η loss x₁ p t)''',
    'selected_scaling': '''  simp only [selected, scaledPolicy, history_scaling c hc,
    inverse_loss c hc, smul_inv_smul₀ hc.ne']''',
    'legal_feedback_scaling': '''  intro t ht
  rw [selected_scaling c hc]
  apply subgradient_scaled c hc (loss t) (hproper t ht)
  simpa only [output_scaling c hc, smul_inv_smul₀ hc.ne'] using hlegal t ht''',
    'loss_value_scaling': '''  simp only [scaledLoss, output_scaling c hc, smul_inv_smul₀ hc.ne']''',
    'regret_scaling': '''  unfold regret
  apply sum_congr rfl
  intro t ht
  dsimp only
  rw [loss_value_scaling c hc η loss x₁ p t]
  simp only [scaledLoss, smul_inv_smul₀ hc.ne']''',
    'wrong_step_output': '''  have hη : scaledEta c (fun s => c ^ 2 * η s) = η := by
    funext s
    apply (div_eq_iff (pow_ne_zero 2 hc.ne')).mpr
    ring
  have ho := output_scaling c hc (fun s => c ^ 2 * η s) loss x₁ p t
  rw [hη] at ho
  rw [ho, smul_inv_smul₀ hc.ne']''',
    'distance_square_scaling': '''  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), mul_pow]
  simp only [inv_pow, div_eq_mul_inv]
  ring''',
    'energy_scaling': '''  simp only [selected_scaling c hc, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, mul_pow]
  rw [mul_sum]''',
    'upper_bound_scaling': '''  unfold BanditRL.OnlineOptimalStep.upperBound
  field_simp''',
    'regret_fixed_scaled': '''  rw [regret_scaling c hc]
  exact BanditRL.OnlineSubgradientPolicy.regret_fixed V η hη loss x₁ p
    (Set.mem_univ _) T hloss hlegal u (Set.mem_univ _)''',
}
names = list(headers)
count = int(sys.argv[1])
label = sys.argv[2]
assert all(name in bodies for name in names[:count])
target = context + '\n\n'.join(headers[name] + ' := by\n' + bodies[name] for name in names[:count]) + '\n\nend BanditRL.OnlineUnitScaling\n'
(run / 'leaves' / (label + '.lean')).write_text(target, encoding='utf-8')
print('Wrote', label, count, 'actual bodies; other frozen targets remain pending.')
