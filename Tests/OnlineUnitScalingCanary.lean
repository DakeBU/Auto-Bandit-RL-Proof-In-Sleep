import BanditRLProof.OnlineUnitScaling
import BanditRLProof

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineSubgradientPolicy
open BanditRL.OnlineUnitScaling
open scoped InnerProductSpace
namespace UnitScalingProbe

def loss : ℕ → ℝ → EReal := fun _ x => (x : EReal)
def policy : SupportPolicy (E := ℝ) := fun t _ h f =>
  gradient (fun z => (f z).toReal) (h (Fin.last t))
def eta : ℕ → ℝ := fun _ => 1
abbrev old (t : ℕ) := output V eta loss 0 policy t
abbrev good (t : ℕ) := output V (scaledEta 1000 eta)
  (fun s => scaledLoss 1000 (loss s)) ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) t
abbrev bad (t : ℕ) := output V eta
  (fun s => scaledLoss 1000 (loss s)) ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) t

theorem dimensions_eta : ((2, -1) : ℤ × ℤ) = (1, 0) + (1, 0) - (0, 1) :=
  unit_exponents (1, 0) (0, 1) (2, -1) (by norm_num)

theorem dimensions_regret :
    (((1, 0) : ℤ × ℤ) + (1, 0) - ((1, 0) + (1, 0) - (0, 1)) = (0, 1)) ∧
    ((((1, 0) : ℤ × ℤ) + (1, 0) - (0, 1)) + ((0, 1) - (1, 0)) +
      ((0, 1) - (1, 0)) = (0, 1)) :=
  regret_unit_exponents (1, 0) (0, 1)

theorem real_linear_gradient (x : ℝ) :
    gradient (fun z => (loss 0 z).toReal) x = 1 := by
  simpa only [loss, EReal.toReal_coe] using (hasDerivAt_id x).hasGradientAt'.gradient

theorem real_scaled_gradient (x : ℝ) :
    gradient (fun z : ℝ => 1000 * z) x = 1000 := by
  have hg := gradient_scaled 1000 (fun z : ℝ => z) x (differentiableAt_id)
  have hid : gradient (fun z : ℝ => z) ((1000 : ℝ) • x) = 1 :=
    (hasDerivAt_id _).hasGradientAt'.gradient
  simp only [smul_eq_mul] at hid hg
  rw [hid] at hg
  simpa only [mul_one] using hg

theorem support (t : ℕ) (x : ℝ) : SourceSubdifferential (loss t) x = {1} := by
  have hf : (fun y : ℝ => ((inner ℝ (1 : ℝ) y + 0 : ℝ) : EReal)) = loss t := by
    funext y
    change ((y * 1 + 0 : ℝ) : EReal) = (y : EReal)
    simp only [mul_one, add_zero]
  rw [← hf]
  exact affine_subdifferential (1 : ℝ) 0 x

theorem loss_on (t : ℕ) : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t) := by
  constructor
  · refine ⟨?_, 0, 0, rfl⟩
    intro x
    simp [loss]
  · intro x hx
    rw [support]
    exact Set.singleton_nonempty _

theorem selected_one (η : ℕ → ℝ) (t : ℕ) : selected V η loss 0 policy t = 1 := by
  change gradient (fun z => (loss t z).toReal) _ = 1
  exact real_linear_gradient _

theorem legal (η : ℕ → ℝ) (T : ℕ) : LegalFeedback V η loss 0 policy T := by
  intro t ht
  rw [selected_one, support]
  exact Set.mem_singleton _

theorem correct_eta : scaledEta 1000 eta 0 = 1 / 1000000 := by
  norm_num [scaledEta, eta]

theorem positive_eta : 0 < scaledEta 1000 eta 0 :=
  scaled_eta_positive 1000 (by norm_num) eta 0 (by norm_num [eta])

theorem old_one (η : ℕ → ℝ) : output V η loss 0 policy 1 = -η 0 := by
  rw [output_succ, output_zero, selected_one, V, BanditRL.OnlineHuber.project_fullSpace]
  simp [smul_eq_mul]

theorem correct_path : good 1 = -1 / 1000 := by
  unfold good
  rw [output_scaling 1000 (by norm_num) eta loss 0 policy 1, old_one]
  norm_num [eta]

theorem wrong_path : bad 1 = -1000 := by
  have h := wrong_step_output 1000 (by norm_num) eta loss 0 policy 1
  rw [old_one] at h
  change (1000 : ℝ) * bad 1 = _ at h
  norm_num [eta] at h
  linarith

theorem physical_path_difference :
    1000 * good 1 = -1 ∧ 1000 * bad 1 = -1000000 ∧ good 1 ≠ bad 1 := by
  rw [correct_path, wrong_path]
  norm_num

theorem transformed_selected :
    selected V (scaledEta 1000 eta) (fun s => scaledLoss 1000 (loss s))
      ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) 0 = 1000 := by
  rw [selected_scaling 1000 (by norm_num), selected_one]
  norm_num

theorem transformed_legal :
    LegalFeedback V (scaledEta 1000 eta) (fun s => scaledLoss 1000 (loss s))
      ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) 1 :=
  legal_feedback_scaling 1000 (by norm_num) eta loss 0 policy 1
    (fun t _ => (loss_on t).1) (legal eta 1)

theorem old_regret : regret V eta loss 0 policy (-2) 1 = 2 := by
  simp [regret, output_zero, loss]

theorem correct_regret :
    regret V (scaledEta 1000 eta) (fun s => scaledLoss 1000 (loss s))
      ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) ((1000 : ℝ)⁻¹ • (-2 : ℝ)) 1 = 2 := by
  rw [regret_scaling 1000 (by norm_num)]
  exact old_regret

theorem positive_old_energy : (∑ t ∈ range 1, ‖selected V eta loss 0 policy t‖ ^ 2) = (1 : ℝ) := by
  simp [selected_one]

theorem positive_terminal : ‖old 1 - (-2)‖ ^ 2 = (1 : ℝ) := by
  unfold old
  rw [old_one]
  norm_num [eta]

theorem scaled_energy :
    (∑ t ∈ range 1, ‖selected V (scaledEta 1000 eta)
      (fun s => scaledLoss 1000 (loss s)) ((1000 : ℝ)⁻¹ • (0 : ℝ))
      (scaledPolicy 1000 policy) t‖ ^ 2) = (1000000 : ℝ) := by
  rw [energy_scaling 1000 (by norm_num), positive_old_energy]
  norm_num

theorem scaled_distance : ‖(1000 : ℝ)⁻¹ • (0 : ℝ) - (1000 : ℝ)⁻¹ • (-2 : ℝ)‖ ^ 2 = 4 / 1000000 := by
  rw [distance_square_scaling 1000 (by norm_num)]
  norm_num

theorem actual_sharp_bound :
    regret V (scaledEta 1000 (fun _ => (1 : ℝ))) (fun s => scaledLoss 1000 (loss s))
      ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) ((1000 : ℝ)⁻¹ • (-2 : ℝ)) 1 ≤
      ‖(0 : ℝ) - (-2)‖ ^ 2 / (2 * 1) + (1 : ℝ) / 2 *
        (∑ t ∈ range 1, ‖selected V (fun _ => (1 : ℝ)) loss 0 policy t‖ ^ 2) -
        ‖output V (fun _ => (1 : ℝ)) loss 0 policy 1 - (-2)‖ ^ 2 / (2 * 1) :=
  regret_fixed_scaled 1000 (by norm_num) 1 (by norm_num) loss 0 policy 1
    (fun t _ => loss_on t) (legal _ 1) (-2)

theorem sharp_rhs :
    ‖(0 : ℝ) - (-2)‖ ^ 2 / (2 * 1) + (1 : ℝ) / 2 *
      (∑ t ∈ range 1, ‖selected V eta loss 0 policy t‖ ^ 2) -
      ‖old 1 - (-2)‖ ^ 2 / (2 * 1) = 2 := by
  rw [positive_old_energy, positive_terminal]
  norm_num

theorem coarse_bound_invariant :
    BanditRL.OnlineOptimalStep.upperBound (4 / 1000 ^ 2) (1000 ^ 2 * 1)
      (1 / 1000 ^ 2) = BanditRL.OnlineOptimalStep.upperBound 4 1 1 :=
  upper_bound_scaling 1000 (by norm_num) 4 1 1 (by norm_num)

theorem inverse_inadmissible_zero :
    scaledLoss (0 : ℝ)⁻¹ (scaledLoss 0 (loss 0)) (1 : ℝ) ≠ loss 0 1 := by
  norm_num [scaledLoss, loss]

theorem identity_scale :
    output V (scaledEta 1 eta) (fun s => scaledLoss 1 (loss s))
      ((1 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1 policy) 1 = old 1 := by
  simpa using output_scaling 1 (by norm_num) eta loss 0 policy 1

theorem source_horizon_boundary :
    0 < (1 / Real.sqrt (1 : ℝ)) ∧ (1 / Real.sqrt (0 : ℝ)) = 0 ∧ ¬ (0 < (0 : ℝ)) := by
  norm_num

theorem empty_regret :
    regret V (scaledEta 1000 eta) (fun s => scaledLoss 1000 (loss s))
      ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) ((1000 : ℝ)⁻¹ • (-2 : ℝ)) 0 = 0 := by
  simp [regret]

theorem zero_horizon_actual_sharp :
    regret V (scaledEta 1000 (fun _ => (1 : ℝ))) (fun s => scaledLoss 1000 (loss s))
      ((1000 : ℝ)⁻¹ • (0 : ℝ)) (scaledPolicy 1000 policy) ((1000 : ℝ)⁻¹ • (-2 : ℝ)) 0 ≤
      ‖(0 : ℝ) - (-2)‖ ^ 2 / (2 * 1) + (1 : ℝ) / 2 *
        (∑ t ∈ range 0, ‖selected V (fun _ => (1 : ℝ)) loss 0 policy t‖ ^ 2) -
        ‖output V (fun _ => (1 : ℝ)) loss 0 policy 0 - (-2)‖ ^ 2 / (2 * 1) :=
  regret_fixed_scaled 1000 (by norm_num) 1 (by norm_num) loss 0 policy 0
    (fun t _ => loss_on t) (legal _ 0) (-2)

end UnitScalingProbe
