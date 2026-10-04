import BanditRLProof
import Tests.OnlineLinearizationCanary

open Set Finset
open BanditRL.OnlineOptimalStep

namespace OptimalStepProbe

noncomputable section

theorem positive_optimizer : 0 < optimalStep 9 4 :=
  optimal_positive 9 4 (by norm_num) (by norm_num)

theorem chosen : optimalStep 9 4 = 3 / 2 := by
  norm_num [optimalStep]

theorem attained : upperBound 9 4 (3 / 2) = 6 := by
  norm_num [upperBound]

theorem public_argmin :
    0 < optimalStep 9 4 ∧ upperBound 9 4 (optimalStep 9 4) = Real.sqrt (9 * 4) ∧
    ∀ η : ℝ, 0 < η → upperBound 9 4 (optimalStep 9 4) ≤ upperBound 9 4 η :=
  source_argmin 9 4 (by norm_num) (by norm_num)

theorem universal (η : ℝ) (hη : 0 < η) : 6 ≤ upperBound 9 4 η := by
  have h := lower_bound 9 4 η (by norm_num) (by norm_num) hη
  norm_num at h
  exact h

theorem unique (η : ℝ) (hη : 0 < η) : upperBound 9 4 η = 6 ↔ η = 3 / 2 := by
  simpa only [chosen, attained] using optimal_unique 9 4 η (by norm_num) (by norm_num) hη

theorem wrong_eta_strict : upperBound 9 4 1 = 13 / 2 ∧ 6 < upperBound 9 4 1 := by
  norm_num [upperBound]

theorem tuned :
    optimalStep 9 16 = 3 / 4 ∧ upperBound 9 16 (3 / 4) = 12 ∧
    ∀ η : ℝ, 0 < η → upperBound 9 16 (3 / 4) ≤ upperBound 9 16 η := by
  have h := diameter_argmin 3 2 4 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem horizon_one :
    optimalStep 9 4 = 3 / 2 ∧ upperBound 9 4 (3 / 2) = 6 ∧
    ∀ η : ℝ, 0 < η → upperBound 9 4 (3 / 2) ≤ upperBound 9 4 η := by
  have h := diameter_argmin 3 2 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem zero_distance_no_min (η : ℝ) (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ upperBound 0 4 θ < upperBound 0 4 η :=
  ⟨η / 2, zero_distance_decreases 4 η (by norm_num) hη⟩

theorem zero_energy_no_min (η : ℝ) (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ upperBound 9 0 θ < upperBound 9 0 η :=
  ⟨2 * η, zero_energy_decreases 9 η (by norm_num) hη⟩

theorem all_zero (η : ℝ) : upperBound 0 0 η = 0 := zero_coefficients η

theorem zero_distance_optimizer_inadmissible :
    optimalStep 0 4 = 0 ∧ ¬ 0 < optimalStep 0 4 := by
  norm_num [optimalStep]

theorem division_zero_inadmissible :
    upperBound 9 0 0 = 0 ∧ ∀ η : ℝ, 0 < η → 0 < upperBound 9 0 η := by
  constructor
  · norm_num [upperBound]
  · intro η hη
    dsimp [upperBound]
    positivity

-- Reuse the earlier canary's shared actual unbounded domain.
abbrev V : BanditRL.OnlineGradientDescent.Domain ℝ := LinearizationProbe.V
def loss (x : ℝ) : ℝ := (x - 1) ^ 2 / 2
def X (η : ℝ) : ℕ → ℝ :=
  BanditRL.OnlineGradientDescent.iterate V η (fun _ => loss) 0
def feedback (η : ℝ) (t : ℕ) : ℝ := gradient loss (X η t)
def energy (η : ℝ) : ℝ := ∑ t ∈ range 2, (feedback η t) ^ 2

theorem actual_gradient (x : ℝ) : gradient loss x = x - 1 := by
  have hd : HasDerivAt loss (x - 1) x := by
    convert (((hasDerivAt_id x).sub_const (1 : ℝ)).pow 2).div_const 2 using 1 <;>
      norm_num <;> ring
  exact hd.hasGradientAt'.gradient

theorem actual_projection (z : ℝ) : BanditRL.OnlineGradientDescent.project V z = z := by
  apply BanditRL.OnlineGradientDescent.project_eq_of_variational
  · change z ∈ univ
    trivial
  · intro w hw
    simp

theorem first_output (η : ℝ) : X η 0 = 0 := rfl

theorem after_one (η : ℝ) : X η 1 = η := by
  dsimp [X, BanditRL.OnlineGradientDescent.iterate, BanditRL.OnlineGradientDescent.step]
  rw [actual_gradient, actual_projection]
  simp [smul_eq_mul]

theorem first_feedback (η : ℝ) : feedback η 0 = -1 := by
  rw [feedback, first_output, actual_gradient]
  norm_num

theorem second_feedback (η : ℝ) : feedback η 1 = η - 1 := by
  rw [feedback, after_one, actual_gradient]

theorem energy_formula (η : ℝ) : energy η = 1 + (η - 1) ^ 2 := by
  simp [energy, Finset.sum_range_succ, first_feedback, second_feedback]

theorem same_loss_different_energy : energy 1 = 1 ∧ energy 2 = 2 ∧ energy 1 ≠ energy 2 := by
  rw [energy_formula, energy_formula]
  norm_num

end
end OptimalStepProbe
