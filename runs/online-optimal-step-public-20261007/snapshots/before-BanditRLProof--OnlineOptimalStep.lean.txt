import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Frozen-coefficient stepsize minimization

Orabona arXiv:1912.13213v10, printed page15/PDF27, unnumbered main-text
scalar minimization and the D/(G sqrt T) tuning calculation. Coefficients are
held fixed. Realized gradient energy depends on the stepsize itself, so these
scalar minima do not construct a learner using future information or optimize
regret across rerun trajectories. Actual OGD/OSD guarantees are separate.

Strict positivity is required for the attained positive-coefficient argmin;
one-zero cases have no minimizer among positive stepsizes, with explicit
strictly improving alternatives. Both-zero is the constant-zero algebraic
extension. Equality and gap identities are library refinements.
-/

namespace BanditRL.OnlineOptimalStep

noncomputable def upperBound (A B η : ℝ) : ℝ := A / (2 * η) + η * B / 2
noncomputable def optimalStep (A B : ℝ) : ℝ := Real.sqrt A / Real.sqrt B

theorem gap_identity (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) :
    upperBound A B η - Real.sqrt A * Real.sqrt B =
      (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η) := by
  have hAsq := Real.sq_sqrt hA
  have hBsq := Real.sq_sqrt hB
  dsimp [upperBound]
  field_simp [ne_of_gt hη]
  linear_combination -hAsq - η ^ 2 * hBsq

theorem lower_bound (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) :
    Real.sqrt A * Real.sqrt B ≤ upperBound A B η := by
  have hgap := gap_identity A B η hA hB hη
  have hnon : 0 ≤ (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η) := by positivity
  linarith

theorem optimal_positive (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < optimalStep A B := by
  exact div_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hB)

theorem optimal_value (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    upperBound A B (optimalStep A B) = Real.sqrt A * Real.sqrt B := by
  have hη := optimal_positive A B hA hB
  have hBroot : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  have hgap := gap_identity A B (optimalStep A B) hA.le hB.le hη
  have hz : Real.sqrt A - optimalStep A B * Real.sqrt B = 0 := by
    simp [optimalStep, div_mul_cancel₀ _ hBroot]
  rw [hz] at hgap
  exact sub_eq_zero.mp (by simpa using hgap)

theorem optimal_unique (A B η : ℝ) (hA : 0 < A) (hB : 0 < B) (hη : 0 < η) :
    upperBound A B η = upperBound A B (optimalStep A B) ↔ η = optimalStep A B := by
  rw [optimal_value A B hA hB]
  constructor
  · intro he
    have hgap := gap_identity A B η hA.le hB.le hη
    rw [he, sub_self] at hgap
    have hden : 2 * η ≠ 0 := ne_of_gt (mul_pos (by norm_num) hη)
    have hsq : (Real.sqrt A - η * Real.sqrt B) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hgap.symm).resolve_right hden
    have hz : Real.sqrt A - η * Real.sqrt B = 0 := pow_eq_zero hsq
    unfold optimalStep
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr hB))).mpr
    linarith
  · rintro rfl
    exact optimal_value A B hA hB

theorem source_argmin (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < optimalStep A B ∧
    upperBound A B (optimalStep A B) = Real.sqrt (A * B) ∧
    ∀ η : ℝ, 0 < η → upperBound A B (optimalStep A B) ≤ upperBound A B η := by
  refine ⟨optimal_positive A B hA hB, ?_, ?_⟩
  · rw [optimal_value A B hA hB, Real.sqrt_mul hA.le]
  · intro η hη
    rw [optimal_value A B hA hB]
    exact lower_bound A B η hA.le hB.le hη

theorem distance_energy_argmin (R B : ℝ) (hR : 0 < R) (hB : 0 < B) :
    optimalStep (R ^ 2) B = R / Real.sqrt B ∧
    upperBound (R ^ 2) B (R / Real.sqrt B) = R * Real.sqrt B ∧
    ∀ η : ℝ, 0 < η → upperBound (R ^ 2) B (R / Real.sqrt B) ≤ upperBound (R ^ 2) B η := by
  have hRsq : 0 < R ^ 2 := sq_pos_of_pos hR
  have hsource := source_argmin (R ^ 2) B hRsq hB
  have hopt : optimalStep (R ^ 2) B = R / Real.sqrt B := by
    dsimp [optimalStep]
    rw [Real.sqrt_sq hR.le]
  refine ⟨hopt, ?_, ?_⟩
  · rw [← hopt, optimal_value (R ^ 2) B hRsq hB, Real.sqrt_sq hR.le]
  · simpa only [hopt] using hsource.2.2

theorem diameter_argmin (D G : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G) (hT : 0 < T) :
    optimalStep (D ^ 2) (G ^ 2 * (T : ℝ)) = D / (G * Real.sqrt (T : ℝ)) ∧
    upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) =
      D * G * Real.sqrt (T : ℝ) ∧
    ∀ η : ℝ, 0 < η →
      upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) ≤
      upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) η := by
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hB : 0 < G ^ 2 * (T : ℝ) := mul_pos (sq_pos_of_pos hG) hTr
  have hroot : Real.sqrt (G ^ 2 * (T : ℝ)) = G * Real.sqrt (T : ℝ) := by
    rw [Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG.le]
  simpa only [hroot, mul_assoc] using distance_energy_argmin D (G ^ 2 * (T : ℝ)) hD hB

theorem zero_distance_decreases (B η : ℝ) (hB : 0 < B) (hη : 0 < η) :
    0 < η / 2 ∧ upperBound 0 B (η / 2) < upperBound 0 B η := by
  constructor
  · positivity
  · dsimp [upperBound]
    simp only [zero_div, zero_add]
    nlinarith [mul_pos hη hB]

theorem zero_energy_decreases (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    0 < 2 * η ∧ upperBound A 0 (2 * η) < upperBound A 0 η := by
  constructor
  · positivity
  · dsimp [upperBound]
    simp only [mul_zero, zero_div, add_zero]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_pos hA hη]

theorem zero_coefficients (η : ℝ) : upperBound 0 0 η = 0 := by
  simp [upperBound]

end BanditRL.OnlineOptimalStep
