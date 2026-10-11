import BanditRLProof

/-! Public-root tests for Orabona v10's fixed-step projected OGD chain. -/
noncomputable section
open Set Finset
open BanditRL.OnlineGradientDescent

namespace Tests.OnlineGradientDescent

def interval : Domain ℝ where
  carrier := Icc 0 1
  nonempty := ⟨0, by norm_num⟩
  closed := isClosed_Icc
  convex := convex_Icc 0 1

def losses (t : ℕ) (x : ℝ) : ℝ := (if t = 0 then -2 else 1 / 2) * x

lemma linear_regular (c : ℝ) : RegularLoss interval (fun x : ℝ => c * x) := by
  refine ⟨univ, isOpen_univ, subset_univ _, ?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    ring_nf
    exact le_rfl
  · exact (differentiable_id.const_mul c).differentiableOn

lemma losses_regular (t : ℕ) : RegularLoss interval (losses t) :=
  linear_regular _

lemma gradient_linear (c x : ℝ) : gradient (fun y : ℝ => c * y) x = c := by
  simpa using (((hasDerivAt_id x).const_mul c).hasGradientAt).gradient

lemma gradient_losses (t : ℕ) (x : ℝ) :
    gradient (losses t) x = if t = 0 then -2 else 1 / 2 := by
  exact gradient_linear _ _

lemma project_high : project interval (2 : ℝ) = 1 := by
  apply project_eq_of_variational interval 2 1 (by norm_num [interval])
  intro w hw
  change w ∈ Icc (0 : ℝ) 1 at hw
  change (w - 1) * (2 - 1) ≤ 0
  nlinarith [hw.2]

lemma project_half : project interval (1 / 2 : ℝ) = 1 / 2 := by
  apply project_eq_of_variational interval (1 / 2) (1 / 2) (by norm_num [interval])
  intro w hw
  simp

lemma trajectory_one : iterate interval 1 losses 0 1 = 1 := by
  simp only [iterate, step, gradient_losses]
  norm_num
  exact project_high

lemma trajectory_two : iterate interval 1 losses 0 2 = 1 / 2 := by
  change step interval 1 (losses 1) (iterate interval 1 losses 0 1) = _
  rw [trajectory_one]
  simp only [step, gradient_losses, if_neg (by decide : (1 : ℕ) ≠ 0)]
  norm_num
  exact project_half

/-- Nondegenerate: gradient step leaves the interval, projection changes it, next loss changes sign,
regret is positive and the terminal squared distance is strictly positive. -/
theorem nondegenerate_canary :
    iterate interval 1 losses 0 1 = 1 ∧
    iterate interval 1 losses 0 2 = 1 / 2 ∧
    regret interval 1 losses 0 0 2 = 1 / 2 ∧
    ‖iterate interval 1 losses 0 2 - (0 : ℝ)‖ ^ 2 = 1 / 4 := by
  refine ⟨trajectory_one, trajectory_two, ?_, ?_⟩
  · simp only [regret, sum_range_succ, sum_range_zero, zero_add]
    rw [trajectory_one]
    norm_num [iterate, losses]
  · rw [trajectory_two]
    norm_num

/-- Public fixed-step endpoint applies to the exact active-projection trajectory. -/
example : regret interval 1 losses 0 0 2 ≤ ‖(0 : ℝ) - 0‖ ^ 2 / (2 * 1) +
    1 / 2 * (∑ t ∈ range 2, ‖gradient (losses t) (iterate interval 1 losses 0 t)‖ ^ 2) -
    ‖iterate interval 1 losses 0 2 - 0‖ ^ 2 / (2 * 1) :=
  theorem_2_13_fixed interval 1 (by norm_num) losses 0 (by norm_num [interval]) 2
    (fun t _ => losses_regular t) 0 (by norm_num [interval])

/-- Eq. (2.1) instantiates a different, horizon-tuned trajectory with uniform gradient bounds. -/
example : ∀ u ∈ interval.carrier,
    regret interval (1 / (2 * Real.sqrt 2)) losses 0 u 2 ≤ 1 * 2 * Real.sqrt 2 := by
  apply equation_2_1 interval losses 0 (by norm_num [interval]) 2 (by decide)
    1 2 (by norm_num) (by norm_num)
  · intro x hx y hy
    change x ∈ Icc (0 : ℝ) 1 at hx
    change y ∈ Icc (0 : ℝ) 1 at hy
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · exact fun t _ => losses_regular t
  · intro t ht
    simp only [gradient_losses]
    split_ifs <;> norm_num

/-- Finite-dimensional Euclidean instantiation requires no additional analytic assumptions. -/
example (V : Domain (EuclideanSpace ℝ (Fin 3))) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ) (x₁ : EuclideanSpace ℝ (Fin 3))
    (hx : x₁ ∈ V.carrier) (T : ℕ) (hloss : ∀ t < T, RegularLoss V (loss t))
    (u : EuclideanSpace ℝ (Fin 3)) (hu : u ∈ V.carrier) :
    regret V η loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖gradient (loss t) (iterate V η loss x₁ t)‖ ^ 2) -
      ‖iterate V η loss x₁ T - u‖ ^ 2 / (2 * η) :=
  theorem_2_13_fixed V η hη loss x₁ hx T hloss u hu

#print axioms BanditRL.OnlineGradientDescent.project_spec
#print axioms BanditRL.OnlineGradientDescent.project_eq_of_variational
#print axioms BanditRL.OnlineGradientDescent.proposition_2_11
#print axioms BanditRL.OnlineGradientDescent.first_order
#print axioms BanditRL.OnlineGradientDescent.lemma_2_12
#print axioms BanditRL.OnlineGradientDescent.iterate_prefix
#print axioms BanditRL.OnlineGradientDescent.theorem_2_13_fixed
#print axioms BanditRL.OnlineGradientDescent.equation_2_1
#print axioms nondegenerate_canary
end Tests.OnlineGradientDescent

