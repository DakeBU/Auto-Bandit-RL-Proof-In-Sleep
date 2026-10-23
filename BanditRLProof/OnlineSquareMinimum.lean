import BanditRLProof.OnlineLearningFTL
import BanditRLProof.OnlineLearningRegret
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace BanditRL.OnlineLearning
noncomputable def squaredBestRegret (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)

/-- Produced feasible minimum; T0 is the empty-prefix convention, not uniqueness. -/
theorem guessing_prefix_minimum (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    empiricalMean y T ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2) ≤
          ∑ t ∈ Finset.range T, (u - y t)^2 := by
  by_cases hT : T = 0
  · subst T
    simp [empiricalMean]
  · have hp : 0 < T := Nat.pos_of_ne_zero hT
    exact ⟨empiricalMean_mem y T hp hy,
      fun u _ => empiricalMean_minimizes y T hp u⟩

/-- The actual least element is in the interval-loss image; no minimizer is assumed. -/
theorem squaredLoss_minimum_eq (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1) =
        ∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2 := by
  have hm := guessing_prefix_minimum y T hy
  have hleast : IsLeast
      ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) '' Set.Icc (0 : ℝ) 1)
      (∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2) := by
    constructor
    · exact ⟨empiricalMean y T, hm.1, rfl⟩
    · rintro a ⟨u, hu, rfl⟩
      exact hm.2 u hu
  exact hleast.csInf_eq

/-- Signed pathwise minimum regret equals regret at the produced empirical mean. -/
theorem squaredBestRegret_eq_comparatorRegret (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y prediction T =
      comparatorRegret (fun t x => (x - y t)^2) prediction (empiricalMean y T) T := by
  unfold squaredBestRegret comparatorRegret
  rw [squaredLoss_minimum_eq y T hy]

/-- Any feasible fixed comparator gives regret at most the same-horizon minimum regret. -/
theorem comparatorRegret_le_squaredBestRegret (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    comparatorRegret (fun t x => (x - y t)^2) prediction u T ≤
      squaredBestRegret y prediction T := by
  rw [squaredBestRegret_eq_comparatorRegret y prediction T hy]
  unfold comparatorRegret
  exact sub_le_sub_left ((guessing_prefix_minimum y T hy).2 u hu) _

/-- Orabona v10 Theorem 1.3, now expressed against the actual interval minimum. -/
theorem meanPredict_bestRegret_bound (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y (meanPredict y) T ≤ 4 + 4 * Real.log T := by
  rw [squaredBestRegret_eq_comparatorRegret y (meanPredict y) T hy]
  simpa only [comparatorRegret] using theorem_1_3 y T hT hy

/-- Printed p5 intermediate bound: initial half and source rounds 2..T preserved. -/
theorem meanPredict_bestRegret_refined (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y (meanPredict y) T ≤
      (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2) := by
  rw [squaredBestRegret_eq_comparatorRegret y (meanPredict y) T hy]
  simpa only [comparatorRegret] using meanPredict_regret_refined y T hT hy

end BanditRL.OnlineLearning
