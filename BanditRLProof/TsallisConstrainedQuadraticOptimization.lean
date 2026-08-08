import BanditRLProof.TsallisScheduledSelfBoundingInterpolation

/-!
# Constrained quadratic optimization for self-bounding Tsallis analysis

This module gives a rigorous finite-sum version of the one-round optimization
used after lambda interpolation.  In contrast to the informal paper lemma,
the quadratic coefficients are required to be strictly positive and the
simplex-derived square-root mass constraint is explicit.
-/

namespace BanditRLProof
namespace Tsallis

universe u

/-- A downward quadratic is bounded by its unconstrained vertex value. -/
theorem linear_sub_quadratic_le_sq_div_four
    (b x c : Real) (hc : 0 < c) :
    b * x - c * x ^ 2 ≤ b ^ 2 / (4 * c) := by
  rw [le_div_iff₀ (by positivity : 0 < 4 * c)]
  nlinarith [sq_nonneg (2 * c * x - b)]

/-- Coordinatewise completion of squares gives the unconstrained finite-sum
branch of the paper's quadratic optimization. -/
theorem sum_linear_sub_quadratic_le_unconstrained
    {Index : Type u} [DecidableEq Index]
    (indices : Finset Index) (b : Real) (c x : Index → Real)
    (hc : ∀ i ∈ indices, 0 < c i) :
    indices.sum (fun i => b * x i - c i * x i ^ 2) ≤
      b ^ 2 / 4 * indices.sum (fun i => 1 / c i) := by
  calc
    indices.sum (fun i => b * x i - c i * x i ^ 2) ≤
        indices.sum (fun i => b ^ 2 / (4 * c i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact linear_sub_quadratic_le_sq_div_four b (x i) (c i) (hc i hi)
    _ = b ^ 2 / 4 * indices.sum (fun i => 1 / c i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [ne_of_gt (hc i hi)]

/-- If the unconstrained vertex lies beyond a finite `sum x ≤ M` constraint,
shift the common linear coefficient and apply completion of squares to obtain
the active-constraint branch. -/
theorem sum_linear_sub_quadratic_le_of_sum_le
    {Index : Type u} [DecidableEq Index]
    (indices : Finset Index) (b M : Real) (c x : Index → Real)
    (hc : ∀ i ∈ indices, 0 < c i)
    (hreciprocal : 0 < indices.sum (fun i => 1 / c i))
    (hxsum : indices.sum x ≤ M)
    (hthreshold :
      2 * M ≤ b * indices.sum (fun i => 1 / c i)) :
    indices.sum (fun i => b * x i - c i * x i ^ 2) ≤
      b * M - M ^ 2 / indices.sum (fun i => 1 / c i) := by
  let reciprocal := indices.sum (fun i => 1 / c i)
  let shifted := 2 * M / reciprocal
  let residual := b - shifted
  have hresidual : 0 ≤ residual := by
    dsimp [residual, shifted, reciprocal]
    rw [sub_nonneg, div_le_iff₀ hreciprocal]
    simpa [mul_comm] using hthreshold
  have hvertex :
      indices.sum (fun i => shifted * x i - c i * x i ^ 2) ≤
        shifted ^ 2 / 4 * reciprocal := by
    simpa [reciprocal] using
      (sum_linear_sub_quadratic_le_unconstrained
        indices shifted c x hc)
  calc
    indices.sum (fun i => b * x i - c i * x i ^ 2) =
        residual * indices.sum x +
          indices.sum (fun i => shifted * x i - c i * x i ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [residual]
      ring
    _ ≤ residual * M + shifted ^ 2 / 4 * reciprocal :=
      add_le_add (mul_le_mul_of_nonneg_left hxsum hresidual) hvertex
    _ = b * M - M ^ 2 / indices.sum (fun i => 1 / c i) := by
      dsimp [residual, shifted, reciprocal]
      field_simp [ne_of_gt hreciprocal]
      ring

/-- Positive coefficients on a nonempty finite set have a positive reciprocal
sum. -/
theorem sum_inv_pos_of_nonempty
    {Index : Type u} [DecidableEq Index]
    (indices : Finset Index) (hindices : indices.Nonempty)
    (c : Index → Real) (hc : ∀ i ∈ indices, 0 < c i) :
    0 < indices.sum (fun i => 1 / c i) := by
  rcases hindices with ⟨i, hi⟩
  exact Finset.sum_pos'
    (fun j hj => (one_div_pos.mpr (hc j hj)).le)
    ⟨i, hi, one_div_pos.mpr (hc i hi)⟩

/-- A finite simplex point has suboptimal square-root mass at most the square
root of the number of suboptimal coordinates. -/
theorem sum_erase_sqrt_le_sqrt_card
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (probability : Action → Real)
    (hprobability : FTRL.finiteSimplex arms probability) :
    (arms.erase best).sum (fun action => Real.sqrt (probability action)) ≤
      Real.sqrt ((arms.erase best).card : Real) := by
  let suboptimal := arms.erase best
  have hprobNonneg : ∀ action,
      0 ≤ if action ∈ suboptimal then probability action else 0 := by
    intro action
    by_cases haction : action ∈ suboptimal
    · rw [if_pos haction]
      exact hprobability.1 action (Finset.mem_of_mem_erase haction)
    · simp [haction]
  have hsqrt := Real.sum_sqrt_mul_sqrt_le suboptimal
    hprobNonneg (fun _ => (zero_le_one : (0 : Real) ≤ 1))
  have hsumProbability : suboptimal.sum probability ≤ 1 := by
    have hsplit := Finset.add_sum_erase arms probability hbest
    rw [hprobability.2] at hsplit
    have hbestNonneg := hprobability.1 best hbest
    dsimp [suboptimal]
    linarith
  have hsumIf :
      suboptimal.sum (fun action =>
        if action ∈ suboptimal then probability action else 0) =
        suboptimal.sum probability := by
    apply Finset.sum_congr rfl
    intro action haction
    simp [haction]
  calc
    suboptimal.sum (fun action => Real.sqrt (probability action)) =
        suboptimal.sum (fun action =>
          Real.sqrt (if action ∈ suboptimal then probability action else 0) *
            Real.sqrt (1 : Real)) := by
      apply Finset.sum_congr rfl
      intro action haction
      simp [haction]
    _ ≤ Real.sqrt
          (suboptimal.sum (fun action =>
            if action ∈ suboptimal then probability action else 0)) *
        Real.sqrt (suboptimal.sum (fun _ => (1 : Real))) :=
      hsqrt
    _ = Real.sqrt (suboptimal.sum probability) *
        Real.sqrt (suboptimal.card : Real) := by
      rw [hsumIf]
      simp
    _ ≤ Real.sqrt 1 * Real.sqrt (suboptimal.card : Real) := by
      gcongr
    _ = Real.sqrt (suboptimal.card : Real) := by simp

/-- The unconstrained one-round branch after substituting
`x action = sqrt (probability action)` and
`c action = lambda * gap action`. -/
theorem sum_erase_sqrt_probability_sub_gap_le_unconstrained
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action}
    (probability gap : Action → Real)
    (hprobability : FTRL.finiteSimplex arms probability)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (b lambda : Real) (hlambda : 0 < lambda) :
    (arms.erase best).sum (fun action =>
        b * Real.sqrt (probability action) -
          lambda * gap action * probability action) ≤
      b ^ 2 / 4 * (arms.erase best).sum (fun action =>
        1 / (lambda * gap action)) := by
  have hc : ∀ action ∈ arms.erase best,
      0 < lambda * gap action := by
    intro action haction
    exact mul_pos hlambda (hgap action haction)
  calc
    (arms.erase best).sum (fun action =>
        b * Real.sqrt (probability action) -
          lambda * gap action * probability action) =
        (arms.erase best).sum (fun action =>
          b * Real.sqrt (probability action) -
            (lambda * gap action) *
              Real.sqrt (probability action) ^ 2) := by
      apply Finset.sum_congr rfl
      intro action haction
      rw [Real.sq_sqrt
        (hprobability.1 action (Finset.mem_of_mem_erase haction))]
    _ ≤ b ^ 2 / 4 * (arms.erase best).sum (fun action =>
        1 / (lambda * gap action)) :=
      sum_linear_sub_quadratic_le_unconstrained
        (arms.erase best) b (fun action => lambda * gap action)
          (fun action => Real.sqrt (probability action)) hc

/-- On the active-constraint branch, finite-simplex square-root mass sharpens
the unconstrained coordinatewise bound by the common mass constraint. -/
theorem sum_erase_sqrt_probability_sub_gap_le_of_threshold
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (probability gap : Action → Real)
    (hprobability : FTRL.finiteSimplex arms probability)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (b lambda : Real) (hlambda : 0 < lambda)
    (hthreshold :
      2 * Real.sqrt ((arms.erase best).card : Real) ≤
        b * (arms.erase best).sum (fun action =>
          1 / (lambda * gap action))) :
    (arms.erase best).sum (fun action =>
        b * Real.sqrt (probability action) -
          lambda * gap action * probability action) ≤
      b * Real.sqrt ((arms.erase best).card : Real) -
        (arms.erase best).card /
          (arms.erase best).sum (fun action =>
            1 / (lambda * gap action)) := by
  have hc : ∀ action ∈ arms.erase best,
      0 < lambda * gap action := by
    intro action haction
    exact mul_pos hlambda (hgap action haction)
  have hreciprocal :
      0 < (arms.erase best).sum (fun action =>
        1 / (lambda * gap action)) :=
    sum_inv_pos_of_nonempty (arms.erase best) hsuboptimal
      (fun action => lambda * gap action) hc
  have hbound := sum_linear_sub_quadratic_le_of_sum_le
    (arms.erase best) b (Real.sqrt ((arms.erase best).card : Real))
      (fun action => lambda * gap action)
      (fun action => Real.sqrt (probability action))
      hc hreciprocal
      (sum_erase_sqrt_le_sqrt_card arms hbest probability hprobability)
      hthreshold
  calc
    (arms.erase best).sum (fun action =>
        b * Real.sqrt (probability action) -
          lambda * gap action * probability action) =
        (arms.erase best).sum (fun action =>
          b * Real.sqrt (probability action) -
            (lambda * gap action) *
              Real.sqrt (probability action) ^ 2) := by
      apply Finset.sum_congr rfl
      intro action haction
      rw [Real.sq_sqrt
        (hprobability.1 action (Finset.mem_of_mem_erase haction))]
    _ ≤ b * Real.sqrt ((arms.erase best).card : Real) -
        Real.sqrt ((arms.erase best).card : Real) ^ 2 /
          (arms.erase best).sum (fun action =>
            1 / (lambda * gap action)) := hbound
    _ = b * Real.sqrt ((arms.erase best).card : Real) -
        (arms.erase best).card /
          (arms.erase best).sum (fun action =>
            1 / (lambda * gap action)) := by
      rw [Real.sq_sqrt (by positivity :
        (0 : Real) ≤ ((arms.erase best).card : Real))]

/-- Generated expected-probability specialization of the unconstrained
one-round quadratic branch. All measure and Jensen obligations are discharged
by the existing finite-simplex expectation theorem. -/
theorem sampledScheduledHalfTsallisExpectedProbability_sum_le_unconstrained
    {Env : Type u} {Action : Type*}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : MeasureTheory.Measure (Env × ((k : Nat) → Action × Real)))
    [MeasureTheory.IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat → Real)
    (t : Nat) {best : Action} (gap : Action → Real)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (b lambda : Real) (hlambda : 0 < lambda) :
    (arms.erase best).sum (fun action =>
        b * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action) -
        lambda * gap action *
          sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action) ≤
      b ^ 2 / 4 * (arms.erase best).sum (fun action =>
        1 / (lambda * gap action)) := by
  exact sum_erase_sqrt_probability_sub_gap_le_unconstrained
    arms
    (sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t)
    gap
    (finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t)
    hgap b lambda hlambda

/-- Generated expected-probability specialization of the active-constraint
one-round quadratic branch. This is the direct consumer for the later
time-threshold split in the improved self-bounding route. -/
theorem sampledScheduledHalfTsallisExpectedProbability_sum_le_of_threshold
    {Env : Type u} {Action : Type*}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : MeasureTheory.Measure (Env × ((k : Nat) → Action × Real)))
    [MeasureTheory.IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat → Real)
    (t : Nat) {best : Action} (hbest : best ∈ arms)
    (gap : Action → Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (b lambda : Real) (hlambda : 0 < lambda)
    (hthreshold :
      2 * Real.sqrt ((arms.erase best).card : Real) ≤
        b * (arms.erase best).sum (fun action =>
          1 / (lambda * gap action))) :
    (arms.erase best).sum (fun action =>
        b * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action) -
        lambda * gap action *
          sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action) ≤
      b * Real.sqrt ((arms.erase best).card : Real) -
        (arms.erase best).card /
          (arms.erase best).sum (fun action =>
            1 / (lambda * gap action)) := by
  exact sum_erase_sqrt_probability_sub_gap_le_of_threshold
    arms hbest
    (sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t)
    gap
    (finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t)
    hsuboptimal hgap b lambda hlambda hthreshold

end Tsallis
end BanditRLProof
