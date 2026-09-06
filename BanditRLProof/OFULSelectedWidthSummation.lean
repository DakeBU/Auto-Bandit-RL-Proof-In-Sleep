import BanditRLProof.OFULFiniteActionOptimism
import BanditRLProof.OFULEllipticalPotentialFoundation

/-!
# Selected-width summation for OFUL

This module converts the compiled logarithmic elliptical-potential endpoint
into cumulative clipped confidence-width bounds for arbitrary feature and
selected-action sequences. The route is deterministic and finite-horizon.
-/

namespace BanditRLProof
namespace OFUL

universe u v

/--
The confidence width clipped at the inverse-quadratic level. This equals
`min 1 (confidenceWidth V x)` when `V` is positive definite.
-/
noncomputable def clippedConfidenceWidth
    {Feature : Type u} [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (x : Feature -> Real) : Real :=
  Real.sqrt (min 1 (dotProduct x (V⁻¹.mulVec x)))

/-- Clipping before the square root agrees with clipping the confidence width. -/
theorem clippedConfidenceWidth_eq_min_one_confidenceWidth
    {Feature : Type u} [Fintype Feature] [DecidableEq Feature]
    (V : Matrix Feature Feature Real) (hV : V.PosDef)
    (x : Feature -> Real) :
    clippedConfidenceWidth V x = min 1 (confidenceWidth V x) := by
  let q : Real := dotProduct x (V⁻¹.mulVec x)
  have hq_nonneg : 0 <= q := hV.inv.posSemidef.dotProduct_mulVec_nonneg x
  change Real.sqrt (min 1 q) = min 1 (Real.sqrt q)
  by_cases hq_one : q <= 1
  · rw [min_eq_right hq_one, min_eq_right]
    exact (Real.sqrt_le_one).2 hq_one
  · have hone_q : 1 <= q := le_of_lt (lt_of_not_ge hq_one)
    rw [min_eq_left hone_q, min_eq_left, Real.sqrt_one]
    exact (Real.one_le_sqrt).2 hone_q

/--
The cumulative clipped widths of a bounded feature sequence are controlled
by the square root of the standard logarithmic elliptical-potential budget.
-/
theorem sum_range_clippedConfidenceWidth_le_sqrt_mul_sqrt_log
    {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (history : Nat -> Feature -> Real) (T : Nat) (L2 : Real)
    (hL2 : 0 <= L2)
    (hbound : forall t, t < T ->
      dotProduct (history t) (history t) <= L2) :
    (Finset.range T).sum (fun t =>
        clippedConfidenceWidth
          (regularizedPrefixFeatureGram lambda history t) (history t)) <=
      Real.sqrt (T : Real) *
        Real.sqrt
          (2 * ((Fintype.card Feature : Real) *
            Real.log (1 +
              (T * L2) /
                ((Fintype.card Feature : Real) * lambda)))) := by
  let q : Nat -> Real := fun t =>
    dotProduct (history t)
      ((regularizedPrefixFeatureGram lambda history t)⁻¹.mulVec (history t))
  have hq_nonneg : forall t, 0 <= q t := fun t =>
    regularizedPrefixFeatureGram_inv_quadratic_nonneg
      lambda hlambda history t (history t)
  have hpotential :
      (Finset.range T).sum (fun t => min 1 (q t)) <=
        2 * ((Fintype.card Feature : Real) *
          Real.log (1 +
            (T * L2) /
              ((Fintype.card Feature : Real) * lambda))) := by
    simpa only [q] using
      (standardLogDeterminantAndEllipticalPotential
        lambda hlambda history T L2 hL2 hbound).2
  have hcs :=
    Real.sum_sqrt_mul_sqrt_le
      (Finset.range T)
      (f := fun _ => (1 : Real))
      (g := fun t => min 1 (q t))
      (fun _ => zero_le_one)
      (fun t => le_min zero_le_one (hq_nonneg t))
  calc
    (Finset.range T).sum (fun t =>
        clippedConfidenceWidth
          (regularizedPrefixFeatureGram lambda history t) (history t)) =
        (Finset.range T).sum (fun t =>
          Real.sqrt 1 * Real.sqrt (min 1 (q t))) := by
      apply Finset.sum_congr rfl
      intro t _ht
      simp only [clippedConfidenceWidth, q, Real.sqrt_one, one_mul]
    _ <=
        Real.sqrt ((Finset.range T).sum (fun _ => (1 : Real))) *
          Real.sqrt ((Finset.range T).sum (fun t => min 1 (q t))) := hcs
    _ =
        Real.sqrt (T : Real) *
          Real.sqrt ((Finset.range T).sum (fun t => min 1 (q t))) := by
      simp
    _ <=
        Real.sqrt (T : Real) *
          Real.sqrt
            (2 * ((Fintype.card Feature : Real) *
              Real.log (1 +
                (T * L2) /
                  ((Fintype.card Feature : Real) * lambda)))) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hpotential) (Real.sqrt_nonneg _)

/-- Public confidence-width form of the clipped selected-feature sum bound. -/
theorem sum_range_min_one_confidenceWidth_le_sqrt_mul_sqrt_log
    {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (history : Nat -> Feature -> Real) (T : Nat) (L2 : Real)
    (hL2 : 0 <= L2)
    (hbound : forall t, t < T ->
      dotProduct (history t) (history t) <= L2) :
    (Finset.range T).sum (fun t =>
        min 1
          (confidenceWidth
            (regularizedPrefixFeatureGram lambda history t) (history t))) <=
      Real.sqrt (T : Real) *
        Real.sqrt
          (2 * ((Fintype.card Feature : Real) *
            Real.log (1 +
              (T * L2) /
                ((Fintype.card Feature : Real) * lambda)))) := by
  have hsum :=
    sum_range_clippedConfidenceWidth_le_sqrt_mul_sqrt_log
      lambda hlambda history T L2 hL2 hbound
  calc
    (Finset.range T).sum (fun t =>
        min 1
          (confidenceWidth
            (regularizedPrefixFeatureGram lambda history t) (history t))) =
        (Finset.range T).sum (fun t =>
          clippedConfidenceWidth
            (regularizedPrefixFeatureGram lambda history t) (history t)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact
        (clippedConfidenceWidth_eq_min_one_confidenceWidth
          (regularizedPrefixFeatureGram lambda history t)
          (regularizedPrefixFeatureGram_posDef
            lambda hlambda history t)
          (history t)).symm
    _ <= _ := hsum

/--
Raw selected-feature widths satisfy the same bound when every charged width
is at most one.
-/
theorem sum_range_confidenceWidth_le_sqrt_mul_sqrt_log_of_width_le_one
    {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (history : Nat -> Feature -> Real) (T : Nat) (L2 : Real)
    (hL2 : 0 <= L2)
    (hbound : forall t, t < T ->
      dotProduct (history t) (history t) <= L2)
    (hwidth : forall t, t < T ->
      confidenceWidth
        (regularizedPrefixFeatureGram lambda history t) (history t) <= 1) :
    (Finset.range T).sum (fun t =>
        confidenceWidth
          (regularizedPrefixFeatureGram lambda history t) (history t)) <=
      Real.sqrt (T : Real) *
        Real.sqrt
          (2 * ((Fintype.card Feature : Real) *
            Real.log (1 +
              (T * L2) /
                ((Fintype.card Feature : Real) * lambda)))) := by
  calc
    (Finset.range T).sum (fun t =>
        confidenceWidth
          (regularizedPrefixFeatureGram lambda history t) (history t)) =
        (Finset.range T).sum (fun t =>
          min 1
            (confidenceWidth
              (regularizedPrefixFeatureGram lambda history t) (history t))) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (min_eq_right (hwidth t (Finset.mem_range.mp ht))).symm
    _ <= _ :=
      sum_range_min_one_confidenceWidth_le_sqrt_mul_sqrt_log
        lambda hlambda history T L2 hL2 hbound

/--
Selected-action specialization of the cumulative clipped confidence-width
bound.
-/
theorem
    sum_range_selectedAction_min_one_confidenceWidth_le_sqrt_mul_sqrt_log
    {Feature : Type u} {Action : Type v}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (actionFeature : Action -> Feature -> Real)
    (selectedAction : Nat -> Action)
    (T : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hbound : forall t, t < T ->
      dotProduct (actionFeature (selectedAction t))
        (actionFeature (selectedAction t)) <= L2) :
    (Finset.range T).sum (fun t =>
        min 1
          (confidenceWidth
            (regularizedPrefixFeatureGram lambda
              (fun s => actionFeature (selectedAction s)) t)
            (actionFeature (selectedAction t)))) <=
      Real.sqrt (T : Real) *
        Real.sqrt
          (2 * ((Fintype.card Feature : Real) *
            Real.log (1 +
              (T * L2) /
                ((Fintype.card Feature : Real) * lambda)))) := by
  exact sum_range_min_one_confidenceWidth_le_sqrt_mul_sqrt_log
    lambda hlambda (fun t => actionFeature (selectedAction t))
    T L2 hL2 hbound

/-- Raw selected-action width sum under an explicit small-width contract. -/
theorem
    sum_range_selectedAction_confidenceWidth_le_sqrt_mul_sqrt_log_of_width_le_one
    {Feature : Type u} {Action : Type v}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (actionFeature : Action -> Feature -> Real)
    (selectedAction : Nat -> Action)
    (T : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hbound : forall t, t < T ->
      dotProduct (actionFeature (selectedAction t))
        (actionFeature (selectedAction t)) <= L2)
    (hwidth : forall t, t < T ->
      confidenceWidth
        (regularizedPrefixFeatureGram lambda
          (fun s => actionFeature (selectedAction s)) t)
        (actionFeature (selectedAction t)) <= 1) :
    (Finset.range T).sum (fun t =>
        confidenceWidth
          (regularizedPrefixFeatureGram lambda
            (fun s => actionFeature (selectedAction s)) t)
          (actionFeature (selectedAction t))) <=
      Real.sqrt (T : Real) *
        Real.sqrt
          (2 * ((Fintype.card Feature : Real) *
            Real.log (1 +
              (T * L2) /
                ((Fintype.card Feature : Real) * lambda)))) := by
  exact sum_range_confidenceWidth_le_sqrt_mul_sqrt_log_of_width_le_one
    lambda hlambda (fun t => actionFeature (selectedAction t))
    T L2 hL2 hbound hwidth

end OFUL
end BanditRLProof
