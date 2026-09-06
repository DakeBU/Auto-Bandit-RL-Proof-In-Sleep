import BanditRLProof.OFULHistoryEnvironmentRewardLaw
import BanditRLProof.OFULSelectedWidthSummation

/-!
# Canonical OFUL radius-times-width assembly

This module connects the canonical successor-gap tail to the deterministic
selected-width theorem. It first bounds every finite-horizon scalar confidence
radius by one standard log-determinant radius at the terminal horizon.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal NNReal ProbabilityTheory MatrixOrder

universe u

/-- The standard log-determinant budget for a bounded scalar-ridge prefix. -/
noncomputable def standardScalarLogDetBudget
    {Feature : Type u} [Fintype Feature]
    (lambda : Real) (T : Nat) (L2 : Real) : Real :=
  (Fintype.card Feature : Real) *
    Real.log
      (1 +
        (T * L2) /
          ((Fintype.card Feature : Real) * lambda))

/--
A deterministic upper radius obtained by replacing the random determinant
ratio with `exp (standardScalarLogDetBudget ...)`.
-/
noncomputable def standardScalarConfidenceRadiusUpper
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (T : Nat) (L2 : Real) : Real :=
  Real.sqrt
      (2 * R ^ 2 *
        Real.log
          (Real.sqrt
              (Real.exp
                (standardScalarLogDetBudget
                  (Feature := Feature) lambda T L2)) /
            delta)) +
    Real.sqrt lambda * S

/-- The selected-width budget paired with the standard log-determinant term. -/
noncomputable def standardSelectedWidthBudget
    {Feature : Type u} [Fintype Feature]
    (lambda : Real) (T : Nat) (L2 : Real) : Real :=
  Real.sqrt (T : Real) *
    Real.sqrt
      (2 *
        standardScalarLogDetBudget
          (Feature := Feature) lambda T L2)

/-- Deterministic radius-times-width budget used by the canonical gap theorem. -/
noncomputable def standardScalarRadiusWidthBound
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (T : Nat) (L2 : Real) : Real :=
  2 *
    standardScalarConfidenceRadiusUpper
      (Feature := Feature) R delta lambda S T L2 *
    standardSelectedWidthBudget
      (Feature := Feature) lambda T L2

/-- The process scalar Gram is definitionally the regularized feature prefix. -/
theorem finiteHorizonScalarGram_eq_regularizedPrefixFeatureGram
    {Omega Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (feature : Nat -> Omega -> Feature -> Real)
    (n : Nat) (omega : Omega) :
    finiteHorizonScalarGram lambda feature n omega =
      regularizedPrefixFeatureGram lambda (fun t => feature t omega) n := by
  rfl

/-- The standard log-determinant budget is monotone in the horizon. -/
theorem standardScalarLogDetBudget_mono
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (L2 : Real) (hL2 : 0 <= L2)
    {n T : Nat} (hnT : n <= T) :
    standardScalarLogDetBudget (Feature := Feature) lambda n L2 <=
      standardScalarLogDetBudget (Feature := Feature) lambda T L2 := by
  have hcard_pos : 0 < (Fintype.card Feature : Real) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card Feature)
  have hdenom_pos :
      0 < (Fintype.card Feature : Real) * lambda :=
    mul_pos hcard_pos hlambda
  have hnT_real : (n : Real) <= (T : Real) := by
    exact_mod_cast hnT
  have hmul :
      (n : Real) * L2 <= (T : Real) * L2 :=
    mul_le_mul_of_nonneg_right hnT_real hL2
  have hfrac :
      (n * L2) / ((Fintype.card Feature : Real) * lambda) <=
        (T * L2) / ((Fintype.card Feature : Real) * lambda) :=
    (div_le_div_iff_of_pos_right hdenom_pos).2 hmul
  have harg_nonneg :
      0 <=
        (n * L2) / ((Fintype.card Feature : Real) * lambda) :=
    div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hL2) hdenom_pos.le
  have hlog :
      Real.log
          (1 + (n * L2) /
            ((Fintype.card Feature : Real) * lambda)) <=
        Real.log
          (1 + (T * L2) /
            ((Fintype.card Feature : Real) * lambda)) :=
    Real.log_le_log (by linarith) (add_le_add_right hfrac 1)
  exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)

/-- The standard log-determinant budget is nonnegative. -/
theorem standardScalarLogDetBudget_nonneg
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (T : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    0 <= standardScalarLogDetBudget (Feature := Feature) lambda T L2 := by
  have hcard_pos : 0 < (Fintype.card Feature : Real) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card Feature)
  have hdenom_pos :
      0 < (Fintype.card Feature : Real) * lambda :=
    mul_pos hcard_pos hlambda
  have hfrac_nonneg :
      0 <=
        (T * L2) / ((Fintype.card Feature : Real) * lambda) :=
    div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hL2) hdenom_pos.le
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by linarith))

/--
Every prefix scalar confidence radius is bounded by the standard deterministic
radius at a later horizon.
-/
theorem finiteHorizonScalarConfidenceRadius_le_standardUpper
    {Omega Feature : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (feature : Nat -> Omega -> Feature -> Real)
    (R delta S : Real)
    (omega : Omega) (n T : Nat) (hnT : n <= T)
    (L2 : Real) (hL2 : 0 <= L2)
    (hbound : forall t, t < T ->
      dotProduct (feature t omega) (feature t omega) <= L2)
    (hdelta : 0 < delta) :
    finiteHorizonScalarConfidenceRadius
        feature R delta lambda S n omega <=
      standardScalarConfidenceRadiusUpper
        (Feature := Feature) R delta lambda S T L2 := by
  let history : Nat -> Feature -> Real := fun t => feature t omega
  let Bn :=
    standardScalarLogDetBudget (Feature := Feature) lambda n L2
  let BT :=
    standardScalarLogDetBudget (Feature := Feature) lambda T L2
  have hbound_n : forall t, t < n ->
      dotProduct (history t) (history t) <= L2 := by
    intro t htn
    exact hbound t (lt_of_lt_of_le htn hnT)
  have hdet_n :
      (regularizedPrefixFeatureGram lambda history n).det <=
        lambda ^ Fintype.card Feature * Real.exp Bn := by
    simpa only [Bn, standardScalarLogDetBudget] using
      (standardLogDeterminantAndEllipticalPotential
        lambda hlambda history n L2 hL2 hbound_n).1
  have hbudget : Bn <= BT := by
    exact standardScalarLogDetBudget_mono
      (Feature := Feature) lambda hlambda L2 hL2 hnT
  have hdet :
      (regularizedPrefixFeatureGram lambda history n).det <=
        lambda ^ Fintype.card Feature * Real.exp BT :=
    hdet_n.trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hbudget)
        (pow_nonneg hlambda.le _))
  have hbase_pos : 0 < lambda ^ Fintype.card Feature :=
    pow_pos hlambda _
  have hratio :
      (regularizedPrefixFeatureGram lambda history n).det /
          (Matrix.scalar Feature lambda).det <=
        Real.exp BT := by
    rw [det_scalar_identity]
    calc
      (regularizedPrefixFeatureGram lambda history n).det /
          lambda ^ Fintype.card Feature <=
        (lambda ^ Fintype.card Feature * Real.exp BT) /
          lambda ^ Fintype.card Feature :=
        (div_le_div_iff_of_pos_right hbase_pos).2 hdet
      _ = Real.exp BT := by
        field_simp
  have hdet_pos :
      0 < (regularizedPrefixFeatureGram lambda history n).det :=
    regularizedPrefixFeatureGram_det_pos lambda hlambda history n
  have hratio_pos :
      0 <
        (regularizedPrefixFeatureGram lambda history n).det /
          (Matrix.scalar Feature lambda).det := by
    rw [det_scalar_identity]
    exact div_pos hdet_pos hbase_pos
  have hsqrt :
      Real.sqrt
          ((regularizedPrefixFeatureGram lambda history n).det /
            (Matrix.scalar Feature lambda).det) <=
        Real.sqrt (Real.exp BT) :=
    Real.sqrt_le_sqrt hratio
  have hlog :
      Real.log
          (Real.sqrt
              ((regularizedPrefixFeatureGram lambda history n).det /
                (Matrix.scalar Feature lambda).det) /
            delta) <=
        Real.log (Real.sqrt (Real.exp BT) / delta) := by
    apply Real.log_le_log
    · exact div_pos (Real.sqrt_pos.2 hratio_pos) hdelta
    · exact (div_le_div_iff_of_pos_right hdelta).2 hsqrt
  have hthreshold :
      2 * R ^ 2 *
          Real.log
            (Real.sqrt
                ((regularizedPrefixFeatureGram lambda history n).det /
                  (Matrix.scalar Feature lambda).det) /
              delta) <=
        2 * R ^ 2 *
          Real.log (Real.sqrt (Real.exp BT) / delta) :=
    mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (by norm_num) (sq_nonneg R))
  unfold finiteHorizonScalarConfidenceRadius finiteHorizonConfidenceRadius
    finiteHorizonConfidenceThreshold standardScalarConfidenceRadiusUpper
  change
    Real.sqrt
          (2 * R ^ 2 *
            Real.log
              (Real.sqrt
                  ((regularizedPrefixFeatureGram lambda history n).det /
                    (Matrix.scalar Feature lambda).det) /
                delta)) +
        Real.sqrt lambda * S <=
      Real.sqrt
          (2 * R ^ 2 *
            Real.log (Real.sqrt (Real.exp BT) / delta)) +
        Real.sqrt lambda * S
  exact add_le_add (Real.sqrt_le_sqrt hthreshold) le_rfl

/-- The standard deterministic confidence-radius upper bound is nonnegative. -/
theorem standardScalarConfidenceRadiusUpper_nonneg
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (T : Nat) (L2 : Real)
    (hS : 0 <= S) :
    0 <= standardScalarConfidenceRadiusUpper
      (Feature := Feature) R delta lambda S T L2 := by
  exact add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hS)

/-- The standard selected-width budget is nonnegative. -/
theorem standardSelectedWidthBudget_nonneg
    {Feature : Type u} [Fintype Feature]
    (lambda : Real) (T : Nat) (L2 : Real) :
    0 <= standardSelectedWidthBudget
      (Feature := Feature) lambda T L2 := by
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/--
Pointwise canonical successor bonus bound. The full action prefix through
`horizon` is charged to the selected-width theorem, while the gap sum only
uses successor rounds `1, ..., horizon`.
-/
theorem
    canonicalHistoryTrajectory_sum_range_succ_radius_mul_width_le_standard
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (trajectory : Nat -> Fin K × Real)
    (hwidth : forall t, t < horizon + 1 ->
      confidenceWidth
          (finiteHorizonScalarGram lambda
            (canonicalHistoryTrajectoryFeature actionFeature)
            t trajectory)
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction trajectory t)) <= 1) :
    (Finset.range horizon).sum (fun n =>
        2 *
          finiteHorizonScalarConfidenceRadius
            (canonicalHistoryTrajectoryFeature actionFeature)
            R (delta / ((horizon + 1 : Nat) : Real))
            lambda S (n + 1) trajectory *
          confidenceWidth
            (finiteHorizonScalarGram lambda
              (canonicalHistoryTrajectoryFeature actionFeature)
              (n + 1) trajectory)
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) <=
      standardScalarRadiusWidthBound
        (Feature := Feature)
        R (delta / ((horizon + 1 : Nat) : Real))
        lambda S (horizon + 1) L2 := by
  let selectedAction : Nat -> Fin K :=
    fun t => Thompson.canonicalHistoryTrajectoryAction trajectory t
  let widthAt : Nat -> Real := fun t =>
    confidenceWidth
      (finiteHorizonScalarGram lambda
        (canonicalHistoryTrajectoryFeature actionFeature) t trajectory)
      (actionFeature (selectedAction t))
  let beta :=
    standardScalarConfidenceRadiusUpper
      (Feature := Feature)
      R (delta / ((horizon + 1 : Nat) : Real))
      lambda S (horizon + 1) L2
  let widthBudget :=
    standardSelectedWidthBudget
      (Feature := Feature) lambda (horizon + 1) L2
  have hdelta_local :
      0 < delta / ((horizon + 1 : Nat) : Real) := by
    exact div_pos hdelta (by positivity)
  have hfeatureBound : forall t, t < horizon + 1 ->
      dotProduct
          (canonicalHistoryTrajectoryFeature actionFeature t trajectory)
          (canonicalHistoryTrajectoryFeature actionFeature t trajectory) <=
        L2 := by
    intro t _ht
    exact hactionFeatureBound
      (Thompson.canonicalHistoryTrajectoryAction trajectory t)
  have hradius : forall n, n < horizon ->
      finiteHorizonScalarConfidenceRadius
          (canonicalHistoryTrajectoryFeature actionFeature)
          R (delta / ((horizon + 1 : Nat) : Real))
          lambda S (n + 1) trajectory <= beta := by
    intro n hn
    exact finiteHorizonScalarConfidenceRadius_le_standardUpper
      lambda hlambda
      (canonicalHistoryTrajectoryFeature actionFeature)
      R (delta / ((horizon + 1 : Nat) : Real)) S
      trajectory (n + 1) (horizon + 1)
      (Nat.succ_le_succ (Nat.le_of_lt hn))
      L2 hL2 hfeatureBound hdelta_local
  have hbeta : 0 <= beta :=
    standardScalarConfidenceRadiusUpper_nonneg
      (Feature := Feature)
      R (delta / ((horizon + 1 : Nat) : Real))
      lambda S (horizon + 1) L2 hS
  have hwidth_nonneg : forall t, 0 <= widthAt t := by
    intro t
    exact Real.sqrt_nonneg _
  have hselectedWidth :
      (Finset.range (horizon + 1)).sum widthAt <= widthBudget := by
    simpa only [selectedAction, widthAt, widthBudget,
      finiteHorizonScalarGram_eq_regularizedPrefixFeatureGram,
      canonicalHistoryTrajectoryFeature] using
      (sum_range_selectedAction_confidenceWidth_le_sqrt_mul_sqrt_log_of_width_le_one
        lambda hlambda actionFeature selectedAction
        (horizon + 1) L2 hL2
        (fun t _ht => hactionFeatureBound (selectedAction t))
        (fun t ht => by
          simpa only [selectedAction, widthAt,
            finiteHorizonScalarGram_eq_regularizedPrefixFeatureGram,
            canonicalHistoryTrajectoryFeature] using hwidth t ht))
  have hsuccessorWidth :
      (Finset.range horizon).sum (fun n => widthAt (n + 1)) <=
        (Finset.range (horizon + 1)).sum widthAt := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (hwidth_nonneg 0)
  have hsum :
      (Finset.range horizon).sum (fun n =>
          2 *
            finiteHorizonScalarConfidenceRadius
              (canonicalHistoryTrajectoryFeature actionFeature)
              R (delta / ((horizon + 1 : Nat) : Real))
              lambda S (n + 1) trajectory *
            widthAt (n + 1)) <=
        (Finset.range horizon).sum (fun n =>
          2 * beta * widthAt (n + 1)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (hradius n (Finset.mem_range.mp hn)) (by norm_num))
      (hwidth_nonneg (n + 1))
  calc
    (Finset.range horizon).sum (fun n =>
        2 *
          finiteHorizonScalarConfidenceRadius
            (canonicalHistoryTrajectoryFeature actionFeature)
            R (delta / ((horizon + 1 : Nat) : Real))
            lambda S (n + 1) trajectory *
          confidenceWidth
            (finiteHorizonScalarGram lambda
              (canonicalHistoryTrajectoryFeature actionFeature)
              (n + 1) trajectory)
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) =
        (Finset.range horizon).sum (fun n =>
          2 *
            finiteHorizonScalarConfidenceRadius
              (canonicalHistoryTrajectoryFeature actionFeature)
              R (delta / ((horizon + 1 : Nat) : Real))
              lambda S (n + 1) trajectory *
            widthAt (n + 1)) := by
      rfl
    _ <= (Finset.range horizon).sum (fun n =>
        2 * beta * widthAt (n + 1)) := hsum
    _ = 2 * beta *
        (Finset.range horizon).sum (fun n => widthAt (n + 1)) := by
      rw [Finset.mul_sum]
    _ <= 2 * beta * (Finset.range (horizon + 1)).sum widthAt := by
      exact mul_le_mul_of_nonneg_left hsuccessorWidth
        (mul_nonneg (by norm_num) hbeta)
    _ <= 2 * beta * widthBudget := by
      exact mul_le_mul_of_nonneg_left hselectedWidth
        (mul_nonneg (by norm_num) hbeta)
    _ = standardScalarRadiusWidthBound
        (Feature := Feature)
        R (delta / ((horizon + 1 : Nat) : Real))
        lambda S (horizon + 1) L2 := by
      rfl

/--
Violation of the deterministic standard radius-times-width successor-gap
budget. The fixed initial gap is still excluded.
-/
def canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (horizon : Nat) (L2 : Real)
    (comparator : Nat -> Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory |
    standardScalarRadiusWidthBound
        (Feature := Feature)
        R (delta / ((horizon + 1 : Nat) : Real))
        lambda S (horizon + 1) L2 <
      (Finset.range horizon).sum (fun n =>
        linearValue thetaStar (actionFeature (comparator (n + 1))) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1))))}

/--
The deterministic-budget violation event is contained in the compiled random
radius-times-width violation event.
-/
theorem
    canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet_subset
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (comparator : Nat -> Fin K)
    (hwidth : forall trajectory t, t < horizon + 1 ->
      confidenceWidth
          (finiteHorizonScalarGram lambda
            (canonicalHistoryTrajectoryFeature actionFeature)
            t trajectory)
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction trajectory t)) <= 1) :
    canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet
        lambda thetaStar actionFeature R delta S horizon L2 comparator <=
      canonicalHistoryTrajectorySumRangeSuccGapViolationSet
        lambda thetaStar actionFeature R delta S horizon comparator := by
  intro trajectory hviolation
  have hbonus :=
    canonicalHistoryTrajectory_sum_range_succ_radius_mul_width_le_standard
      lambda hlambda actionFeature R delta S hdelta hS
      horizon L2 hL2 hactionFeatureBound trajectory
      (hwidth trajectory)
  change
    (Finset.range horizon).sum (fun n =>
        2 *
          finiteHorizonScalarConfidenceRadius
            (canonicalHistoryTrajectoryFeature actionFeature)
            R (delta / ((horizon + 1 : Nat) : Real))
            lambda S (n + 1) trajectory *
          confidenceWidth
            (finiteHorizonScalarGram lambda
              (canonicalHistoryTrajectoryFeature actionFeature)
              (n + 1) trajectory)
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) <
      (Finset.range horizon).sum (fun n =>
        linearValue thetaStar (actionFeature (comparator (n + 1))) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1))))
  change
    standardScalarRadiusWidthBound
        (Feature := Feature)
        R (delta / ((horizon + 1 : Nat) : Real))
        lambda S (horizon + 1) L2 <
      (Finset.range horizon).sum (fun n =>
        linearValue thetaStar (actionFeature (comparator (n + 1))) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) at hviolation
  exact lt_of_le_of_lt hbonus hviolation

/--
Concrete high-probability successor-gap theorem with a deterministic standard
radius-times-width budget under the linear-sub-Gaussian environment law.
-/
theorem
    measure_canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet_le_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (comparator : Nat -> Fin K)
    (hwidth : forall trajectory t, t < horizon + 1 ->
      confidenceWidth
          (finiteHorizonScalarGram lambda
            (canonicalHistoryTrajectoryFeature actionFeature)
            t trajectory)
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction trajectory t)) <= 1)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet
          lambda thetaStar actionFeature R delta S horizon L2 comparator) <=
      ENNReal.ofReal delta := by
  calc
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet
          lambda thetaStar actionFeature R delta S horizon L2 comparator) <=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapViolationSet
          lambda thetaStar actionFeature R delta S horizon comparator) := by
      exact measure_mono
        (canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet_subset
          lambda hlambda thetaStar actionFeature R delta S hdelta hS
          horizon L2 hL2 hactionFeatureBound comparator hwidth)
    _ <= ENNReal.ofReal delta :=
      measure_canonicalHistoryTrajectorySumRangeSuccGapViolationSet_le_of_linearSubgaussianEnvironment
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S environment horizon comparator source

end OFUL
end BanditRLProof
