import BanditRLProof.OFULScheduledAllTimeConfidence
import BanditRLProof.OFULNormalizedRadiusWidth

/-!
# Scheduled canonical all-horizon OFUL cumulative gap

This module combines the one-policy all-time scheduled confidence event with a
deterministic varying-budget radius-width envelope. The terminal event
quantifies over every finite horizon but is absorbed by the same all-time
confidence failure event.
-/

open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal NNReal ProbabilityTheory MatrixOrder

universe u

namespace BanditRLProof
namespace OFUL

/-- The telescoping confidence schedule is antitone in its time index. -/
theorem allTimeTelescopingDelta_antitone
    {delta : Real} (hdelta : 0 <= delta)
    {n T : Nat} (hnT : n <= T) :
    allTimeTelescopingDelta delta T <=
      allTimeTelescopingDelta delta n := by
  unfold allTimeTelescopingDelta allTimeTelescopingWeight
  apply mul_le_mul_of_nonneg_left _ hdelta
  apply one_div_le_one_div_of_le (by positivity)
  have hfirst :
      (((n + 1 : Nat) : Real)) <= (((T + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.add_le_add_right hnT 1
  have hsecond :
      (((n + 2 : Nat) : Real)) <= (((T + 2 : Nat) : Real)) := by
    exact_mod_cast Nat.add_le_add_right hnT 2
  exact mul_le_mul hfirst hsecond (by positivity) (by positivity)

/--
For fixed determinant budget, the standard confidence-radius upper bound is
antitone in the positive confidence level.
-/
theorem standardScalarConfidenceRadiusUpper_antitone_delta
    {Feature : Type u} [Fintype Feature]
    (R lambda S : Real) (T : Nat) (L2 : Real)
    {deltaSmall deltaLarge : Real}
    (hdeltaSmall : 0 < deltaSmall)
    (hdelta : deltaSmall <= deltaLarge) :
    standardScalarConfidenceRadiusUpper
        (Feature := Feature) R deltaLarge lambda S T L2 <=
      standardScalarConfidenceRadiusUpper
        (Feature := Feature) R deltaSmall lambda S T L2 := by
  have hdeltaLarge : 0 < deltaLarge :=
    hdeltaSmall.trans_le hdelta
  have hnum_nonneg :
      0 <=
        Real.sqrt
          (Real.exp
            (standardScalarLogDetBudget
              (Feature := Feature) lambda T L2)) :=
    Real.sqrt_nonneg _
  have hnum_pos :
      0 <
        Real.sqrt
          (Real.exp
            (standardScalarLogDetBudget
              (Feature := Feature) lambda T L2)) :=
    Real.sqrt_pos.2 (Real.exp_pos _)
  have hfrac :
      Real.sqrt
            (Real.exp
              (standardScalarLogDetBudget
                (Feature := Feature) lambda T L2)) /
          deltaLarge <=
        Real.sqrt
            (Real.exp
              (standardScalarLogDetBudget
                (Feature := Feature) lambda T L2)) /
          deltaSmall :=
    div_le_div_of_nonneg_left hnum_nonneg hdeltaSmall hdelta
  have hlog :
      Real.log
          (Real.sqrt
              (Real.exp
                (standardScalarLogDetBudget
                  (Feature := Feature) lambda T L2)) /
            deltaLarge) <=
        Real.log
          (Real.sqrt
              (Real.exp
                (standardScalarLogDetBudget
                  (Feature := Feature) lambda T L2)) /
            deltaSmall) :=
    Real.log_le_log (div_pos hnum_pos hdeltaLarge) hfrac
  have hinside :
      2 * R ^ 2 *
          Real.log
            (Real.sqrt
                (Real.exp
                  (standardScalarLogDetBudget
                    (Feature := Feature) lambda T L2)) /
              deltaLarge) <=
        2 * R ^ 2 *
          Real.log
            (Real.sqrt
                (Real.exp
                  (standardScalarLogDetBudget
                    (Feature := Feature) lambda T L2)) /
              deltaSmall) :=
    mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (by norm_num) (sq_nonneg R))
  have hsqrt := Real.sqrt_le_sqrt hinside
  simpa only [standardScalarConfidenceRadiusUpper, add_comm] using
    add_le_add_right hsqrt (Real.sqrt lambda * S)

/--
Every prefix radius using the varying telescoping schedule is bounded by one
standard radius using separate terminal schedule and Gram-matrix budgets.
-/
theorem
    finiteHorizonScalarConfidenceRadius_telescoping_le_standardUpper_of_indices
    {Omega Feature : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (feature : Nat -> Omega -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta)
    (omega : Omega) (n scheduleT gramT : Nat)
    (hnSchedule : n <= scheduleT) (hnGram : n <= gramT)
    (L2 : Real) (hL2 : 0 <= L2)
    (hbound : forall t, t < gramT ->
      dotProduct (feature t omega) (feature t omega) <= L2) :
    finiteHorizonScalarConfidenceRadius
        feature R (allTimeTelescopingDelta delta n)
        lambda S n omega <=
      standardScalarConfidenceRadiusUpper
        (Feature := Feature)
        R (allTimeTelescopingDelta delta scheduleT)
        lambda S gramT L2 := by
  calc
    finiteHorizonScalarConfidenceRadius
        feature R (allTimeTelescopingDelta delta n)
        lambda S n omega <=
      standardScalarConfidenceRadiusUpper
        (Feature := Feature)
        R (allTimeTelescopingDelta delta n)
        lambda S gramT L2 := by
      exact finiteHorizonScalarConfidenceRadius_le_standardUpper
        lambda hlambda feature R
        (allTimeTelescopingDelta delta n) S
        omega n gramT hnGram L2 hL2 hbound
        (allTimeTelescopingDelta_pos hdelta n)
    _ <=
      standardScalarConfidenceRadiusUpper
        (Feature := Feature)
        R (allTimeTelescopingDelta delta scheduleT)
        lambda S gramT L2 := by
      exact standardScalarConfidenceRadiusUpper_antitone_delta
        (Feature := Feature) R lambda S gramT L2
        (allTimeTelescopingDelta_pos hdelta scheduleT)
        (allTimeTelescopingDelta_antitone hdelta.le hnSchedule)

/--
Every prefix radius using the varying telescoping schedule is bounded by one
standard radius using the same terminal index for both budgets.
-/
theorem
    finiteHorizonScalarConfidenceRadius_telescoping_le_standardUpper
    {Omega Feature : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (feature : Nat -> Omega -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta)
    (omega : Omega) (n T : Nat) (hnT : n <= T)
    (L2 : Real) (hL2 : 0 <= L2)
    (hbound : forall t, t < T ->
      dotProduct (feature t omega) (feature t omega) <= L2) :
    finiteHorizonScalarConfidenceRadius
        feature R (allTimeTelescopingDelta delta n)
        lambda S n omega <=
      standardScalarConfidenceRadiusUpper
        (Feature := Feature)
        R (allTimeTelescopingDelta delta T)
        lambda S T L2 := by
  exact
    finiteHorizonScalarConfidenceRadius_telescoping_le_standardUpper_of_indices
      lambda hlambda feature R delta S hdelta omega n T T hnT hnT
      L2 hL2 hbound

/-- Standard varying-budget radius-width envelope at a finite horizon. -/
noncomputable def telescopingStandardScalarRadiusWidthBound
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  standardScalarRadiusWidthBound
    (Feature := Feature)
    R (allTimeTelescopingDelta delta horizon)
    lambda S (horizon + 1) L2

/--
The scheduled successor bonuses up to a fixed horizon obey one deterministic
terminal radius-times-width budget.
-/
theorem
    canonicalHistoryTrajectory_sum_range_succ_telescoping_radius_mul_width_le_standard
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
            R (allTimeTelescopingDelta delta (n + 1))
            lambda S (n + 1) trajectory *
          confidenceWidth
            (finiteHorizonScalarGram lambda
              (canonicalHistoryTrajectoryFeature actionFeature)
              (n + 1) trajectory)
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) <=
      telescopingStandardScalarRadiusWidthBound
        (Feature := Feature) R delta lambda S horizon L2 := by
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
      R (allTimeTelescopingDelta delta horizon)
      lambda S (horizon + 1) L2
  let widthBudget :=
    standardSelectedWidthBudget
      (Feature := Feature) lambda (horizon + 1) L2
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
          R (allTimeTelescopingDelta delta (n + 1))
          lambda S (n + 1) trajectory <= beta := by
    intro n hn
    exact
      finiteHorizonScalarConfidenceRadius_telescoping_le_standardUpper_of_indices
        lambda hlambda
        (canonicalHistoryTrajectoryFeature actionFeature)
        R delta S hdelta trajectory
        (n + 1) horizon (horizon + 1)
        (Nat.succ_le_iff.2 hn)
        (Nat.succ_le_succ (Nat.le_of_lt hn))
        L2 hL2 hfeatureBound
  have hbeta : 0 <= beta :=
    standardScalarConfidenceRadiusUpper_nonneg
      (Feature := Feature)
      R (allTimeTelescopingDelta delta horizon)
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
              R (allTimeTelescopingDelta delta (n + 1))
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
            R (allTimeTelescopingDelta delta (n + 1))
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
              R (allTimeTelescopingDelta delta (n + 1))
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
    _ = telescopingStandardScalarRadiusWidthBound
        (Feature := Feature) R delta lambda S horizon L2 := by
      rfl

/--
The explicit feature normalization `L2 <= lambda` discharges every scheduled
selected-width premise.
-/
theorem
    canonicalHistoryTrajectory_sum_range_succ_telescoping_radius_mul_width_le_standard_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (trajectory : Nat -> Fin K × Real) :
    (Finset.range horizon).sum (fun n =>
        2 *
          finiteHorizonScalarConfidenceRadius
            (canonicalHistoryTrajectoryFeature actionFeature)
            R (allTimeTelescopingDelta delta (n + 1))
            lambda S (n + 1) trajectory *
          confidenceWidth
            (finiteHorizonScalarGram lambda
              (canonicalHistoryTrajectoryFeature actionFeature)
              (n + 1) trajectory)
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1)))) <=
      telescopingStandardScalarRadiusWidthBound
        (Feature := Feature) R delta lambda S horizon L2 := by
  exact
    canonicalHistoryTrajectory_sum_range_succ_telescoping_radius_mul_width_le_standard
      lambda hlambda actionFeature R delta S hdelta hS
      horizon L2 hL2 hactionFeatureBound trajectory
      (fun t _ht =>
        canonicalHistoryTrajectory_confidenceWidth_le_one
          lambda hlambda actionFeature L2 hactionFeatureBound hL2lambda
          trajectory t)

/--
Outside the single all-time confidence failure event, every fixed-horizon
successor-gap sum is bounded by its scheduled radius-times-width sum.
-/
theorem
    telescopingCanonicalHistoryTrajectory_sum_range_succ_gap_le_radius_mul_width_ae
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (comparator : Nat -> Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        (Finset.range horizon).sum (fun n =>
            linearValue thetaStar
                (actionFeature (comparator (n + 1))) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1)))) <=
          (Finset.range horizon).sum (fun n =>
            2 *
              finiteHorizonScalarConfidenceRadius
                (canonicalHistoryTrajectoryFeature actionFeature)
                R (allTimeTelescopingDelta delta (n + 1))
                lambda S (n + 1) trajectory *
              confidenceWidth
                (finiteHorizonScalarGram lambda
                  (canonicalHistoryTrajectoryFeature actionFeature)
                  (n + 1) trajectory)
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1)))) := by
  have hall :
      ∀ᵐ trajectory ∂
          Thompson.canonicalHistoryTrajectoryMeasure
            (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
              hK lambda actionFeature R delta S)
            environment,
        ∀ n,
          trajectory ∉
              scalarRidgeConfidenceFailureAt
                lambda thetaStar S
                (canonicalHistoryTrajectoryFeature actionFeature)
                canonicalHistoryTrajectoryResponse R
                (allTimeTelescopingDelta delta (n + 1)) (n + 1) ->
            linearValue thetaStar
                (actionFeature (comparator (n + 1))) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1))) <=
              2 *
                finiteHorizonScalarConfidenceRadius
                  (canonicalHistoryTrajectoryFeature actionFeature)
                  R (allTimeTelescopingDelta delta (n + 1))
                  lambda S (n + 1) trajectory *
                confidenceWidth
                  (finiteHorizonScalarGram lambda
                    (canonicalHistoryTrajectoryFeature actionFeature)
                    (n + 1) trajectory)
                  (actionFeature
                    (Thompson.canonicalHistoryTrajectoryAction
                      trajectory (n + 1))) := by
    rw [ae_all_iff]
    intro n
    exact
      telescopingCanonicalHistoryTrajectory_action_succ_gap_le_of_not_mem_confidenceFailure
        hK lambda hlambda thetaStar actionFeature R delta S
        environment n (comparator (n + 1))
  filter_upwards [hall] with trajectory htrajectory
  intro hgood
  apply Finset.sum_le_sum
  intro n hn
  apply htrajectory n
  intro hfailure
  apply hgood
  unfold allTimeTelescopingScalarRidgeConfidenceFailureSet
  exact
    (mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff
      lambda thetaStar S
      (canonicalHistoryTrajectoryFeature actionFeature)
      canonicalHistoryTrajectoryResponse R
      (allTimeTelescopingDelta delta) trajectory).2
      ⟨n + 1, hfailure⟩

/--
The normalized feature contract turns the scheduled fixed-horizon gap sum into
the deterministic terminal standard budget on the same all-time good event.
-/
theorem
    telescopingCanonicalHistoryTrajectory_sum_range_succ_gap_le_standard_ae_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (comparator : Nat -> Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        (Finset.range horizon).sum (fun n =>
            linearValue thetaStar
                (actionFeature (comparator (n + 1))) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1)))) <=
          telescopingStandardScalarRadiusWidthBound
            (Feature := Feature) R delta lambda S horizon L2 := by
  filter_upwards [
    telescopingCanonicalHistoryTrajectory_sum_range_succ_gap_le_radius_mul_width_ae
      hK lambda hlambda thetaStar actionFeature R delta S
      environment horizon comparator] with trajectory hgap
  intro hgood
  exact (hgap hgood).trans
    (canonicalHistoryTrajectory_sum_range_succ_telescoping_radius_mul_width_le_standard_of_featureBound_le_regularization
      lambda hlambda actionFeature R delta S hdelta hS
      horizon L2 hL2 hactionFeatureBound hL2lambda trajectory)

/--
There exists a finite horizon whose cumulative successor gap exceeds the
corresponding scheduled deterministic terminal budget.
-/
def telescopingCanonicalHistoryTrajectoryAllHorizonSuccGapStandardViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (comparator : Nat -> Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory | ∃ horizon,
    telescopingStandardScalarRadiusWidthBound
        (Feature := Feature) R delta lambda S horizon L2 <
      (Finset.range horizon).sum (fun n =>
        linearValue thetaStar
            (actionFeature (comparator (n + 1))) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction
                trajectory (n + 1))))}

/--
Any all-horizon cumulative successor-gap violation forces the one-policy
all-time confidence failure event almost surely.
-/
theorem
    telescopingCanonicalHistoryTrajectoryAllHorizonSuccGapStandardViolationSet_subset_confidenceFailure_ae
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (comparator : Nat -> Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment,
      trajectory ∈
          telescopingCanonicalHistoryTrajectoryAllHorizonSuccGapStandardViolationSet
            lambda thetaStar actionFeature R delta S L2 comparator ->
        trajectory ∈
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta := by
  have hall :
      ∀ᵐ trajectory ∂
          Thompson.canonicalHistoryTrajectoryMeasure
            (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
              hK lambda actionFeature R delta S)
            environment,
        ∀ horizon,
          trajectory ∉
              allTimeTelescopingScalarRidgeConfidenceFailureSet
                lambda thetaStar S
                (canonicalHistoryTrajectoryFeature actionFeature)
                canonicalHistoryTrajectoryResponse R delta ->
            (Finset.range horizon).sum (fun n =>
                linearValue thetaStar
                    (actionFeature (comparator (n + 1))) -
                  linearValue thetaStar
                    (actionFeature
                      (Thompson.canonicalHistoryTrajectoryAction
                        trajectory (n + 1)))) <=
              telescopingStandardScalarRadiusWidthBound
                (Feature := Feature) R delta lambda S horizon L2 := by
    rw [ae_all_iff]
    intro horizon
    exact
      telescopingCanonicalHistoryTrajectory_sum_range_succ_gap_le_standard_ae_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R delta S hdelta hS
        environment horizon L2 hL2 hactionFeatureBound hL2lambda comparator
  filter_upwards [hall] with trajectory htrajectory
  rintro ⟨horizon, hviolation⟩
  by_contra hgood
  exact (not_lt_of_ge (htrajectory horizon hgood)) hviolation

/--
For the one telescoping-schedule generated policy, the probability that any
finite-horizon cumulative successor gap exceeds its scheduled deterministic
standard budget is at most `delta`.
-/
theorem
    measure_telescopingCanonicalHistoryTrajectoryAllHorizonSuccGapStandardViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (comparator : Nat -> Fin K)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalHistoryTrajectoryAllHorizonSuccGapStandardViolationSet
          lambda thetaStar actionFeature R delta S L2 comparator) <=
      ENNReal.ofReal delta := by
  calc
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalHistoryTrajectoryAllHorizonSuccGapStandardViolationSet
          lambda thetaStar actionFeature R delta S L2 comparator) <=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) := by
      exact measure_mono_ae
        (telescopingCanonicalHistoryTrajectoryAllHorizonSuccGapStandardViolationSet_subset_confidenceFailure_ae
          hK lambda hlambda thetaStar actionFeature R delta S hdelta hS
          environment L2 hL2 hactionFeatureBound hL2lambda comparator)
    _ <= ENNReal.ofReal delta := by
      exact
        measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment
          hK lambda hlambda thetaStar actionFeature R hR
          delta hdelta hdelta_one S environment source

end OFUL
end BanditRLProof
