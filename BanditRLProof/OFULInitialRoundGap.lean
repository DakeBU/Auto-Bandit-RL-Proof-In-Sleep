import BanditRLProof.OFULNormalizedRadiusWidth

/-!
# Initial-round accounting for the canonical OFUL trajectory

This module bounds the fixed time-zero linear gap by the parameter and feature
norm envelopes, then adds that deterministic charge to the compiled normalized
successor-gap tail.
-/

namespace BanditRLProof.OFUL

open MeasureTheory Real Matrix
open scoped MatrixOrder

universe u

/-- Ordinary finite-dimensional Cauchy--Schwarz on the local linear-value surface. -/
theorem abs_linearValue_le_euclideanLength_mul_euclideanLength
    {Feature : Type u} [Fintype Feature]
    (theta x : Feature -> Real) :
    |linearValue theta x| <= euclideanLength theta * euclideanLength x := by
  have hupper :
      linearValue theta x <=
        euclideanLength theta * euclideanLength x := by
    have h :=
      Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset Feature) theta x
    simpa [linearValue, euclideanLength, dotProduct, pow_two] using h
  have hnegative :
      -linearValue theta x <=
        euclideanLength theta * euclideanLength x := by
    have h :=
      Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset Feature) (fun i => -theta i) x
    simpa [linearValue, euclideanLength, dotProduct, pow_two] using h
  exact abs_le.2 ⟨by linarith, hupper⟩

/-- A common parameter/feature envelope bounds the absolute linear value. -/
theorem abs_linearValue_le_parameterFeatureBound
    {Feature : Type u} [Fintype Feature]
    (theta x : Feature -> Real)
    (S L2 : Real) (hS : 0 <= S)
    (htheta : euclideanLength theta <= S)
    (hx : dotProduct x x <= L2) :
    |linearValue theta x| <= S * Real.sqrt L2 := by
  have hxLength : euclideanLength x <= Real.sqrt L2 := by
    exact Real.sqrt_le_sqrt hx
  exact
    (abs_linearValue_le_euclideanLength_mul_euclideanLength theta x).trans
      (mul_le_mul htheta hxLength (Real.sqrt_nonneg _) hS)

/-- Two arms sharing the same feature envelope differ by at most `2*S*sqrt L2`. -/
theorem linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
    {Feature : Type u} [Fintype Feature]
    (theta x y : Feature -> Real)
    (S L2 : Real) (hS : 0 <= S)
    (htheta : euclideanLength theta <= S)
    (hx : dotProduct x x <= L2)
    (hy : dotProduct y y <= L2) :
    linearValue theta x - linearValue theta y <=
      2 * S * Real.sqrt L2 := by
  have hxAbs :=
    abs_linearValue_le_parameterFeatureBound theta x S L2 hS htheta hx
  have hyAbs :=
    abs_linearValue_le_parameterFeatureBound theta y S L2 hS htheta hy
  have hxUpper := (abs_le.mp hxAbs).2
  have hyLower := (abs_le.mp hyAbs).1
  linarith

/-- Deterministic charge used for the canonical time-zero arm. -/
noncomputable def standardScalarInitialGapBound (S L2 : Real) : Real :=
  2 * S * Real.sqrt L2

/--
The canonical OFUL initial action is the fixed arm `0` almost surely, so its
linear gap to any comparator is bounded by the common parameter/feature
envelope.
-/
theorem canonicalHistoryTrajectory_initialGap_le_ae
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R algorithmDelta S : Real) (hS : 0 <= S)
    (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (comparator : Fin K)
    (htheta : euclideanLength thetaStar <= S) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R algorithmDelta S)
          environment,
      linearValue thetaStar (actionFeature comparator) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory 0)) <=
        standardScalarInitialGapBound S L2 := by
  filter_upwards [
    canonicalHistoryTrajectory_action_zero_ae_eq_initialArm
      hK lambda actionFeature R algorithmDelta S environment] with
    trajectory haction
  rw [haction]
  exact
    linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
      thetaStar (actionFeature comparator) (actionFeature ⟨0, hK⟩)
      S L2 hS htheta
      (hactionFeatureBound comparator)
      (hactionFeatureBound ⟨0, hK⟩)

/-- Standard finite-window cumulative-gap budget including time zero. -/
noncomputable def standardScalarAllRoundGapBound
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  standardScalarInitialGapBound S L2 +
    standardScalarRadiusWidthBound
      (Feature := Feature)
      R (delta / ((horizon + 1 : Nat) : Real))
      lambda S (horizon + 1) L2

/-- Violation of the standard OFUL cumulative-gap budget over rounds `0, ..., horizon`. -/
noncomputable def canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
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
    standardScalarAllRoundGapBound
        (Feature := Feature) R delta lambda S horizon L2 <
      (Finset.range (horizon + 1)).sum (fun t =>
        linearValue thetaStar (actionFeature (comparator t)) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory t)))}

/--
Almost surely, an all-round violation implies the previously compiled
successor-only standard-budget violation.
-/
theorem
    canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet_ae_le_succ
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (comparator : Nat -> Fin K)
    (htheta : euclideanLength thetaStar <= S) :
    ∀ᵐ trajectory ∂
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment,
      trajectory ∈
          canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
            lambda thetaStar actionFeature R delta S horizon L2 comparator ->
        trajectory ∈
          canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet
            lambda thetaStar actionFeature R delta S horizon L2 comparator := by
  filter_upwards [
    canonicalHistoryTrajectory_initialGap_le_ae
      hK lambda thetaStar actionFeature R
      (delta / ((horizon + 1 : Nat) : Real)) S hS L2
      hactionFeatureBound environment (comparator 0) htheta] with
    trajectory hinitial
  intro hall
  change
    standardScalarAllRoundGapBound
        (Feature := Feature) R delta lambda S horizon L2 <
      (Finset.range (horizon + 1)).sum (fun t =>
        linearValue thetaStar (actionFeature (comparator t)) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory t))) at hall
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
                trajectory (n + 1))))
  rw [Finset.sum_range_succ'] at hall
  unfold standardScalarAllRoundGapBound at hall
  linarith

/--
Concrete high-probability standard cumulative-gap theorem over all rounds
`0, ..., horizon`, with automatic normalized width discharge.
-/
theorem
    measure_canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (hL2lambda : L2 <= lambda)
    (comparator : Nat -> Fin K)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
          lambda thetaStar actionFeature R delta S horizon L2 comparator) <=
      ENNReal.ofReal delta := by
  calc
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
          lambda thetaStar actionFeature R delta S horizon L2 comparator) <=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R
            (delta / ((horizon + 1 : Nat) : Real)) S)
        environment
        (canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet
          lambda thetaStar actionFeature R delta S horizon L2 comparator) := by
      exact measure_mono_ae
        (canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet_ae_le_succ
          hK lambda thetaStar actionFeature R delta S hS environment
          horizon L2 hactionFeatureBound comparator source.theta_norm_le)
    _ <= ENNReal.ofReal delta :=
      measure_canonicalHistoryTrajectorySumRangeSuccGapStandardViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment horizon L2 hL2
        hactionFeatureBound hL2lambda comparator source

end BanditRLProof.OFUL
