import BanditRLProof.OFULInitialRoundGap

/-!
# Expected finite-window gap for the canonical OFUL trajectory

This module turns the compiled all-round high-probability cumulative-gap tail
into a Bochner expected-gap bound. The bad event is charged by a deterministic
finite-window envelope obtained from the same parameter and arm norm bounds.
-/

namespace BanditRLProof.OFUL

open MeasureTheory Real Matrix Set

universe u

/-- The complete finite-window linear gap along one canonical trajectory. -/
noncomputable def canonicalHistoryTrajectorySumRangeAllGap
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (horizon : Nat)
    (comparator : Nat -> Fin K)
    (trajectory : Nat -> Fin K × Real) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    linearValue thetaStar (actionFeature (comparator t)) -
      linearValue thetaStar
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory t)))

/-- A fixed arm maximizes the true linear value over the finite action set. -/
def IsOptimalLinearArm
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K) : Prop :=
  forall action,
    linearValue thetaStar (actionFeature action) <=
      linearValue thetaStar (actionFeature best)

/-- Gap to an optimal fixed arm is pointwise nonnegative. -/
theorem canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (horizon : Nat)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (trajectory : Nat -> Fin K × Real) :
    0 <= canonicalHistoryTrajectorySumRangeAllGap
      thetaStar actionFeature horizon (fun _t => best) trajectory := by
  unfold canonicalHistoryTrajectorySumRangeAllGap
  exact Finset.sum_nonneg fun t _ht =>
    sub_nonneg.mpr
      (hbest (Thompson.canonicalHistoryTrajectoryAction trajectory t))

/-- The all-round cumulative linear gap is measurable on trajectory space. -/
theorem measurable_canonicalHistoryTrajectorySumRangeAllGap
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (horizon : Nat)
    (comparator : Nat -> Fin K) :
    Measurable
      (canonicalHistoryTrajectorySumRangeAllGap
        thetaStar actionFeature horizon comparator) := by
  unfold canonicalHistoryTrajectorySumRangeAllGap
  refine Finset.measurable_sum (Finset.range (horizon + 1)) fun t _ht => ?_
  exact measurable_const.sub
    ((measurable_of_countable (fun action : Fin K =>
      linearValue thetaStar (actionFeature action))).comp
        (Thompson.measurable_canonicalHistoryTrajectoryAction_apply t))

/--
The absolute linear-value difference between any two bounded arm features is
at most `2*S*sqrt L2`.
-/
theorem abs_linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
    {Feature : Type u} [Fintype Feature]
    (theta x y : Feature -> Real)
    (S L2 : Real) (hS : 0 <= S)
    (htheta : euclideanLength theta <= S)
    (hx : dotProduct x x <= L2)
    (hy : dotProduct y y <= L2) :
    |linearValue theta x - linearValue theta y| <=
      2 * S * Real.sqrt L2 := by
  have hxAbs :=
    abs_linearValue_le_parameterFeatureBound theta x S L2 hS htheta hx
  have hyAbs :=
    abs_linearValue_le_parameterFeatureBound theta y S L2 hS htheta hy
  rw [abs_le]
  constructor
  · have hxLower := (abs_le.mp hxAbs).1
    have hyUpper := (abs_le.mp hyAbs).2
    linarith
  · have hxUpper := (abs_le.mp hxAbs).2
    have hyLower := (abs_le.mp hyAbs).1
    linarith

/-- Uniform absolute envelope for the complete finite-window cumulative gap. -/
noncomputable def standardScalarAllRoundGapEnvelope
    (S : Real) (horizon : Nat) (L2 : Real) : Real :=
  ((horizon + 1 : Nat) : Real) * standardScalarInitialGapBound S L2

/-- Every trajectory satisfies the deterministic all-round gap envelope. -/
theorem abs_canonicalHistoryTrajectorySumRangeAllGap_le_envelope
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (S : Real) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (comparator : Nat -> Fin K)
    (htheta : euclideanLength thetaStar <= S)
    (trajectory : Nat -> Fin K × Real) :
    |canonicalHistoryTrajectorySumRangeAllGap
        thetaStar actionFeature horizon comparator trajectory| <=
      standardScalarAllRoundGapEnvelope S horizon L2 := by
  unfold canonicalHistoryTrajectorySumRangeAllGap
  calc
    |(Finset.range (horizon + 1)).sum (fun t =>
        linearValue thetaStar (actionFeature (comparator t)) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory t)))| <=
      (Finset.range (horizon + 1)).sum (fun t =>
        |linearValue thetaStar (actionFeature (comparator t)) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory t))|) :=
        Finset.abs_sum_le_sum_abs _ _
    _ <=
      (Finset.range (horizon + 1)).sum
        (fun _t => standardScalarInitialGapBound S L2) := by
      apply Finset.sum_le_sum
      intro t _ht
      exact
        abs_linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
          thetaStar
          (actionFeature (comparator t))
          (actionFeature
            (Thompson.canonicalHistoryTrajectoryAction trajectory t))
          S L2 hS htheta
          (hactionFeatureBound (comparator t))
          (hactionFeatureBound
            (Thompson.canonicalHistoryTrajectoryAction trajectory t))
    _ = standardScalarAllRoundGapEnvelope S horizon L2 := by
      simp [standardScalarAllRoundGapEnvelope, standardScalarInitialGapBound]

/-- The deterministic all-round gap envelope is nonnegative. -/
theorem standardScalarAllRoundGapEnvelope_nonneg
    (S : Real) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) :
    0 <= standardScalarAllRoundGapEnvelope S horizon L2 := by
  unfold standardScalarAllRoundGapEnvelope standardScalarInitialGapBound
  positivity

/-- The standard all-round high-probability budget is nonnegative. -/
theorem standardScalarAllRoundGapBound_nonneg
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) :
    0 <= standardScalarAllRoundGapBound
      (Feature := Feature) R delta lambda S horizon L2 := by
  unfold standardScalarAllRoundGapBound standardScalarInitialGapBound
    standardScalarRadiusWidthBound
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hS) (Real.sqrt_nonneg _))
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (standardScalarConfidenceRadiusUpper_nonneg
          (Feature := Feature) R
          (delta / ((horizon + 1 : Nat) : Real))
          lambda S (horizon + 1) L2 hS))
      (standardSelectedWidthBudget_nonneg
        (Feature := Feature) lambda (horizon + 1) L2))

/-- The complete finite-window cumulative gap is integrable under a finite measure. -/
theorem integrable_canonicalHistoryTrajectorySumRangeAllGap
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (mu : Measure (Nat -> Fin K × Real)) [IsFiniteMeasure mu]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (S : Real) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (comparator : Nat -> Fin K)
    (htheta : euclideanLength thetaStar <= S) :
    Integrable
      (canonicalHistoryTrajectorySumRangeAllGap
        thetaStar actionFeature horizon comparator) mu := by
  refine Integrable.of_bound
    (measurable_canonicalHistoryTrajectorySumRangeAllGap
      thetaStar actionFeature horizon comparator).aestronglyMeasurable
    (standardScalarAllRoundGapEnvelope S horizon L2) ?_
  exact Filter.Eventually.of_forall fun trajectory => by
    simpa [Real.norm_eq_abs] using
      abs_canonicalHistoryTrajectorySumRangeAllGap_le_envelope
        thetaStar actionFeature S hS horizon L2 hactionFeatureBound
        comparator htheta trajectory

/-- The named violation set is measurable. -/
theorem measurableSet_canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (horizon : Nat) (L2 : Real)
    (comparator : Nat -> Fin K) :
    MeasurableSet
      (canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
        lambda thetaStar actionFeature R delta S horizon L2 comparator) := by
  exact measurableSet_lt measurable_const
    (measurable_canonicalHistoryTrajectorySumRangeAllGap
      thetaStar actionFeature horizon comparator)

/--
Generic expectation assembly: the all-round gap is charged by the standard
budget off the violation set and by the deterministic envelope on it.
-/
theorem integral_canonicalHistoryTrajectorySumRangeAllGap_le_standard_add_envelope_mul_real_measure
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (mu : Measure (Nat -> Fin K × Real)) [IsProbabilityMeasure mu]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (comparator : Nat -> Fin K)
    (htheta : euclideanLength thetaStar <= S) :
    integral mu
        (canonicalHistoryTrajectorySumRangeAllGap
          thetaStar actionFeature horizon comparator) <=
      standardScalarAllRoundGapBound
          (Feature := Feature) R delta lambda S horizon L2 +
        standardScalarAllRoundGapEnvelope S horizon L2 *
          mu.real
            (canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
              lambda thetaStar actionFeature R delta S horizon L2
                comparator) := by
  let gap :=
    canonicalHistoryTrajectorySumRangeAllGap
      thetaStar actionFeature horizon comparator
  let budget :=
    standardScalarAllRoundGapBound
      (Feature := Feature) R delta lambda S horizon L2
  let envelope := standardScalarAllRoundGapEnvelope S horizon L2
  let bad :=
    canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
      lambda thetaStar actionFeature R delta S horizon L2 comparator
  let overflow : (Nat -> Fin K × Real) -> Real :=
    bad.indicator (fun _trajectory => envelope)
  have hbad : MeasurableSet bad := by
    exact
      measurableSet_canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
        lambda thetaStar actionFeature R delta S horizon L2 comparator
  have hgap : Integrable gap mu := by
    exact
      integrable_canonicalHistoryTrajectorySumRangeAllGap
        mu thetaStar actionFeature S hS horizon L2 hactionFeatureBound
          comparator htheta
  have hoverflow : Integrable overflow mu := by
    exact (integrable_const envelope).indicator hbad
  have hbudget : 0 <= budget := by
    exact
      standardScalarAllRoundGapBound_nonneg
        (Feature := Feature) R delta lambda S hS horizon L2
  have hpoint : forall trajectory, gap trajectory <= budget + overflow trajectory := by
    intro trajectory
    by_cases htrajectory : trajectory ∈ bad
    · have hgapEnvelope : gap trajectory <= envelope := by
        exact (le_abs_self _).trans
          (abs_canonicalHistoryTrajectorySumRangeAllGap_le_envelope
            thetaStar actionFeature S hS horizon L2 hactionFeatureBound
              comparator htheta trajectory)
      calc
        gap trajectory <= envelope := hgapEnvelope
        _ <= budget + envelope := le_add_of_nonneg_left hbudget
        _ = budget + overflow trajectory := by
          simp [overflow, Set.indicator_of_mem htrajectory]
    · have hgapBudget : gap trajectory <= budget := by
        apply le_of_not_gt
        simpa [bad, budget, gap,
          canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet,
          canonicalHistoryTrajectorySumRangeAllGap] using htrajectory
      calc
        gap trajectory <= budget := hgapBudget
        _ = budget + overflow trajectory := by
          simp [overflow, Set.indicator_of_notMem htrajectory]
  calc
    integral mu gap <=
        integral mu (fun trajectory => budget + overflow trajectory) := by
      exact integral_mono hgap ((integrable_const budget).add hoverflow) hpoint
    _ = budget + integral mu overflow := by
      rw [integral_add (integrable_const budget) hoverflow, integral_const]
      simp [MeasureTheory.probReal_univ]
    _ = budget + envelope * mu.real bad := by
      congr 1
      change integral mu (bad.indicator (fun _trajectory => envelope)) =
        envelope * mu.real bad
      rw [integral_indicator hbad, setIntegral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]

/--
Finite-window expected cumulative linear-gap theorem for the canonical OFUL
trajectory. The additive bad-event contribution is the deterministic
all-round envelope times `delta`.
-/
theorem
    integral_canonicalHistoryTrajectorySumRangeAllGap_le_standard_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R
              (delta / ((horizon + 1 : Nat) : Real)) S)
          environment)
        (canonicalHistoryTrajectorySumRangeAllGap
          thetaStar actionFeature horizon comparator) <=
      standardScalarAllRoundGapBound
          (Feature := Feature) R delta lambda S horizon L2 +
        standardScalarAllRoundGapEnvelope S horizon L2 * delta := by
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryScalarRidgeOptimisticAlgorithm
        hK lambda actionFeature R
          (delta / ((horizon + 1 : Nat) : Real)) S)
      environment
  let bad :=
    canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
      lambda thetaStar actionFeature R delta S horizon L2 comparator
  have htail : mu bad <= ENNReal.ofReal delta := by
    exact
      measure_canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment horizon L2 hL2
        hactionFeatureBound hL2lambda comparator source
  have htailReal : mu.real bad <= delta := by
    apply ENNReal.toReal_le_of_le_ofReal hdelta.le
    exact htail
  calc
    integral mu
        (canonicalHistoryTrajectorySumRangeAllGap
          thetaStar actionFeature horizon comparator) <=
      standardScalarAllRoundGapBound
          (Feature := Feature) R delta lambda S horizon L2 +
        standardScalarAllRoundGapEnvelope S horizon L2 * mu.real bad := by
      exact
        integral_canonicalHistoryTrajectorySumRangeAllGap_le_standard_add_envelope_mul_real_measure
          mu lambda thetaStar actionFeature R delta S hS horizon L2
          hactionFeatureBound comparator source.theta_norm_le
    _ <=
      standardScalarAllRoundGapBound
          (Feature := Feature) R delta lambda S horizon L2 +
        standardScalarAllRoundGapEnvelope S horizon L2 * delta := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left htailReal
          (standardScalarAllRoundGapEnvelope_nonneg S hS horizon L2))

/--
Fixed-comparator form of the expected cumulative linear-gap theorem, matching
the usual stochastic linear-bandit pseudo-regret surface.
-/
theorem
    integral_canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_le_standard_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (best : Fin K)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R
              (delta / ((horizon + 1 : Nat) : Real)) S)
          environment)
        (canonicalHistoryTrajectorySumRangeAllGap
          thetaStar actionFeature horizon (fun _t => best)) <=
      standardScalarAllRoundGapBound
          (Feature := Feature) R delta lambda S horizon L2 +
        standardScalarAllRoundGapEnvelope S horizon L2 * delta := by
  exact
    integral_canonicalHistoryTrajectorySumRangeAllGap_le_standard_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment horizon L2 hL2
      hactionFeatureBound hL2lambda (fun _t => best) source

/--
Expected finite-window OFUL pseudo-regret theorem for a certified optimal
fixed arm. The conjunction records both nonnegativity and the explicit upper
bound.
-/
theorem
    integral_canonicalHistoryTrajectoryPseudoRegret_nonneg_and_le_standard_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    let expectedPseudoRegret :=
      integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R
              (delta / ((horizon + 1 : Nat) : Real)) S)
          environment)
        (canonicalHistoryTrajectorySumRangeAllGap
          thetaStar actionFeature horizon (fun _t => best))
    0 <= expectedPseudoRegret ∧
      expectedPseudoRegret <=
        standardScalarAllRoundGapBound
            (Feature := Feature) R delta lambda S horizon L2 +
          standardScalarAllRoundGapEnvelope S horizon L2 * delta := by
  dsimp only
  constructor
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun trajectory =>
        canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
          thetaStar actionFeature horizon best hbest trajectory)
  · exact
      integral_canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_le_standard_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment horizon L2 hL2
        hactionFeatureBound hL2lambda best source

/-- Canonical horizon-tuned outer failure budget for expected regret. -/
noncomputable def standardExpectedRegretDelta (horizon : Nat) : Real :=
  1 / (((horizon + 1 : Nat) : Real))

theorem standardExpectedRegretDelta_pos (horizon : Nat) :
    0 < standardExpectedRegretDelta horizon := by
  unfold standardExpectedRegretDelta
  positivity

theorem standardExpectedRegretDelta_le_one (horizon : Nat) :
    standardExpectedRegretDelta horizon <= 1 := by
  have hdenom : (1 : Real) <= (((horizon + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
  unfold standardExpectedRegretDelta
  simpa using
    one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hdenom

/-- At `delta_T=1/(T+1)`, the bad-event envelope charge is one arm-gap envelope. -/
theorem standardScalarAllRoundGapEnvelope_mul_standardExpectedRegretDelta
    (S : Real) (horizon : Nat) (L2 : Real) :
    standardScalarAllRoundGapEnvelope S horizon L2 *
        standardExpectedRegretDelta horizon =
      standardScalarInitialGapBound S L2 := by
  unfold standardScalarAllRoundGapEnvelope standardExpectedRegretDelta
  have hpos : 0 < ((((horizon + 1 : Nat) : Real))) := by
    positivity
  have hne : ((((horizon + 1 : Nat) : Real))) ≠ 0 := ne_of_gt hpos
  field_simp

/--
Horizon-tuned finite-window expected OFUL pseudo-regret corollary obtained by
choosing the outer failure budget `delta_T=1/(T+1)`. The algorithm receives
the local parameter `delta_T/(T+1)=1/(T+1)^2`, and the bad-event expectation
contributes exactly one additional `2*S*sqrt L2` charge.
-/
theorem
    integral_canonicalHistoryTrajectoryPseudoRegret_nonneg_and_le_standardExpectedBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    let delta := standardExpectedRegretDelta horizon
    let expectedPseudoRegret :=
      integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R
              (delta / ((horizon + 1 : Nat) : Real)) S)
          environment)
        (canonicalHistoryTrajectorySumRangeAllGap
          thetaStar actionFeature horizon (fun _t => best))
    0 <= expectedPseudoRegret ∧
      expectedPseudoRegret <=
        standardScalarAllRoundGapBound
            (Feature := Feature) R delta lambda S horizon L2 +
          standardScalarInitialGapBound S L2 := by
  dsimp only
  have h :=
    integral_canonicalHistoryTrajectoryPseudoRegret_nonneg_and_le_standard_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      (standardExpectedRegretDelta horizon)
      (standardExpectedRegretDelta_pos horizon)
      (standardExpectedRegretDelta_le_one horizon)
      S hS environment horizon L2 hL2 hactionFeatureBound hL2lambda
      best hbest source
  rw [standardScalarAllRoundGapEnvelope_mul_standardExpectedRegretDelta] at h
  exact h

end BanditRLProof.OFUL
