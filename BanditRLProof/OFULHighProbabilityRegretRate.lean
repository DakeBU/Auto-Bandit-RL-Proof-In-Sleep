import BanditRLProof.OFULExpectedRegret

/-!
# Explicit finite-window high-probability OFUL pseudo-regret rate

This module expands the named all-round OFUL gap budget into an explicit
logarithmic radius-width expression and specializes the compiled cumulative-gap
tail to a certified optimal fixed arm.
-/

namespace BanditRLProof.OFUL

open MeasureTheory Real Matrix
open scoped ENNReal

universe u

/--
The confidence logarithm for outer failure probability `delta` over the
complete finite window `0, ..., horizon`.
-/
noncomputable def standardHighProbabilityRegretLogBudget
    {Feature : Type u} [Fintype Feature]
    (lambda delta : Real) (horizon : Nat) (L2 : Real) : Real :=
  standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2 +
    2 * Real.log ((((horizon + 1 : Nat) : Real)) / delta)

/--
At algorithm parameter `delta / (T+1)`, the standard confidence radius has
the explicit form
`R * sqrt (B_T + 2 * log ((T+1)/delta)) + sqrt lambda * S`.
-/
theorem standardScalarConfidenceRadiusUpper_highProbabilityRegret
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    standardScalarConfidenceRadiusUpper
        (Feature := Feature) R
        (delta / (((horizon + 1 : Nat) : Real)))
        lambda S (horizon + 1) L2 =
      R * Real.sqrt
          (standardHighProbabilityRegretLogBudget
            (Feature := Feature) lambda delta horizon L2) +
        Real.sqrt lambda * S := by
  let n : Real := (((horizon + 1 : Nat) : Real))
  let B : Real :=
    standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2
  have hn_pos : 0 < n := by
    dsimp [n]
    positivity
  have hn_one : 1 <= n := by
    dsimp [n]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
  have hB : 0 <= B := by
    exact standardScalarLogDetBudget_nonneg
      (Feature := Feature) lambda hlambda (horizon + 1) L2 hL2
  have hscale_pos : 0 < n / delta := div_pos hn_pos hdelta
  have hscale_one : 1 <= n / delta := by
    rw [le_div_iff₀ hdelta]
    simpa using hdelta_one.trans hn_one
  have hlogscale : 0 <= Real.log (n / delta) :=
    Real.log_nonneg hscale_one
  have hX : 0 <= B + 2 * Real.log (n / delta) := by positivity
  have hquot :
      Real.sqrt (Real.exp B) / (delta / n) =
        Real.sqrt (Real.exp B) * (n / delta) := by
    field_simp
  have hlog :
      Real.log (Real.sqrt (Real.exp B) / (delta / n)) =
        B / 2 + Real.log (n / delta) := by
    rw [hquot]
    rw [Real.log_mul (Real.sqrt_pos.2 (Real.exp_pos B)).ne'
      hscale_pos.ne']
    rw [Real.log_sqrt (Real.exp_pos B).le, Real.log_exp]
  unfold standardScalarConfidenceRadiusUpper
    standardHighProbabilityRegretLogBudget
  change
    Real.sqrt
          (2 * R ^ 2 *
            Real.log (Real.sqrt (Real.exp B) / (delta / n))) +
        Real.sqrt lambda * S =
      R * Real.sqrt (B + 2 * Real.log (n / delta)) +
        Real.sqrt lambda * S
  rw [hlog]
  congr 1
  have hrad :
      2 * R ^ 2 * (B / 2 + Real.log (n / delta)) =
        R ^ 2 * (B + 2 * Real.log (n / delta)) := by ring
  rw [hrad, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]

/-- Explicit complete finite-window high-probability pseudo-regret budget. -/
noncomputable def standardHighProbabilityPseudoRegretBound
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  2 * S * Real.sqrt L2 +
    2 *
      (R * Real.sqrt
          (standardHighProbabilityRegretLogBudget
            (Feature := Feature) lambda delta horizon L2) +
        Real.sqrt lambda * S) *
      (Real.sqrt (((horizon + 1 : Nat) : Real)) *
        Real.sqrt
          (2 *
            standardScalarLogDetBudget
              (Feature := Feature) lambda (horizon + 1) L2))

/-- The named all-round gap budget is exactly the explicit rate expression. -/
theorem standardScalarAllRoundGapBound_eq_standardHighProbabilityPseudoRegretBound
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    standardScalarAllRoundGapBound
        (Feature := Feature) R delta lambda S horizon L2 =
      standardHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 := by
  unfold standardScalarAllRoundGapBound standardScalarRadiusWidthBound
    standardSelectedWidthBudget standardHighProbabilityPseudoRegretBound
    standardScalarInitialGapBound
  rw [standardScalarConfidenceRadiusUpper_highProbabilityRegret
    (Feature := Feature) R hR delta hdelta hdelta_one
      lambda hlambda S horizon L2 hL2]

/-- Complete fixed-optimal-arm pseudo-regret along one canonical trajectory. -/
noncomputable def canonicalStandardHighProbabilityPseudoRegret
    {K : Nat} {Feature : Type u} [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K) (horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  canonicalHistoryTrajectorySumRangeAllGap
    thetaStar actionFeature horizon (fun _t => best) trajectory

/--
Explicit finite-window high-probability pseudo-regret theorem for the canonical
scalar-ridge OFUL trajectory.

The horizon-`T` algorithm is run at `delta / (T+1)`. The result controls the
complete rounds `0, ..., T`; it is not an anytime or all-horizon statement.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_nonneg_and_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    let algorithmDelta :=
      delta / (((horizon + 1 : Nat) : Real))
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R algorithmDelta S)
        environment
    let pseudoRegret :=
      canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon
    (forall trajectory, 0 <= pseudoRegret trajectory) /\
      mu {trajectory |
          standardHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2 <
            pseudoRegret trajectory} <=
        ENNReal.ofReal delta := by
  dsimp only
  constructor
  · intro trajectory
    exact
      canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
        thetaStar actionFeature horizon best hbest trajectory
  · have htail :=
      measure_canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment horizon L2 hL2
        hactionFeatureBound hL2lambda (fun _t => best) source
    have hbound :=
      standardScalarAllRoundGapBound_eq_standardHighProbabilityPseudoRegretBound
        (Feature := Feature) R hR delta hdelta hdelta_one
          lambda hlambda S horizon L2 hL2
    rw [← hbound]
    change
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R
              (delta / (((horizon + 1 : Nat) : Real))) S)
          environment
          (canonicalHistoryTrajectorySumRangeAllGapStandardViolationSet
            lambda thetaStar actionFeature R delta S horizon L2
              (fun _t => best)) <=
        ENNReal.ofReal delta
    exact htail

end BanditRLProof.OFUL
