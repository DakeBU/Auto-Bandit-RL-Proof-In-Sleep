import BanditRLProof.OFULExpectedRegret

/-!
# Explicit finite-window OFUL expected pseudo-regret rate

This module normalizes the horizon-tuned confidence parameter used by the
canonical OFUL expected-regret theorem and exposes its logarithmic
square-root bound without hiding the rate inside the radius-width definitions.
-/

namespace BanditRLProof.OFUL

open MeasureTheory Real Matrix

universe u

/--
The log budget in the horizon-tuned expected-regret radius: the standard
log-determinant term plus the `4 * log (T+1)` confidence contribution.
-/
noncomputable def standardExpectedRegretLogBudget
    {Feature : Type u} [Fintype Feature]
    (lambda : Real) (horizon : Nat) (L2 : Real) : Real :=
  standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2 +
    4 * Real.log (((horizon + 1 : Nat) : Real))

/--
The outer failure budget `1/(T+1)`, divided once more by the uniform-time
schedule size, is exactly the algorithm parameter `1/(T+1)^2`.
-/
theorem standardExpectedRegretAlgorithmDelta_eq_inv_sq
    (horizon : Nat) :
    standardExpectedRegretDelta horizon /
        (((horizon + 1 : Nat) : Real)) =
      1 / (((horizon + 1 : Nat) : Real) ^ 2) := by
  unfold standardExpectedRegretDelta
  ring

/--
At the canonical horizon-tuned algorithm parameter, the standard confidence
radius has the explicit form
`R * sqrt (B_T + 4 * log (T+1)) + sqrt lambda * S`.
-/
theorem standardScalarConfidenceRadiusUpper_standardExpectedRegret
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 < R)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    standardScalarConfidenceRadiusUpper
        (Feature := Feature) R
        (standardExpectedRegretDelta horizon /
          (((horizon + 1 : Nat) : Real)))
        lambda S (horizon + 1) L2 =
      R * Real.sqrt
          (standardExpectedRegretLogBudget
            (Feature := Feature) lambda horizon L2) +
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
  have hlogn : 0 <= Real.log n := Real.log_nonneg hn_one
  have hX : 0 <= B + 4 * Real.log n := by positivity
  have hdelta :
      standardExpectedRegretDelta horizon / n = 1 / n ^ 2 := by
    dsimp [n]
    exact standardExpectedRegretAlgorithmDelta_eq_inv_sq horizon
  have hlog :
      Real.log (Real.sqrt (Real.exp B) /
          (standardExpectedRegretDelta horizon / n)) =
        B / 2 + 2 * Real.log n := by
    rw [hdelta]
    have hquot :
        Real.sqrt (Real.exp B) / (1 / n ^ 2) =
          Real.sqrt (Real.exp B) * n ^ 2 := by
      field_simp
    rw [hquot]
    rw [Real.log_mul (Real.sqrt_pos.2 (Real.exp_pos B)).ne'
      (pow_ne_zero 2 hn_pos.ne')]
    rw [Real.log_sqrt (Real.exp_pos B).le, Real.log_exp, Real.log_pow]
    ring
  unfold standardScalarConfidenceRadiusUpper
  change Real.sqrt
        (2 * R ^ 2 *
          Real.log
            (Real.sqrt (Real.exp B) /
              (standardExpectedRegretDelta horizon / n))) +
      Real.sqrt lambda * S =
    R * Real.sqrt (B + 4 * Real.log n) + Real.sqrt lambda * S
  rw [hlog]
  congr 1
  have hrad :
      2 * R ^ 2 * (B / 2 + 2 * Real.log n) =
        R ^ 2 * (B + 4 * Real.log n) := by ring
  rw [hrad, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]

/-- Explicit logarithmic square-root bound for expected OFUL pseudo-regret. -/
noncomputable def standardExpectedPseudoRegretBound
    {Feature : Type u} [Fintype Feature]
    (R lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  4 * S * Real.sqrt L2 +
    2 *
      (R * Real.sqrt
          (standardExpectedRegretLogBudget
            (Feature := Feature) lambda horizon L2) +
        Real.sqrt lambda * S) *
      (Real.sqrt (((horizon + 1 : Nat) : Real)) *
        Real.sqrt
          (2 *
            standardScalarLogDetBudget
              (Feature := Feature) lambda (horizon + 1) L2))

/-- The prior named expected bound is exactly the explicit rate expression. -/
theorem standardScalarAllRoundGapBound_add_initial_eq_standardExpectedPseudoRegretBound
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 < R)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    standardScalarAllRoundGapBound
        (Feature := Feature) R (standardExpectedRegretDelta horizon)
          lambda S horizon L2 +
        standardScalarInitialGapBound S L2 =
      standardExpectedPseudoRegretBound
        (Feature := Feature) R lambda S horizon L2 := by
  unfold standardScalarAllRoundGapBound standardScalarRadiusWidthBound
    standardSelectedWidthBudget standardExpectedPseudoRegretBound
    standardScalarInitialGapBound
  rw [standardScalarConfidenceRadiusUpper_standardExpectedRegret
    (Feature := Feature) R hR lambda hlambda S horizon L2 hL2]
  ring

/--
Explicit finite-window expected pseudo-regret theorem for the canonical
scalar-ridge OFUL trajectory. The algorithm parameter is displayed directly
as `1/(T+1)^2`, and the upper bound is the logarithmic square-root expression
`standardExpectedPseudoRegretBound`.
-/
theorem
    integral_canonicalHistoryTrajectoryPseudoRegret_nonneg_and_le_explicitStandardExpectedBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    let algorithmDelta :=
      1 / (((horizon + 1 : Nat) : Real) ^ 2)
    let expectedPseudoRegret :=
      integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R algorithmDelta S)
          environment)
        (canonicalHistoryTrajectorySumRangeAllGap
          thetaStar actionFeature horizon (fun _t => best))
    0 <= expectedPseudoRegret ∧
      expectedPseudoRegret <=
        standardExpectedPseudoRegretBound
          (Feature := Feature) R lambda S horizon L2 := by
  dsimp only
  have h :=
    integral_canonicalHistoryTrajectoryPseudoRegret_nonneg_and_le_standardExpectedBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      S hS environment horizon L2 hL2 hactionFeatureBound hL2lambda
      best hbest source
  dsimp only at h
  rw [standardExpectedRegretAlgorithmDelta_eq_inv_sq,
    standardScalarAllRoundGapBound_add_initial_eq_standardExpectedPseudoRegretBound
      (Feature := Feature) R hR lambda hlambda S horizon L2 hL2] at h
  exact h

end BanditRLProof.OFUL
