import BanditRLProof.Exp3RealizedPredictableVarianceAllTime

/-!
# Generated EXP3 realized-deviation confidence over all positive prefixes

This module discharges the variance-good conjunct in the geometric all-time
tail with the deterministic unit bound on each exact selected-loss predictable
variance. The process parameters remain fixed outside the countable index.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

/-- Deterministic selected-loss predictable-variance budget at prefix `n+1`. -/
noncomputable def sampledRealizedPredictableVarianceLinearBudget
    (n : Nat) : Real :=
  ((n + 1 : Nat) : Real)

theorem sampledRealizedPredictableVarianceLinearBudget_pos (n : Nat) :
    0 < sampledRealizedPredictableVarianceLinearBudget n := by
  unfold sampledRealizedPredictableVarianceLinearBudget
  positivity

/-- Geometric-share deviation radius with deterministic variance budget
`n+1`. -/
noncomputable def sampledRealizedDeviationGeometricAllTimeRadius
    (delta : Real) (n : Nat) : Real :=
  sampledRealizedPredictableVarianceGeometricRadius
    sampledRealizedPredictableVarianceLinearBudget delta n

/-- Pure realized-deviation failure event over every positive prefix of one
generated EXP3 trajectory. -/
noncomputable def sampledRealizedDeviationGeometricAllTimeFailureSet
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (delta : Real) :
    Set (Env × ((k : Nat) → Action × Real)) :=
  ⋃ n, {sample |
    sampledRealizedDeviationGeometricAllTimeRadius delta n ≤
      (Finset.range (n + 1)).sum (fun i =>
        sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample)}

theorem mem_sampledRealizedDeviationGeometricAllTimeFailureSet_iff
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (delta : Real)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sample ∈ sampledRealizedDeviationGeometricAllTimeFailureSet
        arms eta gamma loss delta ↔
      ∃ n,
        sampledRealizedDeviationGeometricAllTimeRadius delta n ≤
          (Finset.range (n + 1)).sum (fun i =>
            sampledTrajectoryRealizedDeviationAt
              arms eta gamma loss i sample) := by
  simp [sampledRealizedDeviationGeometricAllTimeFailureSet]

/-- With the deterministic budget `n+1`, the prior joint failure event is
exactly the pure realized-deviation crossing event. -/
theorem sampledPredictableRealizedDeviationAllTimeFailureSet_linearBudget_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (delta : Real) :
    sampledPredictableRealizedDeviationAllTimeFailureSet
        arms eta gamma loss sampledRealizedPredictableVarianceLinearBudget
          delta =
      sampledRealizedDeviationGeometricAllTimeFailureSet
        arms eta gamma loss delta := by
  ext sample
  rw [mem_sampledPredictableRealizedDeviationAllTimeFailureSet_iff,
    mem_sampledRealizedDeviationGeometricAllTimeFailureSet_iff]
  constructor
  · rintro ⟨n, hdeviation, _hvariance⟩
    exact ⟨n, by
      simpa [sampledRealizedDeviationGeometricAllTimeRadius] using hdeviation⟩
  · rintro ⟨n, hdeviation⟩
    refine ⟨n, ?_, ?_⟩
    · simpa [sampledRealizedDeviationGeometricAllTimeRadius] using hdeviation
    · simpa [sampledRealizedPredictableVarianceLinearBudget] using
        (sampledPredictableRealizedVariance_sum_le_horizon
          arms harms eta gamma hgamma_nonneg hgamma_le_one loss (n + 1)
            sample)

/-- On one fixed generated EXP3 trajectory law, the realized selected-loss
deviation stays below its geometric-share quadratic radius at every positive
prefix outside a set of mass at most the outer confidence budget. -/
theorem measure_sampledRealizedDeviationGeometricAllTimeFailureSet_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu (sampledRealizedDeviationGeometricAllTimeFailureSet
        arms eta gamma loss delta) ≤ ENNReal.ofReal delta := by
  dsimp only
  have htail :=
    measure_sampledPredictableRealizedDeviationAllTimeFailureSet_le
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss
        sampledRealizedPredictableVarianceLinearBudget
        sampledRealizedPredictableVarianceLinearBudget_pos delta hdelta
  dsimp only at htail
  rw [sampledPredictableRealizedDeviationAllTimeFailureSet_linearBudget_eq
    arms harms eta gamma hgamma_pos.le hgamma_le_one loss delta] at htail
  exact htail

end BanditRLProof.Exp3
