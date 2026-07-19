import BanditRLProof.ConcentrationQuadraticMaximal
import BanditRLProof.Exp3RealizedPredictableVarianceTail

/-!
# Finite-prefix realized EXP3 predictable-variance tail

This module applies the finite maximal quadratic fixed-MGF route to every
positive prefix of the generated realized-loss deviation process.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Equal-share radius for indices `t < horizon`, hence prefix lengths
`1` through `horizon` inclusive. -/
noncomputable def sampledRealizedPredictableVarianceMaximalRadius
    (horizon : Nat) (varianceBudget delta : Real) : Real :=
  Concentration.quadraticFixedMGFMaximalRadius (Finset.range horizon)
    1 varianceBudget 1 delta

/-- Finite maximal predictable-variance tail for the realized selected-loss
deviation over every positive prefix of the generated EXP3 trajectory. -/
theorem sampledPredictableRealizedDeviation_prefix_max_tail_predictableVariance_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu (⋃ t ∈ Finset.range horizon, {sample |
        sampledRealizedPredictableVarianceMaximalRadius
              horizon varianceBudget delta <=
            (Finset.range (t + 1)).sum (fun i =>
              sampledTrajectoryRealizedDeviationAt
                arms eta gamma loss i sample) ∧
          (Finset.range (t + 1)).sum (fun i =>
            sampledTrajectoryPredictableRealizedVarianceAt
              arms eta gamma loss i sample) <= varianceBudget}) <=
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let times := Finset.range horizon
  let deviation := fun t sample =>
    (Finset.range (t + 1)).sum (fun i =>
      sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample)
  let predictableVariance := fun t sample =>
    (Finset.range (t + 1)).sum (fun i =>
      sampledTrajectoryPredictableRealizedVarianceAt
        arms eta gamma loss i sample)
  have htimes : times.Nonempty := by
    refine ⟨0, ?_⟩
    exact Finset.mem_range.mpr hhorizon
  have hmax :=
    Concentration.measure_biUnion_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
      mu times htimes deviation predictableVariance 1 varianceBudget 1 delta
        (by norm_num) hvarianceBudget (by norm_num) hdelta (by
          intro t ht tilt htilt_nonneg htilt_le_one
          simpa [mu, times, deviation, predictableVariance] using
            (sampledPredictableRealizedDeviation_sum_tail_predictableVariance_fixedTilt
              prior arms harms eta gamma hgamma_pos hgamma_le_one loss (t + 1)
                tilt htilt_nonneg htilt_le_one
                (Concentration.quadraticFixedMGFMaximalRadius
                  times 1 varianceBudget 1 delta) varianceBudget))
  simpa [mu, times, deviation, predictableVariance,
    sampledRealizedPredictableVarianceMaximalRadius] using hmax

end BanditRLProof.Exp3
