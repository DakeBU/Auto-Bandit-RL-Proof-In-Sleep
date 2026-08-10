import BanditRLProof.ConcentrationQuadraticScheduled
import BanditRLProof.ConcentrationConfidenceSchedule
import BanditRLProof.Exp3RealizedPredictableVarianceTail

/-!
# All-time realized EXP3 predictable-variance tail

This module gives every positive prefix of one fixed generated EXP3 process a
geometric confidence share. The resulting countable union is controlled by
one outer confidence budget. This is countable outer-measure subadditivity,
not a Ville/Doob, mixture, optional-stopping, self-normalized, or general
Freedman theorem.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Exp3

universe u v

/-- The selected-loss predictable-variance radius at prefix `n+1` under the
geometric confidence schedule. -/
noncomputable def sampledRealizedPredictableVarianceGeometricRadius
    (varianceBudget : Nat -> Real) (delta : Real) (n : Nat) : Real :=
  sampledRealizedPredictableVarianceRadius (varianceBudget n)
    (Concentration.geometricConfidenceShare delta n)

/-- Countable failure event over every positive prefix of one generated EXP3
trajectory. -/
noncomputable def sampledPredictableRealizedDeviationAllTimeFailureSet
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action)
    (varianceBudget : Nat -> Real) (delta : Real) :
    Set (Env × ((k : Nat) -> Action × Real)) :=
  ⋃ n, {sample |
      sampledRealizedPredictableVarianceGeometricRadius
            varianceBudget delta n <=
          (Finset.range (n + 1)).sum (fun i =>
            sampledTrajectoryRealizedDeviationAt
              arms eta gamma loss i sample) ∧
        (Finset.range (n + 1)).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) <= varianceBudget n}

/-- Membership is failure at at least one positive prefix. -/
theorem mem_sampledPredictableRealizedDeviationAllTimeFailureSet_iff
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action)
    (varianceBudget : Nat -> Real) (delta : Real)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sample ∈ sampledPredictableRealizedDeviationAllTimeFailureSet
        arms eta gamma loss varianceBudget delta ↔
      ∃ n,
        sampledRealizedPredictableVarianceGeometricRadius
              varianceBudget delta n <=
            (Finset.range (n + 1)).sum (fun i =>
              sampledTrajectoryRealizedDeviationAt
                arms eta gamma loss i sample) ∧
          (Finset.range (n + 1)).sum (fun i =>
            sampledTrajectoryPredictableRealizedVarianceAt
              arms eta gamma loss i sample) <= varianceBudget n := by
  simp [sampledPredictableRealizedDeviationAllTimeFailureSet]

/-- On one generated EXP3 trajectory law, the joint
deviation/predictable-variance failures over all positive prefixes have total
mass at most the outer confidence budget. -/
theorem measure_sampledPredictableRealizedDeviationAllTimeFailureSet_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (varianceBudget : Nat -> Real)
    (hvarianceBudget : forall n, 0 < varianceBudget n)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu (sampledPredictableRealizedDeviationAllTimeFailureSet
        arms eta gamma loss varianceBudget delta) <=
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let deviation := fun n sample =>
    (Finset.range (n + 1)).sum (fun i =>
      sampledTrajectoryRealizedDeviationAt arms eta gamma loss i sample)
  let predictableVariance := fun n sample =>
    (Finset.range (n + 1)).sum (fun i =>
      sampledTrajectoryPredictableRealizedVarianceAt
        arms eta gamma loss i sample)
  let varianceScale : Nat -> Real := fun _ => 1
  let tiltCap : Nat -> Real := fun _ => 1
  let deltaAt := Concentration.geometricConfidenceShare delta
  have htail :=
    Concentration.measure_iUnion_scheduled_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
      mu deviation predictableVariance varianceScale varianceBudget tiltCap
        deltaAt delta
        (fun _ => by simp [varianceScale])
        hvarianceBudget
        (fun _ => by simp [tiltCap])
        (fun n => by
          exact Concentration.geometricConfidenceShare_pos hdelta n)
        (by
          intro n tilt htilt_nonneg htilt_le
          simpa [mu, deviation, predictableVariance, varianceScale, tiltCap,
            deltaAt] using
            (sampledPredictableRealizedDeviation_sum_tail_predictableVariance_fixedTilt
              prior arms harms eta gamma hgamma_pos hgamma_le_one loss (n + 1)
                tilt htilt_nonneg htilt_le
                (Concentration.quadraticFixedMGFScheduledRadius
                  varianceScale varianceBudget tiltCap deltaAt n)
                (varianceBudget n)))
        (by
          simpa [deltaAt] using
            (Concentration.tsum_ofReal_geometricConfidenceShare hdelta.le).le)
  simpa [mu, deviation, predictableVariance, varianceScale, tiltCap, deltaAt,
    sampledPredictableRealizedDeviationAllTimeFailureSet,
    sampledRealizedPredictableVarianceGeometricRadius,
    sampledRealizedPredictableVarianceRadius,
    Concentration.quadraticFixedMGFScheduledRadius,
    Concentration.quadraticFixedMGFRadius] using htail

end Exp3
end BanditRLProof
