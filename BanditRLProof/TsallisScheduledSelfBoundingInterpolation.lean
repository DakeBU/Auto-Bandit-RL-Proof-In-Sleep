import BanditRLProof.TsallisScheduledSuboptimalExpectedBound

/-!
# Scheduled self-bounding interpolation for half-Tsallis FTRL

This module formalizes the lambda interpolation step used before the joint
probability/simplex optimization in self-bounding Tsallis-INF analyses. It
combines an upper regret estimate with a terminal self-bounding inequality;
no prefix self-bounding assumption is required.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Algebraic lambda interpolation between an upper regret bound and a
terminal self-bounding lower estimate. -/
theorem regret_le_selfBoundingInterpolation
    (regret upper gapMass corruption lambda : Real)
    (hlambda : lambda ∈ Set.Icc (0 : Real) 1)
    (hupper : regret ≤ upper)
    (hselfBounding : gapMass - corruption ≤ regret) :
    regret ≤
      (1 + lambda) * upper - lambda * gapMass + lambda * corruption := by
  have hscaleUpper :
      (1 + lambda) * regret ≤ (1 + lambda) * upper :=
    mul_le_mul_of_nonneg_left hupper (by linarith [hlambda.1])
  have hscaleSelfBounding :
      lambda * (gapMass - corruption) ≤ lambda * regret :=
    mul_le_mul_of_nonneg_left hselfBounding hlambda.1
  calc
    regret = (1 + lambda) * regret - lambda * regret := by ring
    _ ≤ (1 + lambda) * upper - lambda * (gapMass - corruption) :=
      sub_le_sub hscaleUpper hscaleSelfBounding
    _ = (1 + lambda) * upper - lambda * gapMass + lambda * corruption := by
      ring

/-- The generated scheduled half-Tsallis upper estimate and a terminal
self-bounding constraint imply the paper-facing lambda-interpolated bound.
The remaining route is a finite-dimensional optimization over the expected
action probabilities and `lambda`; kernel, integral, and Jensen obligations
have already been discharged here. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_selfBoundingInterpolation
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat → Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (heta : ∀ t, t ≤ horizon → 0 < eta t)
    (heta_le : ∀ t, t ≤ horizon → eta t ≤ 1 / 2)
    (hetaMono : ∀ t, t < horizon → eta (t + 1) ≤ eta t)
    (gap : Action → Real) (corruption lambda : Real)
    (hlambda : lambda ∈ Set.Icc (0 : Real) 1)
    (hselfBounding :
      let selector :=
        canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
          arms harms eta loss
      let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector.finiteHistory loss.environment
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) - corruption ≤
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss (pointMass best) horizon)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    let upper :=
      (Finset.range (horizon + 1)).sum (fun t =>
        2 * eta t * (arms.erase best).sum (fun action =>
          Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) + 2 * (eta t) ^ 2) +
      halfTsallisPotentialMass arms
          (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
        1 / eta horizon
    let gapMass :=
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action))
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) ≤
      (1 + lambda) * upper - lambda * gapMass + lambda * corruption := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let regret := integral mu
    (sampledScheduledHalfTsallisPredictableEnvironmentRegret
      arms harms eta loss (pointMass best) horizon)
  let upper :=
    (Finset.range (horizon + 1)).sum (fun t =>
      2 * eta t * (arms.erase best).sum (fun action =>
        Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action)) + 2 * (eta t) ^ 2) +
    halfTsallisPotentialMass arms
        (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
      1 / eta horizon
  let gapMass :=
    (Finset.range (horizon + 1)).sum (fun t =>
      (arms.erase best).sum (fun action =>
        gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action))
  have hupper : regret ≤ upper := by
    simpa [regret, upper, mu, selector] using
      (integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_suboptimalExpectedSqrt
        prior arms harms eta loss hbest horizon heta heta_le hetaMono)
  have hselfBounding' : gapMass - corruption ≤ regret := by
    simpa [gapMass, regret, mu, selector] using hselfBounding
  simpa [regret, upper, gapMass, mu, selector] using
    (regret_le_selfBoundingInterpolation
      regret upper gapMass corruption lambda hlambda hupper hselfBounding')

end Tsallis
end BanditRLProof
