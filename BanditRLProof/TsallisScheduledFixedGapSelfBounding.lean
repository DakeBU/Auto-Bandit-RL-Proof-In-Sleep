import BanditRLProof.TsallisScheduledSuboptimalExpectedBound

/-!
# Fixed-gap self-bounding for scheduled half-Tsallis FTRL

This module identifies generated scheduled predictable environment regret
with expected suboptimal-arm gap mass under an exact predictable fixed-gap
law.  It discharges the explicit self-bounding premise of the scheduled
completion-of-squares theorem.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Pathwise suboptimal-arm gap mass of the scheduled generated laws. -/
noncomputable def sampledScheduledHalfTsallisPredictableSuboptimalGapMass
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (best : Action) (gap : Action -> Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    (arms.erase best).sum (fun action =>
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action * gap action))

/-- An exact predictable fixed-gap law identifies scheduled environment
regret against the best-arm point mass with suboptimal-arm gap mass
pathwise. -/
theorem sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalGapMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (gap : Action -> Real)
    (horizon : Nat)
    (hgapLaw : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon sample =
      sampledScheduledHalfTsallisPredictableSuboptimalGapMass
        arms harms eta best gap horizon sample := by
  unfold sampledScheduledHalfTsallisPredictableEnvironmentRegret
    sampledScheduledHalfTsallisPredictableSuboptimalGapMass
  apply Finset.sum_congr rfl
  intro t _ht
  rw [linearLoss_sub_pointMass_eq_gapMass
    arms hbest
    (sampledScheduledHalfTsallisProbabilityAtTime arms harms eta t sample)
    (Exp3.predictableLossAt loss t sample) gap
    (finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample)
    (hgapLaw t sample)]
  rw [← Finset.sum_erase_add _ _ hbest]
  have hgapBest : gap best = 0 := by
    have h := hgapLaw t sample best hbest
    linarith
  simp [hgapBest]

/-- Integrating scheduled pathwise suboptimal gap mass gives the deterministic
time-by-arm sum of gaps times expected scheduled action probabilities. -/
theorem integral_sampledScheduledHalfTsallisPredictableSuboptimalGapMass_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (best : Action) (gap : Action -> Real) (horizon : Nat) :
    integral mu (sampledScheduledHalfTsallisPredictableSuboptimalGapMass
        arms harms eta best gap horizon) =
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) := by
  unfold sampledScheduledHalfTsallisPredictableSuboptimalGapMass
  rw [ExpectationBochnerSums.integral_finset_sum mu
    (Finset.range (horizon + 1))]
  · apply Finset.sum_congr rfl
    intro t _ht
    rw [ExpectationBochnerSums.integral_finset_sum mu (arms.erase best)]
    · apply Finset.sum_congr rfl
      intro action haction
      rw [integral_mul_const]
      unfold sampledScheduledHalfTsallisExpectedProbabilityAt
      ring
    · intro action haction
      exact
        (integrable_sampledScheduledHalfTsallisProbabilityAtTime
          mu arms harms eta t action (Finset.mem_of_mem_erase haction)).mul_const
          (gap action)
  · intro t _ht
    exact IntegrabilitySums.integrable_finset_sum mu (arms.erase best)
      (fun action sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample action * gap action)
      (fun action haction =>
        (integrable_sampledScheduledHalfTsallisProbabilityAtTime
          mu arms harms eta t action (Finset.mem_of_mem_erase haction)).mul_const
          (gap action))

/-- The exact predictable fixed-gap law identifies the integrated scheduled
environment regret with the expected suboptimal-arm gap mass. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalExpectedGapMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (gap : Action -> Real)
    (horizon : Nat)
    (hgapLaw : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) =
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) =
      integral mu (sampledScheduledHalfTsallisPredictableSuboptimalGapMass
        arms harms eta best gap horizon) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun sample =>
            sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalGapMass
              arms harms eta loss hbest gap horizon hgapLaw sample
    _ = (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) := by
          exact
            integral_sampledScheduledHalfTsallisPredictableSuboptimalGapMass_eq
              mu arms harms eta best gap horizon

/-- Any nonnegative corruption allowance turns the exact fixed-gap identity
into the explicit self-bounding inequality required by completion of
squares. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_fixedGap
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (gap : Action -> Real)
    (horizon : Nat)
    (hgapLaw : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action)
    (corruption : Real) (hcorruption : 0 <= corruption) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) - corruption <=
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) := by
  dsimp only
  have heq :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalExpectedGapMass
      prior arms harms eta loss hbest gap horizon hgapLaw
  dsimp only at heq
  linarith

/-- The generated scheduled regret bound with an explicit self-bounding
premise becomes automatic under an exact predictable fixed-gap law. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_of_fixedGap
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (heta : forall t, t <= horizon -> 0 < eta t)
    (heta_le : forall t, t <= horizon -> eta t <= 1 / 2)
    (hetaMono : forall t, t < horizon -> eta (t + 1) <= eta t)
    (gap : Action -> Real)
    (hgapPos : forall action, action ∈ arms.erase best -> 0 < gap action)
    (hgapLaw : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action)
    (corruption : Real) (hcorruption : 0 <= corruption) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) <=
      2 * ((Finset.range (horizon + 1)).sum (fun t =>
          2 * (eta t) ^ 2) +
        (halfTsallisPotentialMass arms
            (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
          1 / eta horizon)) +
        ((Finset.range (horizon + 1)).product (arms.erase best)).sum
          (fun index => (2 * eta index.1) ^ 2 / gap index.2) +
        corruption := by
  dsimp only
  apply
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_of_selfBounding
      prior arms harms eta loss hbest horizon heta heta_le hetaMono gap
        hgapPos corruption
  exact
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_fixedGap
      prior arms harms eta loss hbest gap horizon hgapLaw corruption hcorruption

end Tsallis
end BanditRLProof
