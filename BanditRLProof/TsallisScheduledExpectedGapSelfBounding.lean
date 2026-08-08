import BanditRLProof.TsallisScheduledFixedGapSelfBounding

/-!
# Expected-gap self-bounding for scheduled half-Tsallis FTRL

This module replaces the samplewise fixed-gap premise by the stochastic
first-moment law actually needed by self-bounding.  For every time and
suboptimal arm, the probability-weighted predictable loss difference has
expectation `gap action * E[p_t(action)]`.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- The per-time, per-suboptimal-arm first-moment law needed by stochastic
self-bounding.  It is deliberately finer than the final summed regret law so
that later conditional-expectation producers can discharge it one coordinate
at a time. -/
def HasScheduledExpectedGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Action -> Real) (horizon : Nat) : Prop :=
  ∀ t, t <= horizon -> ∀ action, action ∈ arms.erase best ->
    integral mu (fun sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample action *
          (Exp3.predictableLossAt loss t sample action -
            Exp3.predictableLossAt loss t sample best)) =
      gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t action

/-- One probability-weighted predictable loss difference is integrable. -/
theorem integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (best action : Action) (haction : action ∈ arms) (t : Nat) :
    Integrable (fun sample =>
      sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample action *
        (Exp3.predictableLossAt loss t sample action -
          Exp3.predictableLossAt loss t sample best)) mu := by
  have hp := integrable_sampledScheduledHalfTsallisProbabilityAtTime
    mu arms harms eta t action haction
  have hdiffMeas :=
    (Exp3.measurable_predictableLossAt loss t action).sub
      (Exp3.measurable_predictableLossAt loss t best)
  refine hp.mul_bdd (c := 1) hdiffMeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun sample => by
    have hmem (candidate : Action) :
        Exp3.predictableLossAt loss t sample candidate ∈ Set.Icc (0 : Real) 1 := by
      cases t with
      | zero => exact loss.initial_mem_unitInterval sample.1 candidate
      | succ n =>
          exact loss.successor_mem_unitInterval n sample.1
            (Preorder.frestrictLe n sample.2) candidate
    have ha := hmem action
    have hb := hmem best
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Pathwise scheduled regret against a best-arm point mass is the finite sum
of probability-weighted predictable loss differences over suboptimal arms. -/
theorem sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_weightedLossGapMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon sample =
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          sampledScheduledHalfTsallisProbabilityAtTime
              arms harms eta t sample action *
            (Exp3.predictableLossAt loss t sample action -
              Exp3.predictableLossAt loss t sample best))) := by
  unfold sampledScheduledHalfTsallisPredictableEnvironmentRegret
  apply Finset.sum_congr rfl
  intro t _ht
  rw [linearLoss_sub_pointMass_eq_gapMass
    arms hbest
    (sampledScheduledHalfTsallisProbabilityAtTime arms harms eta t sample)
    (Exp3.predictableLossAt loss t sample)
    (fun action => Exp3.predictableLossAt loss t sample action -
      Exp3.predictableLossAt loss t sample best)
    (finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample)
    (fun _action _haction => rfl)]
  rw [← Finset.sum_erase_add _ _ hbest]
  simp

/-- A coordinatewise expected-gap law identifies integrated scheduled regret
with the expected suboptimal-arm gap mass. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalExpectedGapMass_of_expectedGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (gap : Action -> Real)
    (horizon : Nat)
    (hgapLaw : HasScheduledExpectedGapLaw
      mu arms harms eta loss best gap horizon) :
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) =
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun sample =>
    sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_weightedLossGapMass
      arms harms eta loss hbest horizon sample)]
  rw [ExpectationBochnerSums.integral_finset_sum mu
    (Finset.range (horizon + 1))]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [ExpectationBochnerSums.integral_finset_sum mu (arms.erase best)]
    · apply Finset.sum_congr rfl
      intro action haction
      exact hgapLaw t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
        action haction
    · intro action haction
      exact
        integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
          mu arms harms eta loss best action
            (Finset.mem_of_mem_erase haction) t
  · intro t _ht
    exact IntegrabilitySums.integrable_finset_sum mu (arms.erase best)
      (fun action sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample action *
          (Exp3.predictableLossAt loss t sample action -
            Exp3.predictableLossAt loss t sample best))
      (fun action haction =>
        integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
          mu arms harms eta loss best action
            (Finset.mem_of_mem_erase haction) t)

/-- A nonnegative corruption allowance turns the expected-gap identity into
the self-bounding premise consumed by completion of squares. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_expectedGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (gap : Action -> Real)
    (horizon : Nat)
    (hgapLaw : HasScheduledExpectedGapLaw
      mu arms harms eta loss best gap horizon)
    (corruption : Real) (hcorruption : 0 <= corruption) :
    (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) - corruption <=
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) := by
  have heq :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalExpectedGapMass_of_expectedGapLaw
      mu arms harms eta loss hbest gap horizon hgapLaw
  linarith

end Tsallis
end BanditRLProof
