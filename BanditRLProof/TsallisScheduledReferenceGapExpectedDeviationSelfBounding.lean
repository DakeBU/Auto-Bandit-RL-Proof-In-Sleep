import BanditRLProof.TsallisScheduledReferenceGapSelfBounding

/-!
# Expected-deviation self-bounding for predictable perturbations

This variant retains the scheduled action probability inside the corruption
allowance. A sample-dependent predictable deviation therefore contributes its
actual probability-weighted expectation instead of a deterministic pointwise
envelope.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- A reference expected-gap law plus an integrable sample-dependent
predictable perturbation yields a self-bound with the exact expected weighted
deviation allowance. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_referenceExpectedGapLaw_of_expectedDeviation
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (actualLoss referenceLoss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms)
    (baseGap : Action -> Real)
    (deviation : Nat ->
      (Env × ((k : Nat) -> Action × Real)) -> Action -> Real)
    (horizon : Nat)
    (hreferenceGapLaw : HasScheduledExpectedGapLaw
      mu arms harms eta referenceLoss best baseGap horizon)
    (hdeviation_integrable : forall t, t <= horizon -> forall action,
      action ∈ arms.erase best ->
      Integrable (fun sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample action *
          deviation t sample action) mu)
    (hdeviation : forall t, t <= horizon -> forall sample action,
      action ∈ arms.erase best ->
      |(Exp3.predictableLossAt actualLoss t sample action -
            Exp3.predictableLossAt actualLoss t sample best) -
          (Exp3.predictableLossAt referenceLoss t sample action -
            Exp3.predictableLossAt referenceLoss t sample best)| <=
        deviation t sample action) :
    (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) -
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          integral mu (fun sample =>
            sampledScheduledHalfTsallisProbabilityAtTime
                arms harms eta t sample action *
              deviation t sample action))) <=
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta actualLoss (pointMass best) horizon) := by
  have hactualIntegral :
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta actualLoss (pointMass best) horizon) =
        (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            integral mu (fun sample =>
              sampledScheduledHalfTsallisProbabilityAtTime
                  arms harms eta t sample action *
                (Exp3.predictableLossAt actualLoss t sample action -
                  Exp3.predictableLossAt actualLoss t sample best)))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun sample =>
      sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_weightedLossGapMass
        arms harms eta actualLoss hbest horizon sample)]
    rw [ExpectationBochnerSums.integral_finset_sum mu
      (Finset.range (horizon + 1))]
    · apply Finset.sum_congr rfl
      intro t _ht
      rw [ExpectationBochnerSums.integral_finset_sum mu (arms.erase best)]
      intro action haction
      exact
        integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
          mu arms harms eta actualLoss best action
            (Finset.mem_of_mem_erase haction) t
    · intro t _ht
      exact IntegrabilitySums.integrable_finset_sum mu (arms.erase best)
        (fun action sample =>
          sampledScheduledHalfTsallisProbabilityAtTime
              arms harms eta t sample action *
            (Exp3.predictableLossAt actualLoss t sample action -
              Exp3.predictableLossAt actualLoss t sample best))
        (fun action haction =>
          integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
            mu arms harms eta actualLoss best action
              (Finset.mem_of_mem_erase haction) t)
  have hcoordinate : forall t, t <= horizon -> forall action,
      action ∈ arms.erase best ->
      baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action -
        integral mu (fun sample =>
          sampledScheduledHalfTsallisProbabilityAtTime
              arms harms eta t sample action *
            deviation t sample action) <=
        integral mu (fun sample =>
          sampledScheduledHalfTsallisProbabilityAtTime
              arms harms eta t sample action *
            (Exp3.predictableLossAt actualLoss t sample action -
              Exp3.predictableLossAt actualLoss t sample best)) := by
    intro t ht action haction
    let probability := fun sample : Env × ((k : Nat) -> Action × Real) =>
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action
    let actualDiff := fun sample : Env × ((k : Nat) -> Action × Real) =>
      Exp3.predictableLossAt actualLoss t sample action -
        Exp3.predictableLossAt actualLoss t sample best
    let referenceDiff := fun sample : Env × ((k : Nat) -> Action × Real) =>
      Exp3.predictableLossAt referenceLoss t sample action -
        Exp3.predictableLossAt referenceLoss t sample best
    let weightedDeviation := fun sample :
        Env × ((k : Nat) -> Action × Real) =>
      probability sample * deviation t sample action
    have hrefIntegrable : Integrable (probability * referenceDiff) mu := by
      simpa only [probability, referenceDiff] using
        integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
          mu arms harms eta referenceLoss best action
            (Finset.mem_of_mem_erase haction) t
    have hactualIntegrable : Integrable (probability * actualDiff) mu := by
      simpa only [probability, actualDiff] using
        integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
          mu arms harms eta actualLoss best action
            (Finset.mem_of_mem_erase haction) t
    have hweightedDeviationIntegrable : Integrable weightedDeviation mu := by
      simpa only [weightedDeviation, probability] using
        hdeviation_integrable t ht action haction
    have hpointwise : ∀ᵐ sample ∂mu,
        probability sample * referenceDiff sample -
            weightedDeviation sample <=
          probability sample * actualDiff sample := by
      filter_upwards [] with sample
      have hsimplex :=
        finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample
      have hp0 : 0 <= probability sample :=
        hsimplex.1 action (Finset.mem_of_mem_erase haction)
      have habs : referenceDiff sample - actualDiff sample <=
          |actualDiff sample - referenceDiff sample| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have hdelta : referenceDiff sample - actualDiff sample <=
          deviation t sample action := by
        exact habs.trans (by
          simpa only [actualDiff, referenceDiff] using
            hdeviation t ht sample action haction)
      have hweighted := mul_le_mul_of_nonneg_left hdelta hp0
      dsimp only [weightedDeviation]
      nlinarith
    have hmono := integral_mono_ae
      (hrefIntegrable.sub hweightedDeviationIntegrable)
      hactualIntegrable hpointwise
    change integral mu (fun sample =>
        probability sample * referenceDiff sample -
          weightedDeviation sample) <=
      integral mu (fun sample =>
        probability sample * actualDiff sample) at hmono
    have hsubIntegral :
        integral mu (fun sample =>
            probability sample * referenceDiff sample -
              weightedDeviation sample) =
          integral mu (fun sample =>
            probability sample * referenceDiff sample) -
          integral mu weightedDeviation := by
      simpa only [Pi.sub_apply, Pi.mul_apply] using
        integral_sub hrefIntegrable hweightedDeviationIntegrable
    rw [hsubIntegral] at hmono
    have href : integral mu (fun sample =>
        probability sample * referenceDiff sample) =
        baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action := by
      simpa only [probability, referenceDiff, Pi.mul_apply] using
        hreferenceGapLaw t ht action haction
    rw [href] at hmono
    simpa only [probability, actualDiff, weightedDeviation, Pi.mul_apply] using
      hmono
  calc
    (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) -
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          integral mu (fun sample =>
            sampledScheduledHalfTsallisProbabilityAtTime
                arms harms eta t sample action *
              deviation t sample action))) =
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action -
            integral mu (fun sample =>
              sampledScheduledHalfTsallisProbabilityAtTime
                  arms harms eta t sample action *
                deviation t sample action))) := by
      simp [Finset.sum_sub_distrib]
    _ <= (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          integral mu (fun sample =>
            sampledScheduledHalfTsallisProbabilityAtTime
                arms harms eta t sample action *
              (Exp3.predictableLossAt actualLoss t sample action -
                Exp3.predictableLossAt actualLoss t sample best)))) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' : t <= horizon :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      apply Finset.sum_le_sum
      intro action haction
      exact hcoordinate t ht' action haction
    _ = integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta actualLoss (pointMass best) horizon) :=
      hactualIntegral.symm

end Tsallis
end BanditRLProof
