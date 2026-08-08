import BanditRLProof.TsallisScheduledConditionalMeanGap
import BanditRLProof.TsallisSqrtScheduleFixedGap
import Mathlib.Probability.ConditionalExpectation

/-!
# Independent-mean producer for scheduled half-Tsallis expected gaps

This module turns an independence-plus-global-mean contract for every
predictable loss difference into the conditional-mean law used by scheduled
self-bounding.  It also exposes the resulting logarithmic square-root-schedule
regret theorem on the generated trajectory law.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- For every included time and suboptimal arm, the predictable loss
difference is independent of the pre-action trace sigma-algebra and has global
mean equal to the arm gap. -/
def HasScheduledIndependentMeanGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Action -> Real) (horizon : Nat) : Prop :=
  ∀ t, t <= horizon -> ∀ action, action ∈ arms.erase best ->
    let lossDiff := fun sample : Env × ((k : Nat) -> Action × Real) =>
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best
    Indep (MeasurableSpace.comap lossDiff inferInstance)
        (sampledScheduledHalfTsallisPastSigma
          (Env := Env) (Action := Action) t) mu ∧
      integral mu lossDiff = gap action

/-- Independence from the pre-action trace and the correct global mean imply
the scheduled conditional-mean gap law. -/
theorem hasScheduledConditionalMeanGapLaw_of_independentMeanGapLaw
    {Env : Type u} {Action : Type v}
    [mEnv : MeasurableSpace Env]
    [mAction : MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Action -> Real) (horizon : Nat)
    (hgap : HasScheduledIndependentMeanGapLaw
      mu arms loss best gap horizon) :
    HasScheduledConditionalMeanGapLaw
      mu arms loss best gap horizon := by
  intro t ht action haction
  let lossDiff := fun sample : Env × ((k : Nat) -> Action × Real) =>
    Exp3.predictableLossAt loss t sample action -
      Exp3.predictableLossAt loss t sample best
  let mLoss : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    MeasurableSpace.comap lossDiff inferInstance
  let mPast : MeasurableSpace (Env × ((k : Nat) -> Action × Real)) :=
    sampledScheduledHalfTsallisPastSigma
      (Env := Env) (Action := Action) t
  have hmeasLoss : @Measurable
      (Env × ((k : Nat) -> Action × Real)) Real
      Prod.instMeasurableSpace inferInstance lossDiff := by
    simpa only [lossDiff] using
      (Exp3.measurable_predictableLossAt loss t action).sub
        (Exp3.measurable_predictableLossAt loss t best)
  have hleLoss : mLoss <=
      (Prod.instMeasurableSpace : MeasurableSpace
        (Env × ((k : Nat) -> Action × Real))) := by
    exact Measurable.comap_le hmeasLoss
  have hlePast : mPast <=
      (Prod.instMeasurableSpace : MeasurableSpace
        (Env × ((k : Nat) -> Action × Real))) := by
    change sampledScheduledHalfTsallisPastSigma
      (Env := Env) (Action := Action) t <= Prod.instMeasurableSpace
    exact
      (sampledScheduledHalfTsallisPastSigma_le
        (Env := Env) (Action := Action) t)
  have hstrongLoss : @StronglyMeasurable
      (Env × ((k : Nat) -> Action × Real)) Real _ mLoss lossDiff :=
    (comap_measurable lossDiff).stronglyMeasurable
  rcases hgap t ht action haction with ⟨hindep, hmean⟩
  have hindep' : Indep mLoss mPast mu := by
    simpa only [mLoss, mPast, lossDiff] using hindep
  have hcond :=
    @MeasureTheory.condExp_indep_eq
      (Env × ((k : Nat) -> Action × Real)) Real _ _ _
      mLoss mPast
      Prod.instMeasurableSpace
      mu lossDiff hleLoss hlePast inferInstance hstrongLoss hindep'
  change condExp mPast mu lossDiff =ᵐ[mu] fun _sample => gap action
  exact hcond.mono (fun _sample hsample => by
    rw [hsample, hmean])

/-- The independence-plus-mean contract also directly produces the
coordinatewise first-moment law used by scheduled self-bounding. -/
theorem hasScheduledExpectedGapLaw_of_independentMeanGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Action -> Real) (horizon : Nat)
    (hgap : HasScheduledIndependentMeanGapLaw
      mu arms loss best gap horizon) :
    HasScheduledExpectedGapLaw
      mu arms harms eta loss best gap horizon := by
  exact hasScheduledExpectedGapLaw_of_conditionalMeanGapLaw
    mu arms harms eta loss best gap horizon
      (hasScheduledConditionalMeanGapLaw_of_independentMeanGapLaw
        mu arms loss best gap horizon hgap)

/-- Under coordinatewise independence from the pre-action trace and the
correct global loss-gap means, the generated square-root schedule satisfies
the explicit logarithmic regret bound. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_independentMeanGap
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (gap : Action -> Real)
    (hgapPos : ∀ action, action ∈ arms.erase best -> 0 < gap action)
    (hgapLaw :
      let selector :=
        canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
      let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms sampledScheduledHalfTsallisSqrtSchedule
          selector.finiteHistory loss.environment
      HasScheduledIndependentMeanGapLaw
        mu arms loss best gap horizon)
    (corruption : Real) (hcorruption : 0 <= corruption) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule
        selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)) +
      corruption := by
  dsimp only at hgapLaw ⊢
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  have hgapExpected : HasScheduledExpectedGapLaw
      mu arms harms sampledScheduledHalfTsallisSqrtSchedule
        loss best gap horizon :=
    hasScheduledExpectedGapLaw_of_independentMeanGapLaw
      mu arms harms sampledScheduledHalfTsallisSqrtSchedule
        loss best gap horizon hgapLaw
  exact
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_expectedGap
      prior arms harms loss hbest horizon gap hgapPos
        hgapExpected corruption hcorruption

end Tsallis
end BanditRLProof
