import BanditRLProof.TsallisScheduledConditionalMeanGap
import BanditRLProof.TsallisFiniteArmIIDCorruptedRewardLaw

/-!
# Time-varying expected-gap laws for scheduled half-Tsallis FTRL

This module lets the conditional or independent mean loss gap vary with the
round.  It is the law surface needed by deterministic predictable corruption
schedules: the baseline stochastic gap remains fixed, while clipping a
round-dependent reward shift perturbs the actual gap by a known per-round
amount.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Per-time first-moment law for probability-weighted predictable loss gaps. -/
def HasScheduledTimeVaryingExpectedGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Nat -> Action -> Real) (horizon : Nat) : Prop :=
  ∀ t, t <= horizon -> ∀ action, action ∈ arms.erase best ->
    integral mu (fun sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample action *
          (Exp3.predictableLossAt loss t sample action -
            Exp3.predictableLossAt loss t sample best)) =
      gap t action * sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t action

/-- Per-time conditional mean law relative to the information available
before the scheduled action. -/
def HasScheduledTimeVaryingConditionalMeanGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Nat -> Action -> Real) (horizon : Nat) : Prop :=
  ∀ t, t <= horizon -> ∀ action, action ∈ arms.erase best ->
    condExp
        (sampledScheduledHalfTsallisPastSigma
          (Env := Env) (Action := Action) t)
        mu
        (fun sample =>
          Exp3.predictableLossAt loss t sample action -
            Exp3.predictableLossAt loss t sample best) =ᵐ[mu]
      fun _sample => gap t action

/-- Per-time independence and global-mean law for predictable loss gaps. -/
def HasScheduledTimeVaryingIndependentMeanGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Nat -> Action -> Real) (horizon : Nat) : Prop :=
  ∀ t, t <= horizon -> ∀ action, action ∈ arms.erase best ->
    let lossDiff := fun sample : Env × ((k : Nat) -> Action × Real) =>
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best
    Indep (MeasurableSpace.comap lossDiff inferInstance)
        (sampledScheduledHalfTsallisPastSigma
          (Env := Env) (Action := Action) t) mu ∧
      integral mu lossDiff = gap t action

/-- Independence from the scheduled past identifies each time-varying
conditional mean. -/
theorem hasScheduledTimeVaryingConditionalMeanGapLaw_of_independentMeanGapLaw
    {Env : Type u} {Action : Type v}
    [mEnv : MeasurableSpace Env]
    [mAction : MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Nat -> Action -> Real) (horizon : Nat)
    (hgap : HasScheduledTimeVaryingIndependentMeanGapLaw
      mu arms loss best gap horizon) :
    HasScheduledTimeVaryingConditionalMeanGapLaw
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
        (Env × ((k : Nat) -> Action × Real))) :=
    Measurable.comap_le hmeasLoss
  have hlePast : mPast <=
      (Prod.instMeasurableSpace : MeasurableSpace
        (Env × ((k : Nat) -> Action × Real))) := by
    exact sampledScheduledHalfTsallisPastSigma_le t
  have hstrongLoss : @StronglyMeasurable
      (Env × ((k : Nat) -> Action × Real)) Real _ mLoss lossDiff :=
    (comap_measurable lossDiff).stronglyMeasurable
  rcases hgap t ht action haction with ⟨hindep, hmean⟩
  have hcond :=
    @MeasureTheory.condExp_indep_eq
      (Env × ((k : Nat) -> Action × Real)) Real _ _ _
      mLoss mPast Prod.instMeasurableSpace mu lossDiff
      hleLoss hlePast inferInstance hstrongLoss hindep
  change condExp mPast mu lossDiff =ᵐ[mu] fun _sample => gap t action
  exact hcond.mono (fun _sample hsample => by rw [hsample, hmean])

/-- A time-varying conditional mean law yields the corresponding weighted
expected-gap law by pulling the scheduled probability through `condExp`. -/
theorem hasScheduledTimeVaryingExpectedGapLaw_of_conditionalMeanGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Nat -> Action -> Real) (horizon : Nat)
    (hgap : HasScheduledTimeVaryingConditionalMeanGapLaw
      mu arms loss best gap horizon) :
    HasScheduledTimeVaryingExpectedGapLaw
      mu arms harms eta loss best gap horizon := by
  intro t ht action hactionErase
  have haction : action ∈ arms := Finset.mem_of_mem_erase hactionErase
  let probability := fun sample : Env × ((k : Nat) -> Action × Real) =>
    sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample action
  let lossDiff := fun sample : Env × ((k : Nat) -> Action × Real) =>
    Exp3.predictableLossAt loss t sample action -
      Exp3.predictableLossAt loss t sample best
  have hm := sampledScheduledHalfTsallisPastSigma_le
    (Env := Env) (Action := Action) t
  have hprobability : StronglyMeasurable[
      sampledScheduledHalfTsallisPastSigma
        (Env := Env) (Action := Action) t] probability :=
    (measurable_sampledScheduledHalfTsallisProbabilityAtTime_pastSigma
      arms harms eta t action haction).stronglyMeasurable
  have hlossDiff : Integrable lossDiff mu :=
    (Exp3.integrable_predictableLossAt mu loss t action).sub
      (Exp3.integrable_predictableLossAt mu loss t best)
  have hproduct : Integrable (probability * lossDiff) mu := by
    simpa only [probability, lossDiff] using
      integrable_sampledScheduledHalfTsallisProbability_mul_predictableLossDiffAt
        mu arms harms eta loss best action haction t
  have hpull :
      condExp
          (sampledScheduledHalfTsallisPastSigma
            (Env := Env) (Action := Action) t)
          mu (probability * lossDiff) =ᵐ[mu]
        probability * condExp
          (sampledScheduledHalfTsallisPastSigma
            (Env := Env) (Action := Action) t)
          mu lossDiff :=
    condExp_mul_of_stronglyMeasurable_left
      hprobability hproduct hlossDiff
  have hconditional :
      condExp
          (sampledScheduledHalfTsallisPastSigma
            (Env := Env) (Action := Action) t)
          mu lossDiff =ᵐ[mu] fun _sample => gap t action := by
    simpa only [lossDiff] using hgap t ht action hactionErase
  change integral mu (probability * lossDiff) =
    gap t action * sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action
  calc
    integral mu (probability * lossDiff) =
        integral mu (condExp
          (sampledScheduledHalfTsallisPastSigma
            (Env := Env) (Action := Action) t)
          mu (probability * lossDiff)) := by
      symm
      exact integral_condExp hm
    _ = integral mu (probability * condExp
        (sampledScheduledHalfTsallisPastSigma
          (Env := Env) (Action := Action) t)
        mu lossDiff) := integral_congr_ae hpull
    _ = integral mu (fun sample => probability sample * gap t action) :=
      integral_congr_ae ((Filter.EventuallyEq.refl _ probability).mul hconditional)
    _ = gap t action * integral mu probability := by
      rw [integral_mul_const]
      exact mul_comm _ _
    _ = gap t action * sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t action := rfl

/-- The independent time-varying mean contract directly feeds the weighted
expected-gap law. -/
theorem hasScheduledTimeVaryingExpectedGapLaw_of_independentMeanGapLaw
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (best : Action) (gap : Nat -> Action -> Real) (horizon : Nat)
    (hgap : HasScheduledTimeVaryingIndependentMeanGapLaw
      mu arms loss best gap horizon) :
    HasScheduledTimeVaryingExpectedGapLaw
      mu arms harms eta loss best gap horizon :=
  hasScheduledTimeVaryingExpectedGapLaw_of_conditionalMeanGapLaw
    mu arms harms eta loss best gap horizon
      (hasScheduledTimeVaryingConditionalMeanGapLaw_of_independentMeanGapLaw
        mu arms loss best gap horizon hgap)

/-- A time-varying expected-gap law identifies integrated regret with the
time-by-arm actual gap mass. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalTimeVaryingExpectedGapMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms)
    (gap : Nat -> Action -> Real) (horizon : Nat)
    (hgapLaw : HasScheduledTimeVaryingExpectedGapLaw
      mu arms harms eta loss best gap horizon) :
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) =
      (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          gap t action * sampledScheduledHalfTsallisExpectedProbabilityAt
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

/-- Accumulated coordinatewise deviation from fixed baseline gaps. -/
noncomputable def scheduledTimeVaryingGapDeviationBudget
    {Action : Type*} [DecidableEq Action]
    (arms : Finset Action) (best : Action) (horizon : Nat)
    (deviation : Nat -> Action -> Real) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    (arms.erase best).sum (deviation t))

/-- A time-varying actual-gap law within a known coordinatewise distance of
fixed baseline gaps yields the self-bound consumed by schedule tuning. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_timeVaryingPerturbedExpectedGapLaw
    {Env Action : Type*}
    [MeasurableSpace Env] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (baseGap : Action -> Real) (actualGap deviation : Nat -> Action -> Real)
    (hactualGapLaw : HasScheduledTimeVaryingExpectedGapLaw
      mu arms harms eta loss best actualGap horizon)
    (hdeviation : ∀ t, t <= horizon -> ∀ action,
      action ∈ arms.erase best ->
        |actualGap t action - baseGap action| <= deviation t action) :
    (Finset.range (horizon + 1)).sum (fun t =>
        (arms.erase best).sum (fun action =>
          baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) -
      scheduledTimeVaryingGapDeviationBudget
        arms best horizon deviation <=
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss (pointMass best) horizon) := by
  have hregret :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_eq_suboptimalTimeVaryingExpectedGapMass
      mu arms harms eta loss hbest actualGap horizon hactualGapLaw
  have hbaseLe :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            baseGap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) <=
        (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            actualGap t action *
                sampledScheduledHalfTsallisExpectedProbabilityAt
                  mu arms harms eta t action +
              deviation t action)) := by
    apply Finset.sum_le_sum
    intro t ht
    have ht' : t <= horizon :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    apply Finset.sum_le_sum
    intro action haction
    let probability := sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action
    have hsimplex :=
      finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t
    have hp0 : 0 <= probability :=
      hsimplex.1 action (Finset.mem_of_mem_erase haction)
    have hp1 : probability <= 1 :=
      finiteSimplex_apply_le_one hsimplex
        (Finset.mem_of_mem_erase haction)
    have habs : baseGap action - actualGap t action <=
        |actualGap t action - baseGap action| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have hweighted :
        (baseGap action - actualGap t action) * probability <=
          deviation t action := by
      calc
        (baseGap action - actualGap t action) * probability <=
            |actualGap t action - baseGap action| * probability :=
          mul_le_mul_of_nonneg_right habs hp0
        _ <= |actualGap t action - baseGap action| := by
          simpa using mul_le_of_le_one_right (abs_nonneg _) hp1
        _ <= deviation t action := hdeviation t ht' action haction
    dsimp only [probability] at hweighted ⊢
    linarith
  have hsplit :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            actualGap t action *
                sampledScheduledHalfTsallisExpectedProbabilityAt
                  mu arms harms eta t action +
              deviation t action)) =
        (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            actualGap t action *
              sampledScheduledHalfTsallisExpectedProbabilityAt
                mu arms harms eta t action)) +
          scheduledTimeVaryingGapDeviationBudget
            arms best horizon deviation := by
    simp only [Finset.sum_add_distrib,
      scheduledTimeVaryingGapDeviationBudget]
  rw [hsplit] at hbaseLe
  rw [hregret]
  linarith

end Tsallis
end BanditRLProof
