import BanditRLProof.TsallisScheduledExpectedRegret
import BanditRLProof.TsallisRefinedSuboptimalStability
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Expected suboptimal-arm bound for scheduled half-Tsallis FTRL

This module converts the generated pathwise refined half-power budget into a
deterministic expression involving square roots of expected action
probabilities.  It is the Jensen bridge between the compiled scheduled
expected-regret theorem and the self-bounding completion-of-squares consumer.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Expected probability of one action under an arbitrary trajectory law. -/
noncomputable def sampledScheduledHalfTsallisExpectedProbabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (action : Action) : Real :=
  integral mu (fun sample =>
    sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample action)

theorem integrable_sampledScheduledHalfTsallisProbabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (action : Action) (haction : action ∈ arms) :
    Integrable (fun sample =>
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action) mu := by
  have hmeas := measurable_sampledScheduledHalfTsallisProbabilityAtTime
    (Env := Env) arms harms eta t action haction
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun sample => by
    have hp := finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample
    rw [Real.norm_eq_abs, abs_of_nonneg (hp.1 action haction)]
    exact finiteSimplex_apply_le_one hp haction

theorem integrable_sqrt_sampledScheduledHalfTsallisProbabilityAtTime
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (action : Action) (haction : action ∈ arms) :
    Integrable (fun sample =>
      Real.sqrt (sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action)) mu := by
  have hmeas := (measurable_sampledScheduledHalfTsallisProbabilityAtTime
    (Env := Env) arms harms eta t action haction).sqrt
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun sample => by
    have hp := finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample
    have hsqrtNonneg : 0 <= Real.sqrt
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample action) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsqrtNonneg]
    exact (Real.sqrt_le_one).2 (finiteSimplex_apply_le_one hp haction)

/-- Integrating a generated finite-simplex law under a probability measure
again gives a finite-simplex law. -/
theorem finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) :
    FTRL.finiteSimplex arms
      (sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t) := by
  constructor
  · intro action haction
    unfold sampledScheduledHalfTsallisExpectedProbabilityAt
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun sample =>
      (finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample).1 action haction)
  · unfold sampledScheduledHalfTsallisExpectedProbabilityAt
    rw [← ExpectationBochnerSums.integral_finset_sum mu arms
      (fun action sample =>
        sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample action)
      (fun action haction =>
        integrable_sampledScheduledHalfTsallisProbabilityAtTime
          mu arms harms eta t action haction)]
    have hpointwise : (fun sample : Env × ((k : Nat) -> Action × Real) =>
        arms.sum (fun action =>
          sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample action)) = fun _sample => (1 : Real) := by
      funext sample
      exact (finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample).2
    rw [hpointwise]
    simp

/-- Jensen transport for one scheduled action coordinate. -/
theorem integral_sqrt_sampledScheduledHalfTsallisProbabilityAtTime_le_sqrt_expected
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (action : Action) (haction : action ∈ arms) :
    integral mu (fun sample =>
        Real.sqrt (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample action)) <=
      Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t action) := by
  let probability := fun sample : Env × ((k : Nat) -> Action × Real) =>
    sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample action
  have hprobability : Integrable probability mu :=
    integrable_sampledScheduledHalfTsallisProbabilityAtTime
      mu arms harms eta t action haction
  have hsqrt : Integrable (fun sample => Real.sqrt (probability sample)) mu :=
    integrable_sqrt_sampledScheduledHalfTsallisProbabilityAtTime
      mu arms harms eta t action haction
  have hnonneg : ∀ᵐ sample ∂mu, probability sample ∈ Set.Ici (0 : Real) :=
    Filter.Eventually.of_forall fun sample =>
      (finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample).1 action haction
  have hjensen := Real.strictConcaveOn_sqrt.concaveOn.le_map_integral
    Real.continuous_sqrt.continuousOn isClosed_Ici hnonneg hprobability hsqrt
  simpa [probability, sampledScheduledHalfTsallisExpectedProbabilityAt,
    Function.comp_def] using hjensen

/-- On the small-rate branch, the all-rate actual-time budget is the refined
half-power budget of the actual scheduled probability. -/
theorem sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime_eq_refined
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real)) (t : Nat)
    (heta_le : eta t <= 1 / 2) :
    sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
        arms harms eta sample t =
      refinedPotentialStabilityBound arms (eta t)
        (fun sample action =>
          sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample action) sample := by
  cases t with
  | zero =>
      unfold sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
        sampledScheduledHalfTsallisInitialAllRatePotentialStabilityBound
      rw [if_pos heta_le]
      unfold sampledScheduledHalfTsallisInitialRefinedPotentialStabilityBound
        sampledScheduledHalfTsallisProbabilityAtTime
      rfl
  | succ n =>
      unfold sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
        sampledScheduledHalfTsallisSuccessorAllRatePotentialStabilityBoundAt
      change (if eta (n + 1) <= 1 / 2 then
          sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
            arms harms eta n (sampledScheduledHalfTsallisHistoryAt n sample)
        else 1) = _
      rw [if_pos heta_le]
      unfold sampledScheduledHalfTsallisRefinedPotentialStabilityBoundAt
        sampledScheduledHalfTsallisProbabilityAtTime
        sampledScheduledHalfTsallisProbabilityAt
        sampledScheduledHalfTsallisHistoryAt
      rfl

/-- One integrated small-rate budget is bounded by suboptimal-arm square roots
of expected scheduled probabilities. -/
theorem integral_sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime_le_suboptimalExpectedSqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (t : Nat)
    (heta : 0 < eta t) (heta_le : eta t <= 1 / 2) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t) <=
      2 * eta t * (arms.erase best).sum (fun action =>
        Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action)) + 2 * (eta t) ^ 2 := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let probability := fun sample : Env × ((k : Nat) -> Action × Real) =>
    sampledScheduledHalfTsallisProbabilityAtTime arms harms eta t sample
  let suboptimalSqrt := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (arms.erase best).sum (fun action => Real.sqrt (probability sample action))
  haveI : IsProbabilityMeasure mu := inferInstance
  have hbudget :=
    integral_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
      prior arms harms eta loss t heta
  dsimp only at hbudget
  have hallRateIntegrable : Integrable (fun sample =>
      sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
        arms harms eta sample t) mu := hbudget.2.1
  have hsuboptimalIntegrable : Integrable suboptimalSqrt mu := by
    unfold suboptimalSqrt
    exact IntegrabilitySums.integrable_finset_sum mu (arms.erase best)
      (fun action sample => Real.sqrt (probability sample action))
      (fun action haction => by
        have hairm : action ∈ arms := Finset.mem_of_mem_erase haction
        simpa [probability] using
          (integrable_sqrt_sampledScheduledHalfTsallisProbabilityAtTime
            mu arms harms eta t action hairm))
  let rhs := fun sample : Env × ((k : Nat) -> Action × Real) =>
    2 * eta t * suboptimalSqrt sample + 2 * (eta t) ^ 2
  have hrhsIntegrable : Integrable rhs mu := by
    unfold rhs
    exact (hsuboptimalIntegrable.const_mul (2 * eta t)).add
      (integrable_const _)
  have hpointwise : ∀ᵐ sample ∂mu,
      sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t <= rhs sample := by
    filter_upwards [] with sample
    rw [sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime_eq_refined
      arms harms eta sample t heta_le]
    have hsimplex :=
      finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample
    have heliminate :=
      sum_sqrt_mul_one_sub_le_two_mul_sum_erase_sqrt
        arms hbest (probability sample) hsimplex
    unfold refinedPotentialStabilityBound rhs suboptimalSqrt probability
    nlinarith
  have hintegrated :=
    integral_mono_ae hallRateIntegrable hrhsIntegrable hpointwise
  have hrhsIntegral : integral mu rhs =
      2 * eta t * (arms.erase best).sum (fun action =>
        integral mu (fun sample => Real.sqrt (probability sample action))) +
        2 * (eta t) ^ 2 := by
    unfold rhs
    rw [integral_add (hsuboptimalIntegrable.const_mul (2 * eta t))
      (integrable_const _)]
    rw [integral_const_mul]
    rw [ExpectationBochnerSums.integral_finset_sum mu (arms.erase best)
      (fun action sample => Real.sqrt (probability sample action))]
    · simp
    · intro action haction
      have hairm : action ∈ arms := Finset.mem_of_mem_erase haction
      simpa [probability] using
        (integrable_sqrt_sampledScheduledHalfTsallisProbabilityAtTime
          mu arms harms eta t action hairm)
  rw [hrhsIntegral] at hintegrated
  have hjensen :
      (arms.erase best).sum (fun action =>
          integral mu (fun sample => Real.sqrt (probability sample action))) <=
        (arms.erase best).sum (fun action =>
          Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) := by
    apply Finset.sum_le_sum
    intro action haction
    have hairm : action ∈ arms := Finset.mem_of_mem_erase haction
    simpa [probability] using
      (integral_sqrt_sampledScheduledHalfTsallisProbabilityAtTime_le_sqrt_expected
        mu arms harms eta t action hairm)
  nlinarith

/-- The complete integrated all-rate budget, on its small-rate branch, is
bounded by a deterministic time/suboptimal-arm sum of square roots of expected
scheduled probabilities. -/
theorem integral_sum_sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime_le_suboptimalExpectedSqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (horizon : Nat) (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real) (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms)
    (heta : forall t, t <= horizon -> 0 < eta t)
    (heta_le : forall t, t <= horizon -> eta t <= 1 / 2) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) <=
      (Finset.range (horizon + 1)).sum (fun t =>
        2 * eta t * (arms.erase best).sum (fun action =>
          Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) + 2 * (eta t) ^ 2) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hround (t : Nat) (ht : t ∈ Finset.range (horizon + 1)) :=
    integral_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
      prior arms harms eta loss t
        (heta t (by
          have ht' := Finset.mem_range.mp ht
          omega))
  dsimp only at hround
  calc
    integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) =
      (Finset.range (horizon + 1)).sum (fun t =>
        integral mu (fun sample =>
          sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
            arms harms eta sample t)) := by
        exact ExpectationBochnerSums.integral_finset_sum mu
          (Finset.range (horizon + 1)) _
          (fun t ht => (hround t ht).2.1)
    _ <= (Finset.range (horizon + 1)).sum (fun t =>
        2 * eta t * (arms.erase best).sum (fun action =>
          Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) + 2 * (eta t) ^ 2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact
        integral_sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime_le_suboptimalExpectedSqrt
          prior arms harms eta loss hbest t
            (heta t (by
              have ht' := Finset.mem_range.mp ht
              omega))
            (heta_le t (by
              have ht' := Finset.mem_range.mp ht
              omega))

/-- Generated scheduled predictable environment regret against the best-arm
point mass has the deterministic suboptimal-arm upper needed by the
self-bounding completion-of-squares step. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_suboptimalExpectedSqrt
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
    (hetaMono : forall t, t < horizon -> eta (t + 1) <= eta t) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) <=
      (Finset.range (horizon + 1)).sum (fun t =>
        2 * eta t * (arms.erase best).sum (fun action =>
          Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action)) + 2 * (eta t) ^ 2) +
        halfTsallisPotentialMass arms
          (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
        1 / eta horizon := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  have hregret :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_allRateBound
      prior arms harms eta loss hbest horizon heta hetaMono
  dsimp only at hregret
  have hbudget :=
    integral_sum_sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime_le_suboptimalExpectedSqrt
      prior horizon arms harms eta loss hbest heta heta_le
  dsimp only at hbudget
  linarith

/-- The generated scheduled upper bound feeds the abstract self-bounding
completion-of-squares theorem without any remaining pathwise or Jensen
obligation. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_of_selfBounding
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
    (hgap : forall action, action ∈ arms.erase best -> 0 < gap action)
    (corruption : Real)
    (hselfBounding :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              (prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
                arms harms eta
                  (canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
                    arms harms eta loss).finiteHistory
                  loss.environment)
              arms harms eta t action)) - corruption <=
        integral
          (prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
            arms harms eta
              (canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
                arms harms eta loss).finiteHistory
              loss.environment)
          (sampledScheduledHalfTsallisPredictableEnvironmentRegret
            arms harms eta loss (pointMass best) horizon)) :
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
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let times := Finset.range (horizon + 1)
  let indices := times.product (arms.erase best)
  let probability := fun index : Nat × Action =>
    sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta index.1 index.2
  let coefficient := fun index : Nat × Action => 2 * eta index.1
  let indexGap := fun index : Nat × Action => gap index.2
  let regret := integral mu
    (sampledScheduledHalfTsallisPredictableEnvironmentRegret
      arms harms eta loss (pointMass best) horizon)
  let base := times.sum (fun t => 2 * (eta t) ^ 2) +
    (halfTsallisPotentialMass arms
        (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
      1 / eta horizon)
  have hprobability : forall index, index ∈ indices ->
      0 <= probability index := by
    intro index hindex
    have htime : index.1 ∈ times := (Finset.mem_product.mp hindex).1
    have haction : index.2 ∈ arms.erase best :=
      (Finset.mem_product.mp hindex).2
    have hsimplex :=
      finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta index.1
    exact hsimplex.1 index.2 (Finset.mem_of_mem_erase haction)
  have hgapIndex : forall index, index ∈ indices ->
      0 < indexGap index := by
    intro index hindex
    exact hgap index.2 (Finset.mem_product.mp hindex).2
  have hselfBoundingIndex :
      indices.sum (fun index => indexGap index * probability index) -
          corruption <= regret := by
    simpa [indices, times, indexGap, probability, regret, mu, selector,
      Finset.sum_product] using hselfBounding
  have hregret :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_suboptimalExpectedSqrt
      prior arms harms eta loss hbest horizon heta heta_le hetaMono
  dsimp only at hregret
  have hupper : regret <= base + indices.sum (fun index =>
      coefficient index * Real.sqrt (probability index)) := by
    calc
      regret <= (Finset.range (horizon + 1)).sum (fun t =>
          2 * eta t * (arms.erase best).sum (fun action =>
            Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) + 2 * (eta t) ^ 2) +
          halfTsallisPotentialMass arms
            (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
          1 / eta horizon := by
        simpa [regret, mu, selector] using hregret
      _ = base + indices.sum (fun index =>
          coefficient index * Real.sqrt (probability index)) := by
        simp [base, indices, times, coefficient, probability,
          Finset.sum_product, Finset.sum_add_distrib, Finset.mul_sum]
        ring
  have hfinal := regret_le_two_mul_base_add_sum_sq_div_gap_add_corruption
    indices probability coefficient indexGap regret base corruption
      hprobability hgapIndex hselfBoundingIndex hupper
  simpa [regret, base, indices, times, coefficient, indexGap, probability,
    mu, selector] using hfinal

end Tsallis
end BanditRLProof
