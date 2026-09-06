import BanditRLProof.TsallisScheduledSuboptimalExpectedBound

/-!
# Refined expected penalty for scheduled half-Tsallis FTRL

This module keeps the reciprocal-rate increments from the deterministic
time-varying penalty theorem instead of collapsing them into a terminal
potential mass.  The mass above the point-mass baseline is eliminated in
favor of suboptimal-arm terms, then transported through expectation by the
compiled square-root Jensen bridge.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- The concavity tangent at one bounds the excess of `sqrt x` over `x`. -/
theorem sqrt_sub_self_le_half_one_sub (x : Real) (hx : 0 <= x) :
    Real.sqrt x - x <= (1 - x) / 2 := by
  have hsquare : 0 <= (Real.sqrt x - 1) ^ 2 := sq_nonneg _
  have hsqrtSquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  nlinarith

/-- Above the point-mass baseline, half-Tsallis potential mass is controlled
by the paper's refined suboptimal-arm mass. -/
theorem halfTsallisPotentialMass_sub_one_le_two_mul_sum_erase_refined
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) {best : Action} (hbest : best ∈ arms)
    (probability : Action -> Real)
    (hprobability : FTRL.finiteSimplex arms probability) :
    halfTsallisPotentialMass arms probability - 1 <=
      2 * (arms.erase best).sum (fun action =>
        Real.sqrt (probability action) - probability action / 2) := by
  rw [halfTsallisPotentialMass_eq_two_mul_powerSum_sub_one]
  have hsplitSqrt := Finset.add_sum_erase arms
    (fun action => Real.sqrt (probability action)) hbest
  have hsplitProbability := Finset.add_sum_erase arms probability hbest
  rw [hprobability.2] at hsplitProbability
  have hbestBound := sqrt_sub_self_le_half_one_sub
    (probability best) (hprobability.1 best hbest)
  have heraseRewrite :
      (arms.erase best).sum (fun action =>
          Real.sqrt (probability action) - probability action / 2) =
        (arms.erase best).sum (fun action => Real.sqrt (probability action)) -
          (arms.erase best).sum probability / 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_div]
  rw [heraseRewrite]
  simp only [powerSum, ← Real.sqrt_eq_rpow]
  nlinarith

/-- Generated pathwise point-mass penalty with every reciprocal-rate
increment retained and every potential mass replaced by its refined
suboptimal-arm upper bound. -/
theorem sum_sampledScheduledHalfTsallisPotentialPenalty_pointMass_le_refined
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta : Nat -> Real)
    (sample : Env × ((k : Nat) -> Action × Real))
    {best : Action} (hbest : best ∈ arms) (n : Nat)
    (heta : forall t, t <= n -> 0 < eta t)
    (hetaMono : forall t, t < n -> eta (t + 1) <= eta t) :
    (Finset.range (n + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialPenaltyAtTime
          arms harms eta (pointMass best) sample t) <=
      2 / eta 0 * (arms.erase best).sum (fun action =>
        Real.sqrt (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta 0 sample action) -
        sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta 0 sample action / 2) +
      (Finset.range n).sum (fun t =>
        2 * (1 / eta (t + 1) - 1 / eta t) *
          (arms.erase best).sum (fun action =>
            Real.sqrt (sampledScheduledHalfTsallisProbabilityAtTime
              arms harms eta (t + 1) sample action) -
            sampledScheduledHalfTsallisProbabilityAtTime
              arms harms eta (t + 1) sample action / 2)) := by
  let probability := fun t =>
    sampledScheduledHalfTsallisProbabilityAtTime arms harms eta t sample
  let refinedMass := fun t => (arms.erase best).sum (fun action =>
    Real.sqrt (probability t action) - probability t action / 2)
  have hbase :
      (Finset.range (n + 1)).sum (fun t =>
          sampledScheduledHalfTsallisPotentialPenaltyAtTime
            arms harms eta (pointMass best) sample t) <=
        halfTsallisPotentialMass arms (probability 0) / eta 0 +
          (Finset.range n).sum (fun t =>
            (1 / eta (t + 1) - 1 / eta t) *
              halfTsallisPotentialMass arms (probability (t + 1))) -
          1 / eta n := by
    simpa [probability, sampledScheduledHalfTsallisPotentialPenaltyAtTime,
      sampledScheduledHalfTsallisSameRateNextAt,
      halfTsallisPotentialMass_pointMass arms hbest] using
      (sum_halfTsallisScheduledPotentialPenalty_le
        arms eta
          (fun t => sampledScheduledHalfTsallisObservedEstimatedLossAt
            arms harms eta t sample)
          (fun t => sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta t sample)
          (fun t => sampledScheduledHalfTsallisSameRateNextAt
            arms harms eta sample t)
          (pointMass best) n heta
          (fun t _ht => by
            change FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
              arms (eta t) (negEntropyRegularizer arms (1 / 2 : Real))
                (FTRL.cumulativeLoss
                  (fun s => sampledScheduledHalfTsallisObservedEstimatedLossAt
                    arms harms eta s sample) t)
                (sampledScheduledHalfTsallisProbabilityAtTime
                  arms harms eta t sample)
            rw [← halfTsallisScheduledMinimizer_observedEstimatedLoss_eq_probabilityAtTime
              arms harms eta sample t]
            exact halfTsallisMinimizer_isRegularizedMinimizer
              arms harms (eta t)
                (FTRL.cumulativeLoss
                  (fun s => sampledScheduledHalfTsallisObservedEstimatedLossAt
                    arms harms eta s sample) t))
          (fun t _ht => by
            unfold sampledScheduledHalfTsallisSameRateNextAt
              halfTsallisScheduledSameRateNext
            exact halfTsallisMinimizer_isRegularizedMinimizer
              arms harms (eta t)
                (FTRL.cumulativeLoss
                  (fun s => sampledScheduledHalfTsallisObservedEstimatedLossAt
                    arms harms eta s sample) (t + 1)))
          (finiteSimplex_pointMass arms hbest))
  have hmass (t : Nat) :
      halfTsallisPotentialMass arms (probability t) <=
        1 + 2 * refinedMass t := by
    have hsimplex :=
      finiteSimplex_sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample
    have h := halfTsallisPotentialMass_sub_one_le_two_mul_sum_erase_refined
      arms hbest (probability t) hsimplex
    dsimp only [refinedMass, probability]
    linarith
  have hcoefficient (t : Nat) (ht : t ∈ Finset.range n) :
      0 <= 1 / eta (t + 1) - 1 / eta t := by
    have htn : t < n := Finset.mem_range.mp ht
    exact sub_nonneg.mpr (one_div_le_one_div_of_le
      (heta (t + 1) (Nat.succ_le_of_lt htn)) (hetaMono t htn))
  have hinitial :
      halfTsallisPotentialMass arms (probability 0) / eta 0 <=
        (1 + 2 * refinedMass 0) / eta 0 :=
    (div_le_div_iff_of_pos_right (heta 0 (Nat.zero_le n))).2 (hmass 0)
  have hsum :
      (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (probability (t + 1))) <=
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            (1 + 2 * refinedMass (t + 1))) := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_left (hmass (t + 1)) (hcoefficient t ht)
  have htelescope := Exp3Potential.sum_range_forward_difference
    (fun t => 1 / eta t) n
  have hexpand :
      (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            (1 + 2 * refinedMass (t + 1))) =
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t)) +
        (Finset.range n).sum (fun t =>
          2 * (1 / eta (t + 1) - 1 / eta t) *
            refinedMass (t + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  calc
    (Finset.range (n + 1)).sum (fun t =>
        sampledScheduledHalfTsallisPotentialPenaltyAtTime
          arms harms eta (pointMass best) sample t) <=
      halfTsallisPotentialMass arms (probability 0) / eta 0 +
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            halfTsallisPotentialMass arms (probability (t + 1))) -
        1 / eta n := hbase
    _ <= (1 + 2 * refinedMass 0) / eta 0 +
        (Finset.range n).sum (fun t =>
          (1 / eta (t + 1) - 1 / eta t) *
            (1 + 2 * refinedMass (t + 1))) -
        1 / eta n := by linarith
    _ = 2 / eta 0 * refinedMass 0 +
        (Finset.range n).sum (fun t =>
          2 * (1 / eta (t + 1) - 1 / eta t) *
            refinedMass (t + 1)) := by
      rw [hexpand, htelescope]
      ring
    _ = _ := by rfl

/-- Refined suboptimal-arm mass on one generated trajectory sample. -/
noncomputable def sampledScheduledHalfTsallisRefinedSuboptimalMassAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (best : Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (arms.erase best).sum (fun action =>
    Real.sqrt (sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample action) -
    sampledScheduledHalfTsallisProbabilityAtTime
      arms harms eta t sample action / 2)

/-- Deterministic Jensen target for one refined suboptimal-arm mass. -/
noncomputable def sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (best : Action) (t : Nat) : Real :=
  (arms.erase best).sum (fun action =>
    Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action) -
    sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action / 2)

theorem integrable_sampledScheduledHalfTsallisRefinedSuboptimalMassAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real))) [IsFiniteMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    {best : Action} (t : Nat) :
    Integrable (sampledScheduledHalfTsallisRefinedSuboptimalMassAt
      arms harms eta best t) mu := by
  unfold sampledScheduledHalfTsallisRefinedSuboptimalMassAt
  exact IntegrabilitySums.integrable_finset_sum mu (arms.erase best)
    (fun action sample =>
      Real.sqrt (sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action) -
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action / 2)
    (fun action haction => by
      have hairm : action ∈ arms := Finset.mem_of_mem_erase haction
      exact
        (integrable_sqrt_sampledScheduledHalfTsallisProbabilityAtTime
          mu arms harms eta t action hairm).sub
        ((integrable_sampledScheduledHalfTsallisProbabilityAtTime
          mu arms harms eta t action hairm).div_const 2))

/-- Jensen transport for the complete refined suboptimal-arm mass at one
scheduled time. -/
theorem integral_sampledScheduledHalfTsallisRefinedSuboptimalMassAt_le_expected
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    {best : Action} (t : Nat) :
    integral mu (sampledScheduledHalfTsallisRefinedSuboptimalMassAt
        arms harms eta best t) <=
      sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
        mu arms harms eta best t := by
  unfold sampledScheduledHalfTsallisRefinedSuboptimalMassAt
  rw [ExpectationBochnerSums.integral_finset_sum mu (arms.erase best)
    (fun action sample =>
      Real.sqrt (sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action) -
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample action / 2)]
  · unfold sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
    apply Finset.sum_le_sum
    intro action haction
    have hairm : action ∈ arms := Finset.mem_of_mem_erase haction
    have hsqrt :=
      integrable_sqrt_sampledScheduledHalfTsallisProbabilityAtTime
        mu arms harms eta t action hairm
    have hprobability :=
      integrable_sampledScheduledHalfTsallisProbabilityAtTime
        mu arms harms eta t action hairm
    rw [integral_sub hsqrt (hprobability.div_const 2), integral_div]
    exact sub_le_sub_right
      (integral_sqrt_sampledScheduledHalfTsallisProbabilityAtTime_le_sqrt_expected
        mu arms harms eta t action hairm) _
  · intro action haction
    have hairm : action ∈ arms := Finset.mem_of_mem_erase haction
    exact
      (integrable_sqrt_sampledScheduledHalfTsallisProbabilityAtTime
        mu arms harms eta t action hairm).sub
      ((integrable_sampledScheduledHalfTsallisProbabilityAtTime
        mu arms harms eta t action hairm).div_const 2)

/-- The generated predictable environment regret retains the refined
time-varying penalty after expectation.  Unlike the coarse endpoint theorem,
no terminal potential mass divided by the final learning rate remains. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedExpectedPenalty
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (heta : forall t, t <= horizon -> 0 < eta t)
    (hetaMono : forall t, t < horizon -> eta (t + 1) <= eta t) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) <=
      integral mu (fun sample => (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
          arms harms eta sample t)) +
      2 / eta 0 * sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
        mu arms harms eta best 0 +
      (Finset.range horizon).sum (fun t =>
        2 * (1 / eta (t + 1) - 1 / eta t) *
          sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
            mu arms harms eta best (t + 1)) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let stabilitySum := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    (Finset.range (horizon + 1)).sum (fun t =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta sample t)
  let allRateSum := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    (Finset.range (horizon + 1)).sum (fun t =>
      sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
        arms harms eta sample t)
  let refinedMass := fun t =>
    sampledScheduledHalfTsallisRefinedSuboptimalMassAt
      (Env := Env) arms harms eta best t
  let refinedPenalty := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    2 / eta 0 * refinedMass 0 sample +
      (Finset.range horizon).sum (fun t =>
        2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1) sample)
  let expectedRefinedMass := fun t =>
    sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
      mu arms harms eta best t
  let expectedRefinedPenalty :=
    2 / eta 0 * expectedRefinedMass 0 +
      (Finset.range horizon).sum (fun t =>
        2 * (1 / eta (t + 1) - 1 / eta t) * expectedRefinedMass (t + 1))
  let rhs := fun (sample : Env × ((k : Nat) -> Action × Real)) =>
    stabilitySum sample + refinedPenalty sample
  haveI : IsProbabilityMeasure mu := inferInstance
  have hmoment :=
    integral_sampledScheduledHalfTsallisEstimatedRegret_eq_environmentRegret
      prior arms harms eta loss (pointMass best)
        (finiteSimplex_pointMass arms hbest) horizon
  dsimp only at hmoment
  have hstabilityIntegrable :=
    integrable_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_allRate
      prior horizon arms harms eta heta loss
  dsimp only at hstabilityIntegrable
  have hstabilityIntegrable' : Integrable stabilitySum mu := by
    simpa [stabilitySum, mu, selector] using hstabilityIntegrable.1
  have hallRateIntegrable : Integrable allRateSum mu := by
    simpa [allRateSum, mu, selector] using hstabilityIntegrable.2
  have hrefinedMassIntegrable (t : Nat) : Integrable (refinedMass t) mu := by
    simpa [refinedMass] using
      (integrable_sampledScheduledHalfTsallisRefinedSuboptimalMassAt
        mu arms harms eta (best := best) t)
  have hrefinedPenaltyIntegrable : Integrable refinedPenalty mu := by
    unfold refinedPenalty
    exact (hrefinedMassIntegrable 0).const_mul (2 / eta 0) |>.add
      (IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
        (fun t sample =>
          2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1) sample)
        (fun t _ht =>
          (hrefinedMassIntegrable (t + 1)).const_mul
            (2 * (1 / eta (t + 1) - 1 / eta t))))
  have hrhsIntegrable : Integrable rhs mu := by
    exact hstabilityIntegrable'.add hrefinedPenaltyIntegrable
  have hpathwise : ∀ᵐ sample ∂mu,
      sampledScheduledHalfTsallisEstimatedRegret
          arms harms eta (pointMass best) horizon sample <= rhs sample := by
    filter_upwards [] with sample
    rw [sampledScheduledHalfTsallisEstimatedRegret_eq_stability_add_penalty]
    have hpenalty :=
      sum_sampledScheduledHalfTsallisPotentialPenalty_pointMass_le_refined
        arms harms eta sample hbest horizon heta hetaMono
    simpa [rhs, stabilitySum, refinedPenalty, refinedMass,
      sampledScheduledHalfTsallisRefinedSuboptimalMassAt] using
      add_le_add_left hpenalty
        ((Finset.range (horizon + 1)).sum (fun t =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta sample t))
  have hintegrated := integral_mono_ae hmoment.1 hrhsIntegrable hpathwise
  have hrhsIntegral :
      integral mu rhs = integral mu stabilitySum + integral mu refinedPenalty := by
    unfold rhs
    exact integral_add hstabilityIntegrable' hrefinedPenaltyIntegrable
  have hrefinedPenaltyIntegral :
      integral mu refinedPenalty =
        2 / eta 0 * integral mu (refinedMass 0) +
        (Finset.range horizon).sum (fun t =>
          2 * (1 / eta (t + 1) - 1 / eta t) *
            integral mu (refinedMass (t + 1))) := by
    unfold refinedPenalty
    rw [integral_add ((hrefinedMassIntegrable 0).const_mul (2 / eta 0))
      (IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
        (fun t sample =>
          2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1) sample)
        (fun t _ht =>
          (hrefinedMassIntegrable (t + 1)).const_mul
            (2 * (1 / eta (t + 1) - 1 / eta t))))]
    rw [integral_const_mul]
    rw [ExpectationBochnerSums.integral_finset_sum mu (Finset.range horizon)
      (fun t sample =>
        2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1) sample)]
    · apply congrArg (fun value => 2 / eta 0 * integral mu (refinedMass 0) + value)
      apply Finset.sum_congr rfl
      intro t _ht
      rw [integral_const_mul]
    · intro t _ht
      exact (hrefinedMassIntegrable (t + 1)).const_mul
        (2 * (1 / eta (t + 1) - 1 / eta t))
  have hrefinedPenaltyBound :
      integral mu refinedPenalty <= expectedRefinedPenalty := by
    rw [hrefinedPenaltyIntegral]
    unfold expectedRefinedPenalty expectedRefinedMass
    have hinitial :=
      integral_sampledScheduledHalfTsallisRefinedSuboptimalMassAt_le_expected
        mu arms harms eta (best := best) 0
    have hinitialCoefficient : 0 <= 2 / eta 0 := by
      exact div_nonneg (by norm_num) (le_of_lt (heta 0 (Nat.zero_le horizon)))
    have hsum :
        (Finset.range horizon).sum (fun t =>
            2 * (1 / eta (t + 1) - 1 / eta t) *
              integral mu (refinedMass (t + 1))) <=
          (Finset.range horizon).sum (fun t =>
            2 * (1 / eta (t + 1) - 1 / eta t) *
              sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
                mu arms harms eta best (t + 1)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htn : t < horizon := Finset.mem_range.mp ht
      have hcoefficient :
          0 <= 2 * (1 / eta (t + 1) - 1 / eta t) := by
        have hreciprocal := one_div_le_one_div_of_le
          (heta (t + 1) (Nat.succ_le_of_lt htn)) (hetaMono t htn)
        exact mul_nonneg (by norm_num) (sub_nonneg.mpr hreciprocal)
      exact mul_le_mul_of_nonneg_left
        (by
          simpa [refinedMass] using
            (integral_sampledScheduledHalfTsallisRefinedSuboptimalMassAt_le_expected
              mu arms harms eta (best := best) (t + 1)))
        hcoefficient
    exact add_le_add
      (mul_le_mul_of_nonneg_left hinitial hinitialCoefficient) hsum
  have hstabilityBoundBase :=
    integral_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
      prior horizon arms harms eta heta loss
  dsimp only at hstabilityBoundBase
  have hstabilityBound : integral mu stabilitySum <= integral mu allRateSum := by
    simpa [mu, selector, stabilitySum, allRateSum] using hstabilityBoundBase
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) =
      integral mu (sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta (pointMass best) horizon) := hmoment.2.2.symm
    _ <= integral mu rhs := hintegrated
    _ = integral mu stabilitySum + integral mu refinedPenalty := hrhsIntegral
    _ <= integral mu allRateSum + expectedRefinedPenalty :=
      add_le_add hstabilityBound hrefinedPenaltyBound
    _ = _ := by
      unfold allRateSum expectedRefinedPenalty expectedRefinedMass mu selector
      ring

end Tsallis
end BanditRLProof
