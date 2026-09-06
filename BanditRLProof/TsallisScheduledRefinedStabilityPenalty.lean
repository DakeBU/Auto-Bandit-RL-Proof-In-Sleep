import BanditRLProof.TsallisScheduledRefinedExpectedPenalty
import BanditRLProof.TsallisScheduledExpectedGapSelfBounding

/-!
# Refined scheduled stability-penalty assembly

This module combines the generated small-rate stability budget with the
uncollapsed refined expected penalty.  It exposes one coefficient per actual
time and feeds the resulting square-root upper bound to the exact fixed-gap
self-bounding consumer.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Sum of square roots of expected probabilities over suboptimal arms. -/
noncomputable def sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (best : Action) (t : Nat) : Real :=
  (arms.erase best).sum (fun action =>
    Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action))

/-- Dropping the nonpositive linear correction weakens the expected refined
mass to the square-root mass used by completion of squares. -/
theorem sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt_le_sqrtMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) -> Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    {best : Action} (t : Nat) :
    sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
        mu arms harms eta best t <=
      sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt
        mu arms harms eta best t := by
  unfold sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
    sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt
  apply Finset.sum_le_sum
  intro action haction
  have hsimplex :=
    finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t
  have hnonneg := hsimplex.1 action (Finset.mem_of_mem_erase haction)
  linarith

/-- Combined coefficient multiplying `sqrt (E[p_t(a)])` after adding refined
stability and reciprocal-rate penalty terms. -/
noncomputable def sampledScheduledHalfTsallisRefinedCoefficient
    (eta : Nat -> Real) : Nat -> Real
  | 0 => 2 * eta 0 + 2 / eta 0
  | t + 1 =>
      2 * eta (t + 1) + 2 * (1 / eta (t + 1) - 1 / eta t)

/-- Generated predictable environment regret is bounded by the deterministic
quadratic-rate budget plus one refined square-root mass per actual time. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty
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
      (Finset.range (horizon + 1)).sum (fun t => 2 * (eta t) ^ 2) +
      (Finset.range (horizon + 1)).sum (fun t =>
        sampledScheduledHalfTsallisRefinedCoefficient eta t *
          sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt
            mu arms harms eta best t) := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let sqrtMass := fun t =>
    sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt
      mu arms harms eta best t
  let refinedMass := fun t =>
    sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt
      mu arms harms eta best t
  let stabilityTerm := fun t => 2 * eta t * sqrtMass t + 2 * (eta t) ^ 2
  let penaltyIncrement := fun t =>
    2 * (1 / eta (t + 1) - 1 / eta t) * sqrtMass (t + 1)
  let baseTerm := fun t => 2 * (eta t) ^ 2
  let coefficientTerm := fun t =>
    sampledScheduledHalfTsallisRefinedCoefficient eta t * sqrtMass t
  haveI : IsProbabilityMeasure mu := inferInstance
  have hregret :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedExpectedPenalty
      prior arms harms eta loss hbest horizon heta hetaMono
  dsimp only at hregret
  have hstability :=
    integral_sum_sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime_le_suboptimalExpectedSqrt
      prior horizon arms harms eta loss hbest heta heta_le
  dsimp only at hstability
  have hmass (t : Nat) : refinedMass t <= sqrtMass t := by
    simpa [refinedMass, sqrtMass] using
      (sampledScheduledHalfTsallisExpectedRefinedSuboptimalMassAt_le_sqrtMass
        mu arms harms eta (best := best) t)
  have hinitialCoefficient : 0 <= 2 / eta 0 := by
    exact div_nonneg (by norm_num) (le_of_lt (heta 0 (Nat.zero_le horizon)))
  have hinitial : 2 / eta 0 * refinedMass 0 <=
      2 / eta 0 * sqrtMass 0 :=
    mul_le_mul_of_nonneg_left (hmass 0) hinitialCoefficient
  have hsum :
      (Finset.range horizon).sum (fun t =>
          2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1)) <=
        (Finset.range horizon).sum penaltyIncrement := by
    apply Finset.sum_le_sum
    intro t ht
    have htn : t < horizon := Finset.mem_range.mp ht
    have hreciprocal := one_div_le_one_div_of_le
      (heta (t + 1) (Nat.succ_le_of_lt htn)) (hetaMono t htn)
    have hcoefficient :
        0 <= 2 * (1 / eta (t + 1) - 1 / eta t) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hreciprocal)
    exact mul_le_mul_of_nonneg_left (hmass (t + 1)) hcoefficient
  have hcombined :
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss (pointMass best) horizon) <=
        (Finset.range (horizon + 1)).sum stabilityTerm +
          2 / eta 0 * sqrtMass 0 +
          (Finset.range horizon).sum penaltyIncrement := by
    have hdeterministic :
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
            arms harms eta loss (pointMass best) horizon) <=
          (Finset.range (horizon + 1)).sum stabilityTerm +
            2 / eta 0 * refinedMass 0 +
            (Finset.range horizon).sum (fun t =>
              2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1)) := by
      calc
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
            arms harms eta loss (pointMass best) horizon) <=
          integral mu (fun sample =>
              (Finset.range (horizon + 1)).sum (fun t =>
                sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
                  arms harms eta sample t)) +
            2 / eta 0 * refinedMass 0 +
            (Finset.range horizon).sum (fun t =>
              2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1)) := by
                simpa [refinedMass, mu, selector] using hregret
        _ <= (Finset.range (horizon + 1)).sum stabilityTerm +
            2 / eta 0 * refinedMass 0 +
            (Finset.range horizon).sum (fun t =>
              2 * (1 / eta (t + 1) - 1 / eta t) * refinedMass (t + 1)) := by
                have hs :
                    integral mu (fun sample =>
                        (Finset.range (horizon + 1)).sum (fun t =>
                          sampledScheduledHalfTsallisAllRatePotentialStabilityBoundAtTime
                            arms harms eta sample t)) <=
                      (Finset.range (horizon + 1)).sum stabilityTerm := by
                  simpa [stabilityTerm, sqrtMass, mu, selector] using hstability
                linarith
    linarith
  have hsuccessor :
      (Finset.range horizon).sum (fun t => stabilityTerm (t + 1)) +
          (Finset.range horizon).sum penaltyIncrement =
        (Finset.range horizon).sum (fun t =>
          baseTerm (t + 1) + coefficientTerm (t + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    unfold baseTerm coefficientTerm
    simp [sampledScheduledHalfTsallisRefinedCoefficient]
    ring
  have hrearrange :
      (Finset.range (horizon + 1)).sum stabilityTerm +
          2 / eta 0 * sqrtMass 0 +
          (Finset.range horizon).sum penaltyIncrement =
        (Finset.range (horizon + 1)).sum baseTerm +
          (Finset.range (horizon + 1)).sum coefficientTerm := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ',
      Finset.sum_range_succ']
    calc
      (Finset.range horizon).sum (fun t => stabilityTerm (t + 1)) +
            stabilityTerm 0 + 2 / eta 0 * sqrtMass 0 +
          (Finset.range horizon).sum penaltyIncrement =
        ((Finset.range horizon).sum (fun t => stabilityTerm (t + 1)) +
          (Finset.range horizon).sum penaltyIncrement) +
            (stabilityTerm 0 + 2 / eta 0 * sqrtMass 0) := by ring
      _ = (Finset.range horizon).sum (fun t =>
            baseTerm (t + 1) + coefficientTerm (t + 1)) +
          (baseTerm 0 + coefficientTerm 0) := by
        rw [hsuccessor]
        unfold stabilityTerm baseTerm coefficientTerm
        simp [sampledScheduledHalfTsallisRefinedCoefficient]
        ring
      _ = (Finset.range horizon).sum (fun t => baseTerm (t + 1)) +
            baseTerm 0 +
          ((Finset.range horizon).sum (fun t => coefficientTerm (t + 1)) +
            coefficientTerm 0) := by
        rw [Finset.sum_add_distrib]
        ring
  rw [hrearrange] at hcombined
  simpa [baseTerm, coefficientTerm, sqrtMass, mu, selector] using hcombined

/-- The combined refined scheduled upper bound consumes any matching expected
self-bounding law and yields a squared-coefficient-over-gap theorem. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty_of_selfBounding
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
    (corruption : Real)
    (hselfBounding :
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
          arms harms eta loss (pointMass best) horizon)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) <=
      2 * (Finset.range (horizon + 1)).sum (fun t => 2 * (eta t) ^ 2) +
      ((Finset.range (horizon + 1)).product (arms.erase best)).sum
        (fun index =>
          (sampledScheduledHalfTsallisRefinedCoefficient eta index.1) ^ 2 /
            gap index.2) +
      corruption := by
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let probability := fun t =>
    sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t
  let indices := (Finset.range (horizon + 1)).product (arms.erase best)
  let regret := integral mu
    (sampledScheduledHalfTsallisPredictableEnvironmentRegret
      arms harms eta loss (pointMass best) horizon)
  let base := (Finset.range (horizon + 1)).sum (fun t => 2 * (eta t) ^ 2)
  haveI : IsProbabilityMeasure mu := inferInstance
  have hupperBase :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty
      prior arms harms eta loss hbest horizon heta heta_le hetaMono
  dsimp only at hupperBase
  have hupper :
      regret <= base + indices.sum (fun index =>
        sampledScheduledHalfTsallisRefinedCoefficient eta index.1 *
          Real.sqrt (probability index.1 index.2)) := by
    simpa [regret, base, indices, probability,
      sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt,
      Finset.sum_product, mu, selector, Finset.mul_sum] using hupperBase
  have hprobability : ∀ index ∈ indices,
      0 <= probability index.1 index.2 := by
    intro index hindex
    have htime : index.1 ∈ Finset.range (horizon + 1) :=
      (Finset.mem_product.mp hindex).1
    have haction : index.2 ∈ arms.erase best :=
      (Finset.mem_product.mp hindex).2
    exact
      (finiteSimplex_sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta index.1).1 index.2
          (Finset.mem_of_mem_erase haction)
  have hgapIndex : ∀ index ∈ indices, 0 < gap index.2 := by
    intro index hindex
    exact hgapPos index.2 (Finset.mem_product.mp hindex).2
  dsimp only at hselfBounding
  have hselfBounding' :
      indices.sum (fun index => gap index.2 * probability index.1 index.2) -
          corruption <= regret := by
    simpa [indices, probability, regret, Finset.sum_product, mu, selector] using
      hselfBounding
  have hfinal := regret_le_two_mul_base_add_sum_sq_div_gap_add_corruption
    indices
    (fun index => probability index.1 index.2)
    (fun index => sampledScheduledHalfTsallisRefinedCoefficient eta index.1)
    (fun index => gap index.2)
    regret base corruption hprobability hgapIndex hselfBounding' hupper
  simpa [indices, regret, base, probability, mu, selector] using hfinal

/-- Under an exact predictable fixed-gap law, the combined refined scheduled
upper bound automatically yields a squared-coefficient-over-gap theorem. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty_of_fixedGap
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
      2 * (Finset.range (horizon + 1)).sum (fun t => 2 * (eta t) ^ 2) +
      ((Finset.range (horizon + 1)).product (arms.erase best)).sum
        (fun index =>
          (sampledScheduledHalfTsallisRefinedCoefficient eta index.1) ^ 2 /
            gap index.2) +
      corruption := by
  apply
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty_of_selfBounding
      prior arms harms eta loss hbest horizon heta heta_le hetaMono gap hgapPos
        corruption
  exact
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_fixedGap
      prior arms harms eta loss hbest gap horizon hgapLaw corruption hcorruption

/-- A coordinatewise expected-gap law supplies the refined scheduled
squared-coefficient-over-gap theorem without a samplewise fixed-gap premise. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty_of_expectedGapLaw
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
    (hgapLaw :
      let selector :=
        canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
          arms harms eta loss
      let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms eta selector.finiteHistory loss.environment
      HasScheduledExpectedGapLaw
        mu arms harms eta loss best gap horizon)
    (corruption : Real) (hcorruption : 0 <= corruption) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms eta loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms eta selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) <=
      2 * (Finset.range (horizon + 1)).sum (fun t => 2 * (eta t) ^ 2) +
      ((Finset.range (horizon + 1)).product (arms.erase best)).sum
        (fun index =>
          (sampledScheduledHalfTsallisRefinedCoefficient eta index.1) ^ 2 /
            gap index.2) +
      corruption := by
  dsimp only at hgapLaw ⊢
  apply
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty_of_selfBounding
      prior arms harms eta loss hbest horizon heta heta_le hetaMono gap hgapPos
        corruption
  exact
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_expectedGapLaw
      _ arms harms eta loss hbest gap horizon hgapLaw corruption hcorruption

end Tsallis
end BanditRLProof
