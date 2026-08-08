import BanditRLProof.TsallisConstrainedQuadraticOptimization
import BanditRLProof.TsallisScheduledRefinedStabilityPenalty

/-!
# Scheduled self-bounding quadratic optimization

This module consumes the terminal lambda interpolation and the two one-round
quadratic branches. It partitions a finite time set by the exact active-mass
threshold, then exposes the resulting deterministic scalar sums to the
remaining schedule and lambda optimization.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Split a finite collection of generated expected-probability quadratic
terms at the exact active-mass threshold. The active times use the simplex
mass constraint; all other times use coordinatewise completion of squares. -/
theorem sum_sampledScheduledHalfTsallisExpectedProbability_le_quadraticFilterSplit
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat → Real)
    (times : Finset Nat) {best : Action} (hbest : best ∈ arms)
    (gap : Action → Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (b : Nat → Real) (lambda : Real) (hlambda : 0 < lambda) :
    times.sum (fun t =>
        (arms.erase best).sum (fun action =>
          b t * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action) -
          lambda * gap action *
            sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) ≤
      (times.filter fun t =>
          2 * Real.sqrt ((arms.erase best).card : Real) ≤
            b t * (arms.erase best).sum (fun action =>
              1 / (lambda * gap action))).sum (fun t =>
        b t * Real.sqrt ((arms.erase best).card : Real) -
          (arms.erase best).card /
            (arms.erase best).sum (fun action =>
              1 / (lambda * gap action))) +
      (times.filter fun t => ¬
          2 * Real.sqrt ((arms.erase best).card : Real) ≤
            b t * (arms.erase best).sum (fun action =>
              1 / (lambda * gap action))).sum (fun t =>
        (b t) ^ 2 / 4 * (arms.erase best).sum (fun action =>
          1 / (lambda * gap action))) := by
  classical
  let active : Nat → Prop := fun t =>
    2 * Real.sqrt ((arms.erase best).card : Real) ≤
      b t * (arms.erase best).sum (fun action =>
        1 / (lambda * gap action))
  let roundTerm : Nat → Real := fun t =>
    (arms.erase best).sum (fun action =>
      b t * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t action) -
      lambda * gap action *
        sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action)
  have hactive :
      (times.filter active).sum roundTerm ≤
        (times.filter active).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card /
              (arms.erase best).sum (fun action =>
                1 / (lambda * gap action))) := by
    apply Finset.sum_le_sum
    intro t ht
    exact sampledScheduledHalfTsallisExpectedProbability_sum_le_of_threshold
      mu arms harms eta t hbest gap hsuboptimal hgap (b t) lambda hlambda
        (Finset.mem_filter.mp ht).2
  have hinactive :
      (times.filter fun t => ¬ active t).sum roundTerm ≤
        (times.filter fun t => ¬ active t).sum (fun t =>
          (b t) ^ 2 / 4 * (arms.erase best).sum (fun action =>
            1 / (lambda * gap action))) := by
    apply Finset.sum_le_sum
    intro t ht
    exact sampledScheduledHalfTsallisExpectedProbability_sum_le_unconstrained
      mu arms harms eta t gap hgap (b t) lambda hlambda
  calc
    times.sum (fun t =>
        (arms.erase best).sum (fun action =>
          b t * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action) -
          lambda * gap action *
            sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) =
        (times.filter active).sum roundTerm +
          (times.filter fun t => ¬ active t).sum roundTerm := by
      simpa [active, roundTerm] using
        (Finset.sum_filter_add_sum_filter_not times active roundTerm).symm
    _ ≤
        (times.filter active).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card /
              (arms.erase best).sum (fun action =>
                1 / (lambda * gap action))) +
        (times.filter fun t => ¬ active t).sum (fun t =>
          (b t) ^ 2 / 4 * (arms.erase best).sum (fun action =>
            1 / (lambda * gap action))) := add_le_add hactive hinactive
    _ = _ := by rfl

/-- Prefix/suffix form of the one-round split. A caller supplies a cutoff and
proves the active threshold only on its prefix; the suffix always admits the
unconstrained branch. -/
theorem sum_range_sampledScheduledHalfTsallisExpectedProbability_le_quadraticPrefixSplit
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat → Real)
    (n cutoff : Nat) (hcutoff : cutoff ≤ n)
    {best : Action} (hbest : best ∈ arms) (gap : Action → Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (b : Nat → Real) (lambda : Real) (hlambda : 0 < lambda)
    (hthreshold : ∀ t < cutoff,
      2 * Real.sqrt ((arms.erase best).card : Real) ≤
        b t * (arms.erase best).sum (fun action =>
          1 / (lambda * gap action))) :
    (Finset.range n).sum (fun t =>
        (arms.erase best).sum (fun action =>
          b t * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action) -
          lambda * gap action *
            sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) ≤
      (Finset.range cutoff).sum (fun t =>
        b t * Real.sqrt ((arms.erase best).card : Real) -
          (arms.erase best).card /
            (arms.erase best).sum (fun action =>
              1 / (lambda * gap action))) +
      (Finset.Ico cutoff n).sum (fun t =>
        (b t) ^ 2 / 4 * (arms.erase best).sum (fun action =>
          1 / (lambda * gap action))) := by
  let roundTerm : Nat → Real := fun t =>
    (arms.erase best).sum (fun action =>
      b t * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
        mu arms harms eta t action) -
      lambda * gap action *
        sampledScheduledHalfTsallisExpectedProbabilityAt
          mu arms harms eta t action)
  have hprefix :
      (Finset.range cutoff).sum roundTerm ≤
        (Finset.range cutoff).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card /
              (arms.erase best).sum (fun action =>
                1 / (lambda * gap action))) := by
    apply Finset.sum_le_sum
    intro t ht
    exact sampledScheduledHalfTsallisExpectedProbability_sum_le_of_threshold
      mu arms harms eta t hbest gap hsuboptimal hgap (b t) lambda hlambda
        (hthreshold t (Finset.mem_range.mp ht))
  have hsuffix :
      (Finset.Ico cutoff n).sum roundTerm ≤
        (Finset.Ico cutoff n).sum (fun t =>
          (b t) ^ 2 / 4 * (arms.erase best).sum (fun action =>
            1 / (lambda * gap action))) := by
    apply Finset.sum_le_sum
    intro t ht
    exact sampledScheduledHalfTsallisExpectedProbability_sum_le_unconstrained
      mu arms harms eta t gap hgap (b t) lambda hlambda
  calc
    (Finset.range n).sum (fun t =>
        (arms.erase best).sum (fun action =>
          b t * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
            mu arms harms eta t action) -
          lambda * gap action *
            sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action)) =
        (Finset.range cutoff).sum roundTerm +
          (Finset.Ico cutoff n).sum roundTerm := by
      simpa [roundTerm] using
        (Finset.sum_range_add_sum_Ico roundTerm hcutoff).symm
    _ ≤ _ := add_le_add hprefix hsuffix

/-- The generated scheduled regret theorem after terminal self-bounding and
the exact finite-time quadratic branch split. All probabilistic, conditional
law, Jensen, and finite-simplex obligations have been discharged; the
remaining right-hand side is deterministic schedule algebra. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_selfBoundingQuadraticSplit
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
    (gap : Action → Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption lambda : Real) (hlambda : lambda ∈ Set.Ioc (0 : Real) 1)
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
    let times := Finset.range (horizon + 1)
    let reciprocalGap := (arms.erase best).sum (fun action =>
      1 / (lambda * gap action))
    let b := fun t => 2 * (1 + lambda) * eta t
    let active := fun t =>
      2 * Real.sqrt ((arms.erase best).card : Real) ≤
        b t * reciprocalGap
    let base := times.sum (fun t => 2 * (eta t) ^ 2) +
      (halfTsallisPotentialMass arms
          (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
        1 / eta horizon)
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) ≤
      (1 + lambda) * base + lambda * corruption +
        (times.filter active).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) +
        (times.filter fun t => ¬ active t).sum (fun t =>
          (b t) ^ 2 / 4 * reciprocalGap) := by
  classical
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let times := Finset.range (horizon + 1)
  let probability := fun t action =>
    sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action
  let reciprocalGap := (arms.erase best).sum (fun action =>
    1 / (lambda * gap action))
  let b := fun t => 2 * (1 + lambda) * eta t
  let active := fun t =>
    2 * Real.sqrt ((arms.erase best).card : Real) ≤
      b t * reciprocalGap
  let base := times.sum (fun t => 2 * (eta t) ^ 2) +
    (halfTsallisPotentialMass arms
        (initialHalfTsallisDistribution arms harms (eta 0)) / eta horizon -
      1 / eta horizon)
  let regret := integral mu
    (sampledScheduledHalfTsallisPredictableEnvironmentRegret
      arms harms eta loss (pointMass best) horizon)
  let stability := times.sum (fun t =>
    2 * eta t * (arms.erase best).sum (fun action =>
      Real.sqrt (probability t action)))
  let gapMass := times.sum (fun t =>
    (arms.erase best).sum (fun action =>
      gap action * probability t action))
  let roundTerm := fun t =>
    (arms.erase best).sum (fun action =>
      b t * Real.sqrt (probability t action) -
        lambda * gap action * probability t action)
  have hlambdaIcc : lambda ∈ Set.Icc (0 : Real) 1 :=
    ⟨le_of_lt hlambda.1, hlambda.2⟩
  have hinterpolation :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_selfBoundingInterpolation
      prior arms harms eta loss hbest horizon heta heta_le hetaMono gap
        corruption lambda hlambdaIcc hselfBounding
  dsimp only at hinterpolation
  have hupperEq :
      times.sum (fun t =>
          2 * eta t * (arms.erase best).sum (fun action =>
            Real.sqrt (probability t action)) + 2 * (eta t) ^ 2) +
          halfTsallisPotentialMass arms
              (initialHalfTsallisDistribution arms harms (eta 0)) /
            eta horizon - 1 / eta horizon =
        stability + base := by
    simp [stability, base, Finset.sum_add_distrib]
    ring
  have hround :
      times.sum roundTerm =
        (1 + lambda) * stability - lambda * gapMass := by
    calc
      times.sum roundTerm = times.sum (fun t =>
          (1 + lambda) *
              (2 * eta t * (arms.erase best).sum (fun action =>
                Real.sqrt (probability t action))) -
            lambda * (arms.erase best).sum (fun action =>
              gap action * probability t action)) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [roundTerm]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hgapScale :
            (arms.erase best).sum (fun action =>
                lambda * gap action * probability t action) =
              lambda * (arms.erase best).sum (fun action =>
                gap action * probability t action) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro action haction
          ring
        rw [hgapScale]
        dsimp [b]
        ring
      _ = (1 + lambda) * stability - lambda * gapMass := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have hpre :
      regret ≤ (1 + lambda) * base + lambda * corruption +
        times.sum roundTerm := by
    calc
      regret ≤
          (1 + lambda) *
              (times.sum (fun t =>
                  2 * eta t * (arms.erase best).sum (fun action =>
                    Real.sqrt (probability t action)) +
                    2 * (eta t) ^ 2) +
                halfTsallisPotentialMass arms
                    (initialHalfTsallisDistribution arms harms (eta 0)) /
                  eta horizon - 1 / eta horizon) -
            lambda * times.sum (fun t =>
              (arms.erase best).sum (fun action =>
                gap action * probability t action)) +
            lambda * corruption := by
        simpa [regret, times, probability, mu, selector] using hinterpolation
      _ = (1 + lambda) * (stability + base) -
          lambda * gapMass + lambda * corruption := by
        rw [hupperEq]
      _ = (1 + lambda) * base + lambda * corruption +
          times.sum roundTerm := by rw [hround]; ring
  have hsplit :
      times.sum roundTerm ≤
        (times.filter active).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) +
        (times.filter fun t => ¬ active t).sum (fun t =>
          (b t) ^ 2 / 4 * reciprocalGap) := by
    simpa [roundTerm, probability, active, b, reciprocalGap] using
      (sum_sampledScheduledHalfTsallisExpectedProbability_le_quadraticFilterSplit
        mu arms harms eta times hbest gap hsuboptimal hgap b lambda hlambda.1)
  linarith

/-- Refined generated interpolation with any deterministic coefficient
envelope `b`. This is the common pre-split surface for filter and prefix
quadratic consumers. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedSelfBoundingQuadraticSum_of_refinedCoefficient_le
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
    (hlambda : lambda ∈ Set.Ioc (0 : Real) 1)
    (b : Nat → Real)
    (hb : ∀ t, t ≤ horizon →
      (1 + lambda) * sampledScheduledHalfTsallisRefinedCoefficient eta t ≤
        b t)
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
    let times := Finset.range (horizon + 1)
    let base := times.sum (fun t => 2 * (eta t) ^ 2)
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) ≤
      (1 + lambda) * base + lambda * corruption +
        times.sum (fun t =>
          (arms.erase best).sum (fun action =>
            b t * Real.sqrt (sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t action) -
            lambda * gap action *
              sampledScheduledHalfTsallisExpectedProbabilityAt
                mu arms harms eta t action)) := by
  classical
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let times := Finset.range (horizon + 1)
  let probability := fun t action =>
    sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action
  let coefficient := sampledScheduledHalfTsallisRefinedCoefficient eta
  let base := times.sum (fun t => 2 * (eta t) ^ 2)
  let regret := integral mu
    (sampledScheduledHalfTsallisPredictableEnvironmentRegret
      arms harms eta loss (pointMass best) horizon)
  let stability := times.sum (fun t =>
    coefficient t * (arms.erase best).sum (fun action =>
      Real.sqrt (probability t action)))
  let gapMass := times.sum (fun t =>
    (arms.erase best).sum (fun action =>
      gap action * probability t action))
  let upper := base + stability
  let exactRoundTerm := fun t =>
    (arms.erase best).sum (fun action =>
      (1 + lambda) * coefficient t * Real.sqrt (probability t action) -
        lambda * gap action * probability t action)
  let roundTerm := fun t =>
    (arms.erase best).sum (fun action =>
      b t * Real.sqrt (probability t action) -
        lambda * gap action * probability t action)
  have hupperRaw :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty
      prior arms harms eta loss hbest horizon heta heta_le hetaMono
  dsimp only at hupperRaw
  have hupper : regret ≤ upper := by
    simpa [regret, upper, base, stability, coefficient, times, probability,
      sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt, mu, selector]
      using hupperRaw
  have hselfBounding' : gapMass - corruption ≤ regret := by
    simpa [gapMass, regret, times, probability, mu, selector] using
      hselfBounding
  have hlambdaIcc : lambda ∈ Set.Icc (0 : Real) 1 :=
    ⟨le_of_lt hlambda.1, hlambda.2⟩
  have hinterpolation := regret_le_selfBoundingInterpolation
    regret upper gapMass corruption lambda hlambdaIcc hupper hselfBounding'
  have hround :
      times.sum exactRoundTerm =
        (1 + lambda) * stability - lambda * gapMass := by
    calc
      times.sum exactRoundTerm = times.sum (fun t =>
          (1 + lambda) *
              (coefficient t * (arms.erase best).sum (fun action =>
                Real.sqrt (probability t action))) -
            lambda * (arms.erase best).sum (fun action =>
              gap action * probability t action)) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [exactRoundTerm]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hgapScale :
            (arms.erase best).sum (fun action =>
                lambda * gap action * probability t action) =
              lambda * (arms.erase best).sum (fun action =>
                gap action * probability t action) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro action haction
          ring
        rw [hgapScale]
        ring
      _ = (1 + lambda) * stability - lambda * gapMass := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have hpre :
      regret ≤ (1 + lambda) * base + lambda * corruption +
        times.sum exactRoundTerm := by
    calc
      regret ≤ (1 + lambda) * upper - lambda * gapMass +
          lambda * corruption := hinterpolation
      _ = (1 + lambda) * base + lambda * corruption +
          times.sum exactRoundTerm := by
        rw [hround]
        dsimp [upper]
        ring
  have hdom : times.sum exactRoundTerm ≤ times.sum roundTerm := by
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.sum_le_sum
    intro action haction
    have htHorizon : t ≤ horizon := by
      exact Nat.le_of_lt_succ (by
        simpa [times] using Finset.mem_range.mp ht)
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_right (hb t htHorizon) (Real.sqrt_nonneg _)) _
  have hfinal :
      regret ≤ (1 + lambda) * base + lambda * corruption +
        times.sum roundTerm := by
    linarith
  simpa [regret, base, times, roundTerm, probability, mu, selector] using hfinal

/-- Refined generated quadratic split for the theorem route. Unlike the
coarse scheduled interpolation above, this theorem consumes the uncollapsed
stability-penalty coefficient, so its deterministic base contains only
`sum_t 2 * eta_t^2` and no terminal `1 / eta_T` potential term. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedSelfBoundingQuadraticSplit_of_refinedCoefficient_le
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
    (gap : Action → Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption lambda : Real) (hlambda : lambda ∈ Set.Ioc (0 : Real) 1)
    (b : Nat → Real)
    (hb : ∀ t, t ≤ horizon →
      (1 + lambda) * sampledScheduledHalfTsallisRefinedCoefficient eta t ≤
        b t)
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
    let times := Finset.range (horizon + 1)
    let reciprocalGap := (arms.erase best).sum (fun action =>
      1 / (lambda * gap action))
    let active := fun t =>
      2 * Real.sqrt ((arms.erase best).card : Real) ≤
        b t * reciprocalGap
    let base := times.sum (fun t => 2 * (eta t) ^ 2)
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass best) horizon) ≤
      (1 + lambda) * base + lambda * corruption +
        (times.filter active).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) +
        (times.filter fun t => ¬ active t).sum (fun t =>
          (b t) ^ 2 / 4 * reciprocalGap) := by
  classical
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let times := Finset.range (horizon + 1)
  let probability := fun t action =>
    sampledScheduledHalfTsallisExpectedProbabilityAt
      mu arms harms eta t action
  let reciprocalGap := (arms.erase best).sum (fun action =>
    1 / (lambda * gap action))
  let coefficient := sampledScheduledHalfTsallisRefinedCoefficient eta
  let active := fun t =>
    2 * Real.sqrt ((arms.erase best).card : Real) ≤
      b t * reciprocalGap
  let base := times.sum (fun t => 2 * (eta t) ^ 2)
  let regret := integral mu
    (sampledScheduledHalfTsallisPredictableEnvironmentRegret
      arms harms eta loss (pointMass best) horizon)
  let stability := times.sum (fun t =>
    coefficient t * (arms.erase best).sum (fun action =>
      Real.sqrt (probability t action)))
  let gapMass := times.sum (fun t =>
    (arms.erase best).sum (fun action =>
      gap action * probability t action))
  let upper := base + stability
  let exactRoundTerm := fun t =>
    (arms.erase best).sum (fun action =>
      (1 + lambda) * coefficient t * Real.sqrt (probability t action) -
        lambda * gap action * probability t action)
  let roundTerm := fun t =>
    (arms.erase best).sum (fun action =>
      b t * Real.sqrt (probability t action) -
        lambda * gap action * probability t action)
  have hupperRaw :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty
      prior arms harms eta loss hbest horizon heta heta_le hetaMono
  dsimp only at hupperRaw
  have hupper : regret ≤ upper := by
    simpa [regret, upper, base, stability, coefficient, times, probability,
      sampledScheduledHalfTsallisExpectedSuboptimalSqrtMassAt, mu, selector]
      using hupperRaw
  have hselfBounding' : gapMass - corruption ≤ regret := by
    simpa [gapMass, regret, times, probability, mu, selector] using
      hselfBounding
  have hlambdaIcc : lambda ∈ Set.Icc (0 : Real) 1 :=
    ⟨le_of_lt hlambda.1, hlambda.2⟩
  have hinterpolation := regret_le_selfBoundingInterpolation
    regret upper gapMass corruption lambda hlambdaIcc hupper hselfBounding'
  have hround :
      times.sum exactRoundTerm =
        (1 + lambda) * stability - lambda * gapMass := by
    calc
      times.sum exactRoundTerm = times.sum (fun t =>
          (1 + lambda) *
              (coefficient t * (arms.erase best).sum (fun action =>
                Real.sqrt (probability t action))) -
            lambda * (arms.erase best).sum (fun action =>
              gap action * probability t action)) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [exactRoundTerm]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hgapScale :
            (arms.erase best).sum (fun action =>
                lambda * gap action * probability t action) =
              lambda * (arms.erase best).sum (fun action =>
                gap action * probability t action) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro action haction
          ring
        rw [hgapScale]
        ring
      _ = (1 + lambda) * stability - lambda * gapMass := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have hpre :
      regret ≤ (1 + lambda) * base + lambda * corruption +
        times.sum exactRoundTerm := by
    calc
      regret ≤ (1 + lambda) * upper - lambda * gapMass +
          lambda * corruption := hinterpolation
      _ = (1 + lambda) * base + lambda * corruption +
          times.sum exactRoundTerm := by
        rw [hround]
        dsimp [upper]
        ring
  have hdom : times.sum exactRoundTerm ≤ times.sum roundTerm := by
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.sum_le_sum
    intro action haction
    have htHorizon : t ≤ horizon := by
      exact Nat.le_of_lt_succ (by
        simpa [times] using Finset.mem_range.mp ht)
    have hsqrtNonneg : 0 ≤ Real.sqrt (probability t action) :=
      Real.sqrt_nonneg _
    have hcoefficient := hb t htHorizon
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_right hcoefficient hsqrtNonneg) _
  have hpre' :
      regret ≤ (1 + lambda) * base + lambda * corruption +
        times.sum roundTerm := by
    linarith
  have hsplit :
      times.sum roundTerm ≤
        (times.filter active).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) +
        (times.filter fun t => ¬ active t).sum (fun t =>
          (b t) ^ 2 / 4 * reciprocalGap) := by
    simpa [roundTerm, probability, active, reciprocalGap] using
      (sum_sampledScheduledHalfTsallisExpectedProbability_le_quadraticFilterSplit
        mu arms harms eta times hbest gap hsuboptimal hgap b lambda hlambda.1)
  linarith

end Tsallis
end BanditRLProof
