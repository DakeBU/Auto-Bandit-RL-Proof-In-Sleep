import BanditRLProof.TsallisScheduledRefinedStabilityPenalty
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Square-root schedule fixed-gap bound for half-Tsallis FTRL

This module instantiates the scheduled refined stability-penalty theorem with
`eta t = 1 / (2 * sqrt (t + 1))`.  The schedule contracts and its unified
coefficient are bounded explicitly before the fixed-gap theorem is consumed.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- The concrete small-rate schedule used by the fixed-gap route. -/
noncomputable def sampledScheduledHalfTsallisSqrtSchedule (t : Nat) : Real :=
  1 / (2 * Real.sqrt (((t + 1 : Nat) : Real)))

/-- The finite harmonic budget through the inclusive horizon. -/
noncomputable def sampledScheduledHalfTsallisHarmonicBudget
    (horizon : Nat) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    1 / (((t + 1 : Nat) : Real)))

/-- The local real-valued budget is the real cast of Mathlib's rational
harmonic number. -/
theorem sampledScheduledHalfTsallisHarmonicBudget_eq_harmonic
    (horizon : Nat) :
    sampledScheduledHalfTsallisHarmonicBudget horizon =
      (harmonic (horizon + 1) : Real) := by
  unfold sampledScheduledHalfTsallisHarmonicBudget harmonic
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Rat.cast_inv, Rat.cast_natCast]
  norm_num

/-- Mathlib's finite harmonic estimate gives the explicit logarithmic budget. -/
theorem sampledScheduledHalfTsallisHarmonicBudget_le_one_add_log
    (horizon : Nat) :
    sampledScheduledHalfTsallisHarmonicBudget horizon <=
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  rw [sampledScheduledHalfTsallisHarmonicBudget_eq_harmonic]
  exact harmonic_le_one_add_log (horizon + 1)

theorem sampledScheduledHalfTsallisSqrtSchedule_pos (t : Nat) :
    0 < sampledScheduledHalfTsallisSqrtSchedule t := by
  unfold sampledScheduledHalfTsallisSqrtSchedule
  positivity

theorem sampledScheduledHalfTsallisSqrtSchedule_le_half (t : Nat) :
    sampledScheduledHalfTsallisSqrtSchedule t <= 1 / 2 := by
  unfold sampledScheduledHalfTsallisSqrtSchedule
  have hsqrt :
      1 <= Real.sqrt (((t + 1 : Nat) : Real)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  exact one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2)
    (by nlinarith)

theorem sampledScheduledHalfTsallisSqrtSchedule_succ_le (t : Nat) :
    sampledScheduledHalfTsallisSqrtSchedule (t + 1) <=
      sampledScheduledHalfTsallisSqrtSchedule t := by
  unfold sampledScheduledHalfTsallisSqrtSchedule
  have hsqrt :
      Real.sqrt (((t + 1 : Nat) : Real)) <=
        Real.sqrt (((t + 2 : Nat) : Real)) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hdenom :
      2 * Real.sqrt (((t + 1 : Nat) : Real)) <=
        2 * Real.sqrt (((t + 2 : Nat) : Real)) := by
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) (by simpa [Nat.add_assoc] using hdenom)

theorem sampledScheduledHalfTsallisSqrtSchedule_four_mul_sq (t : Nat) :
    4 * (sampledScheduledHalfTsallisSqrtSchedule t) ^ 2 =
      1 / (((t + 1 : Nat) : Real)) := by
  unfold sampledScheduledHalfTsallisSqrtSchedule
  have hnonneg : 0 <= (((t + 1 : Nat) : Real)) := by positivity
  have hcastPos : 0 < (((t + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.zero_lt_succ t
  have hsqrt_ne : Real.sqrt (((t + 1 : Nat) : Real)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcastPos)
  rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hnonneg]
  field_simp
  ring

private theorem sqrt_succ_sub_sqrt_le_one_div_sqrt_succ (t : Nat) :
    Real.sqrt (((t + 2 : Nat) : Real)) -
        Real.sqrt (((t + 1 : Nat) : Real)) <=
      1 / Real.sqrt (((t + 2 : Nat) : Real)) := by
  let x := Real.sqrt (((t + 1 : Nat) : Real))
  let y := Real.sqrt (((t + 2 : Nat) : Real))
  have hx : 0 <= x := Real.sqrt_nonneg _
  have hy : 0 < y := Real.sqrt_pos.2 (by positivity)
  have hxy : x <= y := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hxx : x ^ 2 = (((t + 1 : Nat) : Real)) := by
    exact Real.sq_sqrt (by positivity)
  have hyy : y ^ 2 = (((t + 2 : Nat) : Real)) := by
    exact Real.sq_sqrt (by positivity)
  have hprod : x ^ 2 <= x * y := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hxy)]
  apply (le_div_iff₀ hy).2
  change (y - x) * y <= 1
  have hcast : (((t + 2 : Nat) : Real)) =
      (((t + 1 : Nat) : Real)) + 1 := by
    push_cast
    ring
  nlinarith [hprod]

theorem sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_nonneg
    (t : Nat) :
    0 <= sampledScheduledHalfTsallisRefinedCoefficient
      sampledScheduledHalfTsallisSqrtSchedule t := by
  cases t with
  | zero =>
      norm_num [sampledScheduledHalfTsallisRefinedCoefficient,
        sampledScheduledHalfTsallisSqrtSchedule]
  | succ t =>
      simp only [sampledScheduledHalfTsallisRefinedCoefficient]
      have hetaPos := sampledScheduledHalfTsallisSqrtSchedule_pos
      have hmono := sampledScheduledHalfTsallisSqrtSchedule_succ_le t
      have hreciprocal := one_div_le_one_div_of_le (hetaPos (t + 1)) hmono
      exact add_nonneg (mul_nonneg (by norm_num) (le_of_lt (hetaPos (t + 1))))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hreciprocal))

theorem sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_le
    (t : Nat) :
    sampledScheduledHalfTsallisRefinedCoefficient
        sampledScheduledHalfTsallisSqrtSchedule t <=
      5 / Real.sqrt (((t + 1 : Nat) : Real)) := by
  cases t with
  | zero =>
      norm_num [sampledScheduledHalfTsallisRefinedCoefficient,
        sampledScheduledHalfTsallisSqrtSchedule]
  | succ t =>
      have hxpos : 0 < (((t + 1 : Nat) : Real)) := by
        exact_mod_cast Nat.zero_lt_succ t
      have hypos : 0 < (((t + 2 : Nat) : Real)) := by
        positivity
      have hxne : Real.sqrt (((t + 1 : Nat) : Real)) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hxpos)
      have hyne : Real.sqrt (((t + 2 : Nat) : Real)) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hypos)
      have hdiff := sqrt_succ_sub_sqrt_le_one_div_sqrt_succ t
      simp only [sampledScheduledHalfTsallisRefinedCoefficient]
      unfold sampledScheduledHalfTsallisSqrtSchedule
      field_simp [hxne, hyne] at hdiff ⊢
      nlinarith

theorem sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_sq_le
    (t : Nat) :
    (sampledScheduledHalfTsallisRefinedCoefficient
        sampledScheduledHalfTsallisSqrtSchedule t) ^ 2 <=
      25 / (((t + 1 : Nat) : Real)) := by
  have hnonneg :=
    sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_nonneg t
  have hupper :=
    sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_le t
  have hsqrtNonneg :
      0 <= Real.sqrt (((t + 1 : Nat) : Real)) := Real.sqrt_nonneg _
  have hsqrtSq :
      (Real.sqrt (((t + 1 : Nat) : Real))) ^ 2 =
        (((t + 1 : Nat) : Real)) := Real.sq_sqrt (by positivity)
  have hboundNonneg :
      0 <= 5 / Real.sqrt (((t + 1 : Nat) : Real)) := by positivity
  have hsq := (sq_le_sq₀ hnonneg hboundNonneg).2 hupper
  rw [div_pow, hsqrtSq] at hsq
  norm_num at hsq ⊢
  exact hsq

/-- The square-root schedule closes any matching self-bounding route with a
finite harmonic budget and an explicit reciprocal-gap factor. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_of_selfBounding
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
    (corruption : Real)
    (hselfBounding :
      let selector :=
        canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
      let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
        arms harms sampledScheduledHalfTsallisSqrtSchedule
          selector.finiteHistory loss.environment
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase best).sum (fun action =>
            gap action * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms sampledScheduledHalfTsallisSqrtSchedule
                t action)) - corruption <=
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
            (pointMass best) horizon)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule
        selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      sampledScheduledHalfTsallisHarmonicBudget horizon *
        (1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)) +
      corruption := by
  dsimp only
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let times := Finset.range (horizon + 1)
  let suboptimal := arms.erase best
  let harmonic := sampledScheduledHalfTsallisHarmonicBudget horizon
  let gapBudget := suboptimal.sum (fun action => 1 / gap action)
  let regret := integral mu
    (sampledScheduledHalfTsallisPredictableEnvironmentRegret
      arms harms eta loss (pointMass best) horizon)
  dsimp only at hselfBounding
  have habstract :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedStabilityPenalty_of_selfBounding
      prior arms harms eta loss hbest horizon
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_pos t)
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_le_half t)
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_succ_le t)
      gap hgapPos corruption (by
        simpa [eta, mu, selector] using hselfBounding)
  dsimp only at habstract
  have hbase :
      2 * times.sum (fun t => 2 * (eta t) ^ 2) = harmonic := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hfour := sampledScheduledHalfTsallisSqrtSchedule_four_mul_sq t
    change 2 * (2 * (sampledScheduledHalfTsallisSqrtSchedule t) ^ 2) =
      1 / (((t + 1 : Nat) : Real))
    nlinarith [hfour]
  have hpenalty :
      (times.product suboptimal).sum (fun index =>
          (sampledScheduledHalfTsallisRefinedCoefficient eta index.1) ^ 2 /
            gap index.2) <=
        harmonic * (25 * gapBudget) := by
    calc
      (times.product suboptimal).sum (fun index =>
          (sampledScheduledHalfTsallisRefinedCoefficient eta index.1) ^ 2 /
            gap index.2) =
          times.sum (fun t => suboptimal.sum (fun action =>
            (sampledScheduledHalfTsallisRefinedCoefficient eta t) ^ 2 /
              gap action)) :=
        Finset.sum_product times suboptimal _
      _ <= times.sum (fun t => suboptimal.sum (fun action =>
            (25 / (((t + 1 : Nat) : Real))) / gap action)) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro action haction
        exact (div_le_div_iff_of_pos_right
          (hgapPos action (by simpa [suboptimal] using haction))).2
          (by simpa [eta] using
            sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_sq_le t)
      _ = times.sum (fun t =>
          (1 / (((t + 1 : Nat) : Real))) * (25 * gapBudget)) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [gapBudget]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro action haction
        ring
      _ = harmonic * (25 * gapBudget) := by
        rw [← Finset.sum_mul]
        rfl
  calc
    regret <=
        2 * times.sum (fun t => 2 * (eta t) ^ 2) +
          (times.product suboptimal).sum (fun index =>
            (sampledScheduledHalfTsallisRefinedCoefficient eta index.1) ^ 2 /
              gap index.2) + corruption := by
      simpa [regret, times, suboptimal, eta, mu, selector] using habstract
    _ <= harmonic + harmonic * (25 * gapBudget) + corruption := by
      rw [hbase]
      gcongr
    _ = harmonic * (1 + 25 * gapBudget) + corruption := by ring
    _ = sampledScheduledHalfTsallisHarmonicBudget horizon *
          (1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)) +
        corruption := by
      rfl

/-- The square-root schedule closes the exact fixed-gap route with a finite
harmonic budget and an explicit reciprocal-gap factor. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_fixedGap
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
    (hgapLaw : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action)
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
      sampledScheduledHalfTsallisHarmonicBudget horizon *
        (1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)) +
      corruption := by
  apply
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_of_selfBounding
      prior arms harms loss hbest horizon gap hgapPos corruption
  exact
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_fixedGap
      prior arms harms sampledScheduledHalfTsallisSqrtSchedule loss hbest gap
        horizon hgapLaw corruption hcorruption

/-- The square-root schedule also closes a coordinatewise expected-gap law;
no samplewise fixed-gap identity is required. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_expectedGap
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
      HasScheduledExpectedGapLaw mu arms harms
        sampledScheduledHalfTsallisSqrtSchedule loss best gap horizon)
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
      sampledScheduledHalfTsallisHarmonicBudget horizon *
        (1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)) +
      corruption := by
  dsimp only at hgapLaw ⊢
  apply
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_of_selfBounding
      prior arms harms loss hbest horizon gap hgapPos corruption
  exact
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_expectedGapLaw
      _ arms harms sampledScheduledHalfTsallisSqrtSchedule loss hbest gap
        horizon hgapLaw corruption hcorruption

/-- The concrete square-root schedule has an explicit logarithmic fixed-gap
regret bound, obtained from Mathlib's finite harmonic estimate. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_fixedGap
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
    (hgapLaw : ∀ t sample action, action ∈ arms ->
      Exp3.predictableLossAt loss t sample action -
        Exp3.predictableLossAt loss t sample best = gap action)
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
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  let gapFactor :=
    1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)
  have hregret :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_fixedGap
      prior arms harms loss hbest horizon gap hgapPos hgapLaw
        corruption hcorruption
  dsimp only at hregret
  have hgapSum :
      0 <= (arms.erase best).sum (fun action => 1 / gap action) := by
    apply Finset.sum_nonneg
    intro action haction
    exact le_of_lt (one_div_pos.mpr (hgapPos action haction))
  have hgapFactor : 0 <= gapFactor := by
    dsimp [gapFactor]
    nlinarith
  have hbudget :=
    sampledScheduledHalfTsallisHarmonicBudget_le_one_add_log horizon
  have hmul :
      sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor <=
        (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor :=
    mul_le_mul_of_nonneg_right hbudget hgapFactor
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor +
        corruption := by
      simpa [mu, selector, gapFactor] using hregret
    _ <= (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor +
        corruption := by
      nlinarith [hmul]
    _ = (1 + Real.log (((horizon + 1 : Nat) : Real))) *
          (1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)) +
        corruption := by
      rfl

/-- Mathlib's harmonic estimate turns the coordinatewise expected-gap route
into the same explicit logarithmic square-root-schedule bound. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_expectedGap
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
      HasScheduledExpectedGapLaw mu arms harms
        sampledScheduledHalfTsallisSqrtSchedule loss best gap horizon)
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
  let gapFactor :=
    1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)
  have hregret :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_expectedGap
      prior arms harms loss hbest horizon gap hgapPos hgapLaw
        corruption hcorruption
  dsimp only at hregret
  have hgapSum :
      0 <= (arms.erase best).sum (fun action => 1 / gap action) := by
    apply Finset.sum_nonneg
    intro action haction
    exact le_of_lt (one_div_pos.mpr (hgapPos action haction))
  have hgapFactor : 0 <= gapFactor := by
    dsimp [gapFactor]
    nlinarith
  have hbudget :=
    sampledScheduledHalfTsallisHarmonicBudget_le_one_add_log horizon
  have hmul :
      sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor <=
        (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor :=
    mul_le_mul_of_nonneg_right hbudget hgapFactor
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor +
        corruption := by
      simpa [mu, selector, gapFactor] using hregret
    _ <= (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor +
        corruption := by
      nlinarith [hmul]
    _ = (1 + Real.log (((horizon + 1 : Nat) : Real))) *
          (1 + 25 * (arms.erase best).sum (fun action => 1 / gap action)) +
        corruption := by
      rfl

end Tsallis
end BanditRLProof
