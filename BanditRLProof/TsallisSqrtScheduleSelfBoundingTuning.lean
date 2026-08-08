import BanditRLProof.TsallisSqrtScheduleSelfBoundingOptimization
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Square-root schedule self-bounding tuning

This module removes the caller-supplied cutoff from the refined generated
self-bounding bound.  It floors the continuous active-branch threshold and
records the large-horizon conditions needed to keep that cutoff positive and
inside the finite horizon.  Joint optimization of `lambda` and corruption is
left to a downstream scalar leaf.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- A positive real threshold and its natural floor differ by at most a
factor of two once the threshold is at least one. -/
theorem natFloor_positive_and_half_le
    (q : Real) (hq : 1 <= q) :
    0 < ⌊q⌋₊ ∧
      ((⌊q⌋₊ : Nat) : Real) <= q ∧
      q <= 2 * ((⌊q⌋₊ : Nat) : Real) := by
  have hqNonneg : 0 <= q := zero_le_one.trans hq
  have hfloorPos : 0 < ⌊q⌋₊ := Nat.floor_pos.mpr hq
  have hfloorLe : ((⌊q⌋₊ : Nat) : Real) <= q := Nat.floor_le hqNonneg
  have hqLt : q < ((⌊q⌋₊ : Nat) : Real) + 1 := by
    simpa using (Nat.lt_floor_add_one q)
  have hfloorOne : (1 : Real) <= ((⌊q⌋₊ : Nat) : Real) := by
    exact_mod_cast hfloorPos
  exact ⟨hfloorPos, hfloorLe, by linarith⟩

/-- The continuous threshold whose floor is used for the active-prefix split. -/
noncomputable def sampledScheduledHalfTsallisSelfBoundingThreshold
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (best : Action) (gap : Action -> Real)
    (lambda : Real) : Real :=
  let reciprocalGap := (arms.erase best).sum (fun action =>
    1 / (lambda * gap action))
  let amplitude := 5 * (1 + lambda)
  (amplitude * reciprocalGap /
      (2 * Real.sqrt ((arms.erase best).card : Real))) ^ 2

/-- In the large-horizon branch, flooring the continuous threshold removes the
explicit cutoff from the refined generated-regret theorem. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingFloorCutoff
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption lambda : Real) (hlambda : lambda ∈ Set.Ioc (0 : Real) 1)
    (hthresholdOne :
      1 <= sampledScheduledHalfTsallisSelfBoundingThreshold
        arms best gap lambda)
    (hthresholdHorizon :
      sampledScheduledHalfTsallisSelfBoundingThreshold arms best gap lambda <=
        ((horizon + 1 : Nat) : Real))
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
    let reciprocalGap := (arms.erase best).sum (fun action =>
      1 / (lambda * gap action))
    let amplitude := 5 * (1 + lambda)
    let threshold := sampledScheduledHalfTsallisSelfBoundingThreshold
      arms best gap lambda
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      (1 + lambda) *
          ((1 + Real.log (((horizon + 1 : Nat) : Real))) / 2) +
        lambda * corruption + amplitude ^ 2 * reciprocalGap +
        (amplitude ^ 2 / 4 * reciprocalGap) *
          Real.log
            ((2 * (((horizon + 1 : Nat) : Real))) / threshold) := by
  classical
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  let reciprocalGap := (arms.erase best).sum (fun action =>
    1 / (lambda * gap action))
  let amplitude := 5 * (1 + lambda)
  let threshold := sampledScheduledHalfTsallisSelfBoundingThreshold
    arms best gap lambda
  let cutoff := ⌊threshold⌋₊
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap]
    exact sum_inv_pos_of_nonempty (arms.erase best) hsuboptimal
      (fun action => lambda * gap action) (by
        intro action haction
        exact mul_pos hlambda.1 (hgap action haction))
  have hamplitude : 0 < amplitude := by
    dsimp [amplitude]
    linarith [hlambda.1]
  have hcard : 0 < (arms.erase best).card := hsuboptimal.card_pos
  have hsqrtCard :
      0 < Real.sqrt ((arms.erase best).card : Real) := by positivity
  have hratio :
      0 < amplitude * reciprocalGap /
        (2 * Real.sqrt ((arms.erase best).card : Real)) := by positivity
  have hthresholdEq :
      threshold =
        (amplitude * reciprocalGap /
          (2 * Real.sqrt ((arms.erase best).card : Real))) ^ 2 := by
    simp [threshold, sampledScheduledHalfTsallisSelfBoundingThreshold,
      amplitude, reciprocalGap]
  have hthresholdPos : 0 < threshold := by
    rw [hthresholdEq]
    positivity
  have hfloor := natFloor_positive_and_half_le threshold
    (by simpa [threshold] using hthresholdOne)
  have hcutoffPos : 0 < cutoff := by simpa [cutoff] using hfloor.1
  have hcutoffLeThreshold : (cutoff : Real) <= threshold := by
    simpa [cutoff] using hfloor.2.1
  have hthresholdLeTwoCutoff : threshold <= 2 * (cutoff : Real) := by
    simpa [cutoff] using hfloor.2.2
  have hcutoff : cutoff <= horizon + 1 := by
    have hcutoffReal :
        (cutoff : Real) <= (((horizon + 1 : Nat) : Real)) :=
      hcutoffLeThreshold.trans
        (by simpa [threshold] using hthresholdHorizon)
    exact_mod_cast hcutoffReal
  have hsqrtThreshold :
      Real.sqrt threshold =
        amplitude * reciprocalGap /
          (2 * Real.sqrt ((arms.erase best).card : Real)) := by
    rw [hthresholdEq, Real.sqrt_sq_eq_abs, abs_of_pos hratio]
  have hcutoffThreshold :
      2 * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) <=
        amplitude * reciprocalGap := by
    have hsqrtLe :
        Real.sqrt (cutoff : Real) <= Real.sqrt threshold :=
      Real.sqrt_le_sqrt hcutoffLeThreshold
    calc
      2 * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) <=
          2 * Real.sqrt ((arms.erase best).card : Real) *
            Real.sqrt threshold := by gcongr
      _ = amplitude * reciprocalGap := by
        rw [hsqrtThreshold]
        field_simp [ne_of_gt hsqrtCard]
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingQuadraticClosedForm
      prior arms harms loss hbest horizon cutoff hcutoffPos hcutoff gap
        hsuboptimal hgap corruption lambda hlambda
        (by simpa [amplitude, reciprocalGap] using hcutoffThreshold)
        (by simpa [selector, mu] using hselfBounding)
  dsimp only at hroute
  have hsqrtCutoffLe :
      Real.sqrt (cutoff : Real) <= Real.sqrt threshold :=
    Real.sqrt_le_sqrt hcutoffLeThreshold
  have hactiveFirst :
      2 * amplitude * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) <=
        amplitude ^ 2 * reciprocalGap := by
    calc
      2 * amplitude * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) <=
          2 * amplitude * Real.sqrt ((arms.erase best).card : Real) *
            Real.sqrt threshold := by gcongr
      _ = amplitude ^ 2 * reciprocalGap := by
        rw [hsqrtThreshold]
        field_simp [ne_of_gt hsqrtCard]
  have hactive :
      2 * amplitude * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) -
        (cutoff : Real) * (arms.erase best).card / reciprocalGap <=
          amplitude ^ 2 * reciprocalGap := by
    have hsubNonneg :
        0 <= (cutoff : Real) * (arms.erase best).card / reciprocalGap := by
      positivity
    linarith
  have hhorizonPos :
      0 < (((horizon + 1 : Nat) : Real)) := by positivity
  have hcutoffCastPos : 0 < (cutoff : Real) := by exact_mod_cast hcutoffPos
  have hratioLe :
      (((horizon + 1 : Nat) : Real)) / (cutoff : Real) <=
        (2 * (((horizon + 1 : Nat) : Real))) / threshold := by
    rw [div_le_div_iff₀ hcutoffCastPos hthresholdPos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hthresholdLeTwoCutoff hhorizonPos.le)
  have hlogLe :
      Real.log ((((horizon + 1 : Nat) : Real)) / (cutoff : Real)) <=
        Real.log
          ((2 * (((horizon + 1 : Nat) : Real))) / threshold) :=
    Real.log_le_log (div_pos hhorizonPos hcutoffCastPos) hratioLe
  have hcoefficient :
      0 <= amplitude ^ 2 / 4 * reciprocalGap := by positivity
  have htail := mul_le_mul_of_nonneg_left hlogLe hcoefficient
  have hharmonic :=
    sampledScheduledHalfTsallisHarmonicBudget_le_one_add_log horizon
  have hbase :
      (1 + lambda) *
          (sampledScheduledHalfTsallisHarmonicBudget horizon / 2) <=
        (1 + lambda) *
          ((1 + Real.log (((horizon + 1 : Nat) : Real))) / 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith [hlambda.1])
  linarith

/-- The `lambda = 1` continuous threshold, written with the ordinary
reciprocal-gap mass. -/
noncomputable def sampledScheduledHalfTsallisSelfBoundingOneThreshold
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (best : Action) (gap : Action -> Real) : Real :=
  let reciprocalGap := (arms.erase best).sum (fun action => 1 / gap action)
  (5 * reciprocalGap /
      Real.sqrt ((arms.erase best).card : Real)) ^ 2

/-- The `lambda = 1` threshold has the expected reciprocal-gap/card form. -/
theorem sampledScheduledHalfTsallisSelfBoundingOneThreshold_eq
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (best : Action) (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty) :
    sampledScheduledHalfTsallisSelfBoundingOneThreshold arms best gap =
      25 * ((arms.erase best).sum (fun action => 1 / gap action)) ^ 2 /
        ((arms.erase best).card : Real) := by
  have hcard : 0 < ((arms.erase best).card : Real) := by
    exact_mod_cast hsuboptimal.card_pos
  have hsqrtPos :
      0 < Real.sqrt ((arms.erase best).card : Real) := by positivity
  have hsqrtSq :
      Real.sqrt ((arms.erase best).card : Real) ^ 2 =
        ((arms.erase best).card : Real) := Real.sq_sqrt hcard.le
  unfold sampledScheduledHalfTsallisSelfBoundingOneThreshold
  dsimp only
  field_simp [ne_of_gt hsqrtPos]
  nlinarith

/-- A concrete large-horizon self-bounding theorem with `lambda = 1`.
Unlike the refined corruption endpoint, this theorem needs no scalar
optimization beyond checking that its continuous threshold lies in the
horizon. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_selfBoundingOne
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption : Real)
    (hthresholdOne :
      1 <= sampledScheduledHalfTsallisSelfBoundingOneThreshold
        arms best gap)
    (hthresholdHorizon :
      sampledScheduledHalfTsallisSelfBoundingOneThreshold arms best gap <=
        ((horizon + 1 : Nat) : Real))
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
    let reciprocalGap := (arms.erase best).sum (fun action => 1 / gap action)
    let threshold := sampledScheduledHalfTsallisSelfBoundingOneThreshold
      arms best gap
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      1 + Real.log (((horizon + 1 : Nat) : Real)) + corruption +
        100 * reciprocalGap +
        25 * reciprocalGap *
          Real.log
            ((2 * (((horizon + 1 : Nat) : Real))) / threshold) := by
  classical
  dsimp only
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms sampledScheduledHalfTsallisSqrtSchedule loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
  let reciprocalGap := (arms.erase best).sum (fun action => 1 / gap action)
  let threshold := sampledScheduledHalfTsallisSelfBoundingOneThreshold
    arms best gap
  have hthresholdEq :
      sampledScheduledHalfTsallisSelfBoundingThreshold arms best gap 1 =
        threshold := by
    simp [threshold,
      sampledScheduledHalfTsallisSelfBoundingThreshold,
      sampledScheduledHalfTsallisSelfBoundingOneThreshold]
    ring
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingFloorCutoff
      prior arms harms loss hbest horizon gap hsuboptimal hgap corruption 1
        (by norm_num) (by simpa [hthresholdEq] using hthresholdOne)
        (by simpa [hthresholdEq] using hthresholdHorizon)
        (by simpa [selector, mu] using hselfBounding)
  dsimp only at hroute
  norm_num [reciprocalGap, threshold, hthresholdEq] at hroute ⊢
  linarith

/-- Fully explicit `lambda = 1` large-horizon bound, with the continuous
threshold rewritten as `25 * S^2 / (K-1)`. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_selfBoundingOne_explicit
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption : Real)
    (hthresholdOne :
      1 <=
        25 * ((arms.erase best).sum (fun action => 1 / gap action)) ^ 2 /
          ((arms.erase best).card : Real))
    (hthresholdHorizon :
      25 * ((arms.erase best).sum (fun action => 1 / gap action)) ^ 2 /
          ((arms.erase best).card : Real) <=
        ((horizon + 1 : Nat) : Real))
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
    let reciprocalGap := (arms.erase best).sum (fun action => 1 / gap action)
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      1 + Real.log (((horizon + 1 : Nat) : Real)) + corruption +
        100 * reciprocalGap +
        25 * reciprocalGap *
          Real.log
            ((2 * (((horizon + 1 : Nat) : Real)) *
                ((arms.erase best).card : Real)) /
              (25 * reciprocalGap ^ 2)) := by
  classical
  dsimp only
  let reciprocalGap := (arms.erase best).sum (fun action => 1 / gap action)
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap]
    exact sum_inv_pos_of_nonempty (arms.erase best) hsuboptimal gap hgap
  have hcard : 0 < ((arms.erase best).card : Real) := by
    exact_mod_cast hsuboptimal.card_pos
  have hthresholdEq :=
    sampledScheduledHalfTsallisSelfBoundingOneThreshold_eq
      arms best gap hsuboptimal
  have hratioEq :
      (2 * (((horizon + 1 : Nat) : Real))) /
          (25 * reciprocalGap ^ 2 /
            ((arms.erase best).card : Real)) =
        (2 * (((horizon + 1 : Nat) : Real)) *
            ((arms.erase best).card : Real)) /
          (25 * reciprocalGap ^ 2) := by
    field_simp [ne_of_gt hreciprocalGap, ne_of_gt hcard]
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_selfBoundingOne
      prior arms harms loss hbest horizon gap hsuboptimal hgap corruption
        (by simpa [hthresholdEq] using hthresholdOne)
        (by simpa [hthresholdEq] using hthresholdHorizon)
        hselfBounding
  dsimp only at hroute
  rw [hthresholdEq] at hroute
  change
    (2 * (((horizon + 1 : Nat) : Real))) /
        (25 * reciprocalGap ^ 2 /
          ((arms.erase best).card : Real)) =
      (2 * (((horizon + 1 : Nat) : Real)) *
          ((arms.erase best).card : Real)) /
        (25 * reciprocalGap ^ 2) at hratioEq
  rw [hratioEq] at hroute
  simpa [reciprocalGap] using hroute

end Tsallis
end BanditRLProof
