import BanditRLProof.TsallisScheduledSelfBoundingOptimization
import BanditRLProof.TsallisSqrtScheduleFixedGap

/-!
# Square-root schedule self-bounding optimization

This module specializes the refined generated quadratic split to the local
schedule `eta_t = 1 / (2 * sqrt (t + 1))`. The refined coefficient is replaced
by its compiled `5 / sqrt (t + 1)` envelope and the deterministic rate-square
base is identified with one half of the harmonic budget.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Integral-comparison bound for the shifted inverse-square-root prefix. -/
theorem sum_range_one_div_sqrt_natSucc_le_two_sqrt (n : Nat) :
    (Finset.range n).sum (fun t =>
        1 / Real.sqrt (((t + 1 : Nat) : Real))) ≤
      2 * Real.sqrt (n : Real) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hincrement :
          1 / Real.sqrt (((n + 1 : Nat) : Real)) ≤
            2 * (Real.sqrt ((n + 1 : Nat) : Real) -
              Real.sqrt (n : Real)) := by
        by_cases hn : n = 0
        · subst n
          norm_num
        · have hsqrtSuccPos :
              0 < Real.sqrt (((n + 1 : Nat) : Real)) := by positivity
          have hsqrtSucc :
              Real.sqrt (((n + 1 : Nat) : Real)) *
                  Real.sqrt (((n + 1 : Nat) : Real)) =
                ((n + 1 : Nat) : Real) :=
            Real.mul_self_sqrt (by positivity)
          have hsqrt :
              Real.sqrt (n : Real) * Real.sqrt (n : Real) =
                (n : Real) := Real.mul_self_sqrt (by positivity)
          have hcast : (((n + 1 : Nat) : Real)) = (n : Real) + 1 := by
            norm_num
          field_simp
          nlinarith [sq_nonneg
            (Real.sqrt (((n + 1 : Nat) : Real)) - Real.sqrt (n : Real))]
      norm_num [Nat.cast_add, Nat.cast_one] at *
      linarith

/-- Harmonic tail bound with the exact logarithmic ratio needed by the
self-bounding threshold split. -/
theorem sum_Ico_one_div_natSucc_le_log_div
    (m n : Nat) (hm : 0 < m) (hmn : m ≤ n) :
    (Finset.Ico m n).sum (fun t =>
        1 / (((t + 1 : Nat) : Real))) ≤
      Real.log ((n : Real) / (m : Real)) := by
  have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hmnReal : (m : Real) ≤ (n : Real) := by exact_mod_cast hmn
  have hsum := AntitoneOn.sum_le_integral_Ico hmn
    (inv_antitoneOn_Icc_right (b := (n : Real)) hmReal)
  have hzero : (0 : Real) ∉ Set.uIcc (m : Real) (n : Real) := by
    rw [Set.uIcc_of_le hmnReal]
    intro hmem
    exact (not_le_of_gt hmReal) hmem.1
  calc
    (Finset.Ico m n).sum (fun t =>
        1 / (((t + 1 : Nat) : Real))) =
        (Finset.Ico m n).sum (fun t =>
          (((t + 1 : Nat) : Real))⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [one_div]
    _ ≤ ∫ x in (m : Real)..(n : Real), x⁻¹ := by
      simpa using hsum
    _ = Real.log ((n : Real) / (m : Real)) := integral_inv hzero

/-- The active-prefix branch of the square-root schedule has a closed-form
inverse-square-root bound. -/
theorem sum_range_sqrtSchedule_activeBranch_le_closedForm
    (cutoff : Nat) (amplitude sqrtCard card reciprocalGap : Real)
    (hamplitude : 0 <= amplitude) (hsqrtCard : 0 <= sqrtCard) :
    (Finset.range cutoff).sum (fun t =>
        amplitude / Real.sqrt (((t + 1 : Nat) : Real)) * sqrtCard -
          card / reciprocalGap) <=
      2 * amplitude * sqrtCard * Real.sqrt (cutoff : Real) -
        (cutoff : Real) * card / reciprocalGap := by
  have hcoefficient : 0 <= amplitude * sqrtCard :=
    mul_nonneg hamplitude hsqrtCard
  have hsum := sum_range_one_div_sqrt_natSucc_le_two_sqrt cutoff
  calc
    (Finset.range cutoff).sum (fun t =>
        amplitude / Real.sqrt (((t + 1 : Nat) : Real)) * sqrtCard -
          card / reciprocalGap) =
        amplitude * sqrtCard *
            (Finset.range cutoff).sum (fun t =>
              1 / Real.sqrt (((t + 1 : Nat) : Real))) -
          (cutoff : Real) * card / reciprocalGap := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        ring
      · simp
        ring
    _ <= amplitude * sqrtCard * (2 * Real.sqrt (cutoff : Real)) -
          (cutoff : Real) * card / reciprocalGap := by
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hsum hcoefficient) _
    _ = 2 * amplitude * sqrtCard * Real.sqrt (cutoff : Real) -
          (cutoff : Real) * card / reciprocalGap := by ring

/-- The unconstrained tail branch of the square-root schedule is controlled by
the logarithmic harmonic tail. -/
theorem sum_Ico_sqrtSchedule_unconstrainedBranch_le_log
    (m n : Nat) (hm : 0 < m) (hmn : m <= n)
    (amplitude reciprocalGap : Real) (hreciprocalGap : 0 <= reciprocalGap) :
    (Finset.Ico m n).sum (fun t =>
        (amplitude / Real.sqrt (((t + 1 : Nat) : Real))) ^ 2 / 4 *
          reciprocalGap) <=
      (amplitude ^ 2 / 4 * reciprocalGap) *
        Real.log ((n : Real) / (m : Real)) := by
  have hsum := sum_Ico_one_div_natSucc_le_log_div m n hm hmn
  have hcoefficient : 0 <= amplitude ^ 2 / 4 * reciprocalGap := by
    positivity
  calc
    (Finset.Ico m n).sum (fun t =>
        (amplitude / Real.sqrt (((t + 1 : Nat) : Real))) ^ 2 / 4 *
          reciprocalGap) =
        (amplitude ^ 2 / 4 * reciprocalGap) *
          (Finset.Ico m n).sum (fun t =>
            1 / (((t + 1 : Nat) : Real))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hsqrtPos :
          0 < Real.sqrt (((t + 1 : Nat) : Real)) := by positivity
      have hsqrtSq :
          Real.sqrt (((t + 1 : Nat) : Real)) ^ 2 =
            ((t + 1 : Nat) : Real) := Real.sq_sqrt (by positivity)
      field_simp [ne_of_gt hsqrtPos]
      nlinarith
    _ <= (amplitude ^ 2 / 4 * reciprocalGap) *
          Real.log ((n : Real) / (m : Real)) :=
      mul_le_mul_of_nonneg_left hsum hcoefficient

/-- The refined terminal self-bounding route under the concrete square-root
schedule, reduced to two explicit filtered scalar sums. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingQuadraticSplit
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon : Nat)
    (gap : Action → Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption lambda : Real) (hlambda : lambda ∈ Set.Ioc (0 : Real) 1)
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
                t action)) - corruption ≤
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms sampledScheduledHalfTsallisSqrtSchedule loss
            (pointMass best) horizon)) :
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule
        selector.finiteHistory loss.environment
    let times := Finset.range (horizon + 1)
    let reciprocalGap := (arms.erase best).sum (fun action =>
      1 / (lambda * gap action))
    let b := fun t =>
      (1 + lambda) *
        (5 / Real.sqrt (((t + 1 : Nat) : Real)))
    let active := fun t =>
      2 * Real.sqrt ((arms.erase best).card : Real) ≤
        b t * reciprocalGap
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) ≤
      (1 + lambda) *
          (sampledScheduledHalfTsallisHarmonicBudget horizon / 2) +
        lambda * corruption +
        (times.filter active).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) +
        (times.filter fun t => ¬ active t).sum (fun t =>
          (b t) ^ 2 / 4 * reciprocalGap) := by
  classical
  dsimp only
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let times := Finset.range (horizon + 1)
  let reciprocalGap := (arms.erase best).sum (fun action =>
    1 / (lambda * gap action))
  let b := fun t =>
    (1 + lambda) *
      (5 / Real.sqrt (((t + 1 : Nat) : Real)))
  let active := fun t =>
    2 * Real.sqrt ((arms.erase best).card : Real) ≤
      b t * reciprocalGap
  let base := times.sum (fun t => 2 * (eta t) ^ 2)
  have hb : ∀ t, t ≤ horizon →
      (1 + lambda) * sampledScheduledHalfTsallisRefinedCoefficient eta t ≤
        b t := by
    intro t ht
    exact mul_le_mul_of_nonneg_left
      (by simpa [eta] using
        sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_le t)
      (by linarith [hlambda.1])
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedSelfBoundingQuadraticSplit_of_refinedCoefficient_le
      prior arms harms eta loss hbest horizon
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_pos t)
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_le_half t)
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_succ_le t)
      gap hsuboptimal hgap corruption lambda hlambda b hb
      (by simpa [eta, mu, selector] using hselfBounding)
  dsimp only at hroute
  have hbaseTwice :
      2 * base = sampledScheduledHalfTsallisHarmonicBudget horizon := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hfour := sampledScheduledHalfTsallisSqrtSchedule_four_mul_sq t
    change 2 * (2 * (sampledScheduledHalfTsallisSqrtSchedule t) ^ 2) =
      1 / (((t + 1 : Nat) : Real))
    nlinarith [hfour]
  have hbase :
      base = sampledScheduledHalfTsallisHarmonicBudget horizon / 2 := by
    linarith
  have hbase' :
      (Finset.range (horizon + 1)).sum (fun t =>
          2 * (sampledScheduledHalfTsallisSqrtSchedule t) ^ 2) =
        sampledScheduledHalfTsallisHarmonicBudget horizon / 2 := by
    simpa [base, times, eta] using hbase
  rw [hbase'] at hroute
  simpa [eta, mu, selector, times, reciprocalGap, b, active, base] using hroute

/-- Prefix/suffix specialization with a single scalar cutoff certificate. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingQuadraticPrefixSplit
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon cutoff : Nat)
    (hcutoff : cutoff ≤ horizon + 1)
    (gap : Action → Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption lambda : Real) (hlambda : lambda ∈ Set.Ioc (0 : Real) 1)
    (hcutoffThreshold :
      2 * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) ≤
        5 * (1 + lambda) * (arms.erase best).sum (fun action =>
          1 / (lambda * gap action)))
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
                t action)) - corruption ≤
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
    let b := fun t =>
      (1 + lambda) *
        (5 / Real.sqrt (((t + 1 : Nat) : Real)))
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) ≤
      (1 + lambda) *
          (sampledScheduledHalfTsallisHarmonicBudget horizon / 2) +
        lambda * corruption +
        (Finset.range cutoff).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) +
        (Finset.Ico cutoff (horizon + 1)).sum (fun t =>
          (b t) ^ 2 / 4 * reciprocalGap) := by
  classical
  dsimp only
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector :=
    canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
      arms harms eta loss
  let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let times := Finset.range (horizon + 1)
  let reciprocalGap := (arms.erase best).sum (fun action =>
    1 / (lambda * gap action))
  let b := fun t =>
    (1 + lambda) *
      (5 / Real.sqrt (((t + 1 : Nat) : Real)))
  let base := times.sum (fun t => 2 * (eta t) ^ 2)
  have hb : ∀ t, t ≤ horizon →
      (1 + lambda) * sampledScheduledHalfTsallisRefinedCoefficient eta t ≤
        b t := by
    intro t ht
    exact mul_le_mul_of_nonneg_left
      (by simpa [eta] using
        sampledScheduledHalfTsallisRefinedCoefficient_sqrtSchedule_le t)
      (by linarith [hlambda.1])
  have hsum :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_refinedSelfBoundingQuadraticSum_of_refinedCoefficient_le
      prior arms harms eta loss hbest horizon
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_pos t)
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_le_half t)
      (fun t _ht => sampledScheduledHalfTsallisSqrtSchedule_succ_le t)
      gap corruption lambda hlambda b hb
      (by simpa [eta, mu, selector] using hselfBounding)
  dsimp only at hsum
  have hthreshold : ∀ t < cutoff,
      2 * Real.sqrt ((arms.erase best).card : Real) ≤
        b t * reciprocalGap := by
    intro t ht
    have htCast : (((t + 1 : Nat) : Real)) ≤ (cutoff : Real) := by
      exact_mod_cast (Nat.succ_le_iff.mpr ht)
    have hsqrtLe :
        Real.sqrt (((t + 1 : Nat) : Real)) ≤
          Real.sqrt (cutoff : Real) := Real.sqrt_le_sqrt htCast
    have hsqrtPos :
        0 < Real.sqrt (((t + 1 : Nat) : Real)) := by positivity
    have hscaled :
        2 * Real.sqrt ((arms.erase best).card : Real) *
            Real.sqrt (((t + 1 : Nat) : Real)) ≤
          2 * Real.sqrt ((arms.erase best).card : Real) *
            Real.sqrt (cutoff : Real) := by
      gcongr
    have hproduct :
        2 * Real.sqrt ((arms.erase best).card : Real) *
            Real.sqrt (((t + 1 : Nat) : Real)) ≤
          5 * (1 + lambda) * reciprocalGap :=
      hscaled.trans (by simpa [reciprocalGap] using hcutoffThreshold)
    have hbEq :
        b t * reciprocalGap =
          (5 * (1 + lambda) * reciprocalGap) /
            Real.sqrt (((t + 1 : Nat) : Real)) := by
      dsimp [b]
      field_simp [ne_of_gt hsqrtPos]
    rw [hbEq, le_div_iff₀ hsqrtPos]
    exact hproduct
  have hsplit :=
    sum_range_sampledScheduledHalfTsallisExpectedProbability_le_quadraticPrefixSplit
      mu arms harms eta (horizon + 1) cutoff hcutoff hbest gap
        hsuboptimal hgap b lambda hlambda.1 hthreshold
  have hbaseTwice :
      2 * base = sampledScheduledHalfTsallisHarmonicBudget horizon := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hfour := sampledScheduledHalfTsallisSqrtSchedule_four_mul_sq t
    change 2 * (2 * (sampledScheduledHalfTsallisSqrtSchedule t) ^ 2) =
      1 / (((t + 1 : Nat) : Real))
    nlinarith [hfour]
  have hbase :
      base = sampledScheduledHalfTsallisHarmonicBudget horizon / 2 := by
    linarith
  have hfinal :
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          arms harms eta loss (pointMass best) horizon) ≤
        (1 + lambda) * base + lambda * corruption +
        (Finset.range cutoff).sum (fun t =>
          b t * Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) +
        (Finset.Ico cutoff (horizon + 1)).sum (fun t =>
          (b t) ^ 2 / 4 * reciprocalGap) := by
    linarith
  rw [hbase] at hfinal
  simpa [eta, mu, selector, reciprocalGap, b, base] using hfinal

/-- Closed-form generated-regret endpoint after choosing a positive cutoff.
The only remaining scalar optimization is the choice of `cutoff` and `lambda`. -/
theorem integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingQuadraticClosedForm
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms) (horizon cutoff : Nat)
    (hcutoffPos : 0 < cutoff) (hcutoff : cutoff <= horizon + 1)
    (gap : Action -> Real)
    (hsuboptimal : (arms.erase best).Nonempty)
    (hgap : ∀ action ∈ arms.erase best, 0 < gap action)
    (corruption lambda : Real) (hlambda : lambda ∈ Set.Ioc (0 : Real) 1)
    (hcutoffThreshold :
      2 * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) <=
        5 * (1 + lambda) * (arms.erase best).sum (fun action =>
          1 / (lambda * gap action)))
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
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass best) horizon) <=
      (1 + lambda) *
          (sampledScheduledHalfTsallisHarmonicBudget horizon / 2) +
        lambda * corruption +
        2 * amplitude * Real.sqrt ((arms.erase best).card : Real) *
          Real.sqrt (cutoff : Real) -
        (cutoff : Real) * (arms.erase best).card / reciprocalGap +
        (amplitude ^ 2 / 4 * reciprocalGap) *
          Real.log (((horizon + 1 : Nat) : Real) / (cutoff : Real)) := by
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
  have hreciprocalGap : 0 < reciprocalGap := by
    dsimp [reciprocalGap]
    exact sum_inv_pos_of_nonempty (arms.erase best) hsuboptimal
      (fun action => lambda * gap action) (by
        intro action haction
        exact mul_pos hlambda.1 (hgap action haction))
  have hroute :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_refinedSelfBoundingQuadraticPrefixSplit
      prior arms harms loss hbest horizon cutoff hcutoff gap hsuboptimal hgap
        corruption lambda hlambda hcutoffThreshold
        (by simpa [selector, mu] using hselfBounding)
  dsimp only at hroute
  have hprefixScalar :=
    sum_range_sqrtSchedule_activeBranch_le_closedForm cutoff amplitude
      (Real.sqrt ((arms.erase best).card : Real))
      ((arms.erase best).card : Real) reciprocalGap
      (by dsimp [amplitude]; linarith [hlambda.1]) (Real.sqrt_nonneg _)
  have hprefix :
      (Finset.range cutoff).sum (fun t =>
          (1 + lambda) *
              (5 / Real.sqrt (((t + 1 : Nat) : Real))) *
              Real.sqrt ((arms.erase best).card : Real) -
            (arms.erase best).card / reciprocalGap) <=
        2 * amplitude * Real.sqrt ((arms.erase best).card : Real) *
            Real.sqrt (cutoff : Real) -
          (cutoff : Real) * (arms.erase best).card / reciprocalGap := by
    calc
      _ = (Finset.range cutoff).sum (fun t =>
          amplitude / Real.sqrt (((t + 1 : Nat) : Real)) *
              Real.sqrt ((arms.erase best).card : Real) -
            ((arms.erase best).card : Real) / reciprocalGap) := by
        apply Finset.sum_congr rfl
        intro t ht
        dsimp [amplitude]
        ring
      _ <= _ := hprefixScalar
  have htailScalar :=
    sum_Ico_sqrtSchedule_unconstrainedBranch_le_log cutoff (horizon + 1)
      hcutoffPos hcutoff amplitude reciprocalGap hreciprocalGap.le
  have htail :
      (Finset.Ico cutoff (horizon + 1)).sum (fun t =>
          ((1 + lambda) *
              (5 / Real.sqrt (((t + 1 : Nat) : Real)))) ^ 2 / 4 *
            reciprocalGap) <=
        (amplitude ^ 2 / 4 * reciprocalGap) *
          Real.log (((horizon + 1 : Nat) : Real) / (cutoff : Real)) := by
    calc
      _ = (Finset.Ico cutoff (horizon + 1)).sum (fun t =>
          (amplitude / Real.sqrt (((t + 1 : Nat) : Real))) ^ 2 / 4 *
            reciprocalGap) := by
        apply Finset.sum_congr rfl
        intro t ht
        dsimp [amplitude]
        ring
      _ <= _ := htailScalar
  linarith

end Tsallis
end BanditRLProof
