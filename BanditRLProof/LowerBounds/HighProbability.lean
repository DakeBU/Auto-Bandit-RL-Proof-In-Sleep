import BanditRLProof.LowerBounds.InstanceDependent
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.Linarith

/-!
# High-probability lower-bound interfaces

This module formalizes the source-faithful threshold surfaces and reusable
probability/algebra leaves from Lattimore--Szepesvari, *Bandit Algorithms*
(2020), Part IV, Chapter 17.

The file closes Theorem 17.1 and Corollary 17.2 on the canonical adaptive
history law, and keeps their random pseudo-regret separate from deterministic
expected pseudo-regret.  It also formalizes Claim 17.5, the exact correlated
clipped-Gaussian path construction, and Eq. (17.8) for adversarial random
regret.  Corollary 17.3 and the probabilistic Claims 17.6--17.7 remain explicit
frontier obligations; consequently Theorem 17.4 is not claimed here.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The tail event used throughout Chapter 17: the realized quantity is at
least the displayed lower-bound threshold. -/
def tailAtLeast {Omega : Type*} (quantity : Omega -> Real) (threshold : Real) :
    Set Omega :=
  {omega | threshold <= quantity omega}

/-- The exact threshold inside Theorem 17.1, with `alternativeArms = k - 1`.
The theorem's factor `1/4` multiplies the whole minimum. -/
def stochasticHighProbabilityThreshold
    (horizon alternativeArms : Nat) (B delta : Real) : Real :=
  (1 / 4 : Real) *
    min (horizon : Real)
      ((1 / B) * Real.sqrt ((alternativeArms : Real) * (horizon : Real)) *
        Real.log (1 / (4 * delta)))

/-- The exact threshold in Corollary 17.2, again with
`alternativeArms = k - 1`. -/
def stochasticMinimaxHighProbabilityThreshold
    (horizon alternativeArms : Nat) (delta : Real) : Real :=
  (1 / 4 : Real) *
    min (horizon : Real)
      (Real.sqrt
        (((horizon : Real) * (alternativeArms : Real) / 2) *
          Real.log (1 / (4 * delta))))

/-- The threshold shape in Theorem 17.4.  The universal constant `c` remains
an explicit argument, and the logarithm is `log (1 / (2 * delta))`. -/
def adversarialHighProbabilityThreshold
    (horizon arms : Nat) (c delta : Real) : Real :=
  c * Real.sqrt
    ((horizon : Real) * (arms : Real) * Real.log (1 / (2 * delta)))

/-- The stochastic random pseudo-regret from Section 17.1, evaluated on one
realized canonical finite history.  It is deliberately separate from the
deterministic expected pseudo-regret below. -/
noncomputable def gaussianRandomPseudoRegret
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) : Real :=
  (finiteHistoryGaussianPseudoRegret environment lastRound history).toReal

/-- The deterministic expected pseudo-regret presentation used in Eq. (17.4),
written as expected pull counts times gaps (the Lemma 4.5 identity).  This is
not the random pseudo-regret and is not adversarial random regret. -/
noncomputable def gaussianExpectedPseudoRegretReal
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) : Real :=
  ∑ arm : Fin K,
    (environment.mean environment.bestArm - environment.mean arm) *
      gaussianExpectedPullCountReal algorithm environment.mean lastRound arm

/-- The source class `E^k`: unit-variance Gaussian arms with gaps bounded by
one, without an artificial absolute restriction on the means. -/
structure GapOneGaussianBanditEnvironment (K : Nat) where
  mean : Fin K -> Real
  bestArm : Fin K
  isBest : forall arm, mean arm <= mean bestArm
  gap_le_one : forall arm, mean bestArm - mean arm <= 1

/-- Deterministic expected pseudo-regret for the full source class `E^k`. -/
noncomputable def gapOneGaussianExpectedPseudoRegretReal
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : GapOneGaussianBanditEnvironment K)
    (lastRound : Nat) : Real :=
  ∑ arm : Fin K,
    (environment.mean environment.bestArm - environment.mean arm) *
      gaussianExpectedPullCountReal algorithm environment.mean lastRound arm

def UnitGaussianBanditEnvironment.toGapOne
    {K : Nat} (environment : UnitGaussianBanditEnvironment K) :
    GapOneGaussianBanditEnvironment K where
  mean := environment.mean
  bestArm := environment.bestArm
  isBest := environment.isBest
  gap_le_one := by
    intro arm
    have hbestOne := (environment.mean_mem_unit environment.bestArm).2
    have harmZero := (environment.mean_mem_unit arm).1
    linarith

@[simp]
theorem gapOneGaussianExpectedPseudoRegretReal_toGapOne
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitGaussianBanditEnvironment K) (lastRound : Nat) :
    gapOneGaussianExpectedPseudoRegretReal algorithm environment.toGapOne lastRound =
      gaussianExpectedPseudoRegretReal algorithm environment lastRound := rfl

/-- The exact gap selected in the proof of Theorem 17.1. -/
noncomputable def stochasticHighProbabilityGap
    (horizon alternativeArms : Nat) (B delta : Real) : Real :=
  min (1 / 2 : Real)
    ((1 / (2 * B)) *
      Real.sqrt ((alternativeArms : Real) / (horizon : Real)) *
      Real.log (1 / (4 * delta)))

theorem gaussianRandomPseudoRegret_nonneg
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) :
    0 <= gaussianRandomPseudoRegret environment lastRound history := by
  exact ENNReal.toReal_nonneg

theorem measurable_gaussianRandomPseudoRegret
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) :
    Measurable (gaussianRandomPseudoRegret environment lastRound) := by
  exact (measurable_finiteHistoryGaussianPseudoRegret
    environment lastRound).ennreal_toReal

/-- Unit-cube gaps and the exact pull-count sum bound stochastic random
pseudo-regret by the number of observed rounds. -/
theorem gaussianRandomPseudoRegret_le_horizon
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) :
    gaussianRandomPseudoRegret environment lastRound history <=
      (lastRound + 1 : Nat) := by
  rw [gaussianRandomPseudoRegret,
    finiteHistoryGaussianPseudoRegret_toReal]
  calc
    (∑ arm : Fin K,
        (environment.mean environment.bestArm - environment.mean arm) *
          finiteHistoryPullCountReal lastRound history arm) <=
      ∑ arm : Fin K, 1 * finiteHistoryPullCountReal lastRound history arm := by
        apply Finset.sum_le_sum
        intro arm _harm
        apply mul_le_mul_of_nonneg_right _
          (finiteHistoryPullCountReal_nonneg lastRound history arm)
        have hbestOne := (environment.mean_mem_unit environment.bestArm).2
        have harmZero := (environment.mean_mem_unit arm).1
        linarith
    _ = ∑ arm : Fin K,
        finiteHistoryPullCountReal lastRound history arm := by simp
    _ = (lastRound + 1 : Nat) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        sum_finiteHistoryPullCountReal lastRound history

theorem integrable_gaussianRandomPseudoRegret
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) :
    Integrable (gaussianRandomPseudoRegret environment lastRound)
      (canonicalBanditHistoryMeasure algorithm
        (unitGaussianKernel environment.mean) lastRound) := by
  refine Integrable.of_bound
    (measurable_gaussianRandomPseudoRegret environment lastRound).aestronglyMeasurable
    (lastRound + 1 : Nat) ?_
  filter_upwards [] with history
  rw [Real.norm_eq_abs,
    abs_of_nonneg (gaussianRandomPseudoRegret_nonneg
      environment lastRound history)]
  exact gaussianRandomPseudoRegret_le_horizon environment lastRound history

theorem gaussianExpectedPseudoRegret_toReal_eq
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) :
    (gaussianExpectedPseudoRegret algorithm environment lastRound).toReal =
      gaussianExpectedPseudoRegretReal algorithm environment lastRound := by
  classical
  rw [gaussianExpectedPseudoRegret_eq_sum_expectedPulls,
    ENNReal.toReal_sum]
  · unfold gaussianExpectedPseudoRegretReal gaussianExpectedPullCountReal
    apply Finset.sum_congr rfl
    intro arm _harm
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (sub_nonneg.mpr (environment.isBest arm))]
  · intro arm _harm
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (canonicalRealizedExpectedPullCountThrough_ne_top
        algorithm (unitGaussianKernel environment.mean) lastRound arm)

/-- The deterministic expected pseudo-regret surface is the integral of the
random pseudo-regret under the same policy/environment history law. -/
theorem integral_gaussianRandomPseudoRegret_eq_expected
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) :
    ∫ history,
        gaussianRandomPseudoRegret environment lastRound history
      ∂canonicalBanditHistoryMeasure algorithm
        (unitGaussianKernel environment.mean) lastRound =
      gaussianExpectedPseudoRegretReal algorithm environment lastRound := by
  let mu := canonicalBanditHistoryMeasure algorithm
    (unitGaussianKernel environment.mean) lastRound
  calc
    ∫ history, gaussianRandomPseudoRegret environment lastRound history ∂mu =
        (∫⁻ history,
          ENNReal.ofReal
            (gaussianRandomPseudoRegret environment lastRound history)
          ∂mu).toReal := by
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun history =>
          gaussianRandomPseudoRegret_nonneg environment lastRound history)
        (integrable_gaussianRandomPseudoRegret
          algorithm environment lastRound).aestronglyMeasurable
    _ = (gaussianExpectedPseudoRegret
          algorithm environment lastRound).toReal := by
      congr 1
      unfold gaussianExpectedPseudoRegret gaussianRandomPseudoRegret
      apply lintegral_congr
      intro history
      rw [ENNReal.ofReal_toReal
        (finiteHistoryGaussianPseudoRegret_ne_top
          environment lastRound history)]
    _ = gaussianExpectedPseudoRegretReal
          algorithm environment lastRound :=
      gaussianExpectedPseudoRegret_toReal_eq
        algorithm environment lastRound

/-- Integrating a nonnegative bounded random variable after splitting at one
measurable upper-tail event. -/
theorem integral_le_threshold_add_bound_mul_tailMass
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (quantity : Omega -> Real) (threshold bound : Real)
    (hmeas : Measurable quantity) (hintegrable : Integrable quantity mu)
    (hthreshold : 0 <= threshold)
    (hbound : forall omega, quantity omega <= bound) :
    ∫ omega, quantity omega ∂mu <=
      threshold + bound * mu.real (tailAtLeast quantity threshold) := by
  let bad := tailAtLeast quantity threshold
  have hbad : MeasurableSet bad :=
    measurableSet_le measurable_const hmeas
  let penalty : Omega -> Real := bad.indicator (fun _ => bound)
  have hpenalty : Integrable penalty mu :=
    (integrable_const bound).indicator hbad
  have hmajorant : Integrable (fun omega => threshold + penalty omega) mu :=
    (integrable_const threshold).add hpenalty
  calc
    ∫ omega, quantity omega ∂mu <=
        ∫ omega, threshold + penalty omega ∂mu := by
      apply integral_mono hintegrable hmajorant
      intro omega
      by_cases hmem : omega ∈ bad
      · simp [penalty, hmem]
        exact (hbound omega).trans (le_add_of_nonneg_left hthreshold)
      · simp [penalty, hmem]
        simp only [bad, tailAtLeast, Set.mem_setOf_eq] at hmem
        exact (lt_of_not_ge hmem).le
    _ = threshold + bound * mu.real bad := by
      rw [integral_add (integrable_const threshold) hpenalty]
      simp [penalty, hbad, Measure.real_def, mul_comm]

/-- In the base environment, expected pseudo-regret is exactly the common
alternative gap times the sum of the alternative expected pull counts. -/
theorem gaussianExpectedPseudoRegretReal_base_eq
    {m : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (hgap : 0 <= gap) (hgap_le : gap <= 1 / 2)
    (lastRound : Nat) :
    gaussianExpectedPseudoRegretReal algorithm
        (gaussianMinimaxBaseEnvironment gap hgap hgap_le) lastRound =
      gap * ∑ i : Fin m,
        gaussianExpectedPullCountReal algorithm
          (gaussianMinimaxBaseMean gap) lastRound i.succ := by
  classical
  unfold gaussianExpectedPseudoRegretReal
  rw [Fin.sum_univ_succ]
  simp only [gaussianMinimaxBaseEnvironment, gaussianMinimaxBaseMean_zero,
    gaussianMinimaxBaseMean_succ, sub_self, zero_mul, zero_add, sub_zero]
  rw [Finset.mul_sum]

/-- Positive-horizon square-root normalization used by the exact Chapter 17
gap calibration. -/
theorem horizon_mul_sqrt_div_eq_sqrt_mul
    {horizon alternatives : Real} (hhorizon : 0 < horizon)
    (halternatives : 0 <= alternatives) :
    horizon * Real.sqrt (alternatives / horizon) =
      Real.sqrt (horizon * alternatives) := by
  calc
    horizon * Real.sqrt (alternatives / horizon) =
        horizon * (Real.sqrt alternatives / Real.sqrt horizon) := by
      rw [Real.sqrt_div halternatives]
    _ = Real.sqrt horizon * Real.sqrt alternatives := by
      calc
        horizon * (Real.sqrt alternatives / Real.sqrt horizon) =
            (Real.sqrt horizon * Real.sqrt horizon) *
              (Real.sqrt alternatives / Real.sqrt horizon) := by
          rw [Real.mul_self_sqrt hhorizon.le]
        _ = Real.sqrt horizon * Real.sqrt alternatives := by
          field_simp [Real.sqrt_ne_zero'.mpr hhorizon]
    _ = Real.sqrt (horizon * alternatives) :=
      (Real.sqrt_mul hhorizon.le alternatives).symm

/-- The two square-root factors in the information exponent cancel exactly. -/
theorem sqrt_mul_mul_sqrt_div_eq_alternatives
    {horizon alternatives : Real} (hhorizon : 0 < horizon)
    (halternatives : 0 <= alternatives) :
    Real.sqrt (alternatives * horizon) *
        Real.sqrt (alternatives / horizon) = alternatives := by
  have hroot :
      Real.sqrt (alternatives * horizon) =
        horizon * Real.sqrt (alternatives / horizon) := by
    simpa [mul_comm] using
      (horizon_mul_sqrt_div_eq_sqrt_mul hhorizon halternatives).symm
  have hsquare : Real.sqrt (alternatives / horizon) ^ 2 =
      alternatives / horizon := by
    rw [Real.sq_sqrt]
    positivity
  rw [hroot]
  calc
    (horizon * Real.sqrt (alternatives / horizon)) *
        Real.sqrt (alternatives / horizon) =
      horizon * Real.sqrt (alternatives / horizon) ^ 2 := by ring
    _ = horizon * (alternatives / horizon) := by rw [hsquare]
    _ = alternatives := by field_simp [hhorizon.ne']

/-- The chosen source gap times half the horizon is exactly the threshold
displayed in Theorem 17.1, including the outer factor `1/4`. -/
theorem horizon_mul_stochasticHighProbabilityGap_div_two
    (horizon alternatives : Nat) (B delta : Real)
    (hhorizon : 0 < horizon) (hB : 0 < B) :
    (horizon : Real) *
        stochasticHighProbabilityGap horizon alternatives B delta / 2 =
      stochasticHighProbabilityThreshold horizon alternatives B delta := by
  let candidate : Real :=
    (1 / (2 * B)) *
      Real.sqrt ((alternatives : Real) / (horizon : Real)) *
      Real.log (1 / (4 * delta))
  let sourceTerm : Real :=
    (1 / B) * Real.sqrt ((alternatives : Real) * (horizon : Real)) *
      Real.log (1 / (4 * delta))
  have hroot := horizon_mul_sqrt_div_eq_sqrt_mul
    (show (0 : Real) < (horizon : Real) by exact_mod_cast hhorizon)
    (show (0 : Real) <= (alternatives : Real) by positivity)
  have hscale : 2 * (horizon : Real) * candidate = sourceTerm := by
    dsimp [candidate, sourceTerm]
    rw [show Real.sqrt ((horizon : Real) * (alternatives : Real)) =
        Real.sqrt ((alternatives : Real) * (horizon : Real)) by
      rw [mul_comm]] at hroot
    rw [← hroot]
    field_simp [hB.ne']
  unfold stochasticHighProbabilityGap stochasticHighProbabilityThreshold
  change (horizon : Real) * min (1 / 2 : Real) candidate / 2 =
    (1 / 4 : Real) * min (horizon : Real) sourceTerm
  by_cases hc : candidate <= 1 / 2
  · rw [min_eq_right hc]
    have hsource : sourceTerm <= (horizon : Real) := by
      have hhorizonReal : 0 <= (horizon : Real) := by positivity
      nlinarith
    rw [min_eq_right hsource]
    nlinarith
  · have hc' : (1 / 2 : Real) <= candidate := le_of_not_ge hc
    rw [min_eq_left hc']
    have hsource : (horizon : Real) <= sourceTerm := by
      have hhorizonReal : 0 <= (horizon : Real) := by positivity
      nlinarith
    rw [min_eq_left hsource]
    ring

/-- Exact scalar information calibration in the positive-logarithm branch of
Theorem 17.1. -/
theorem stochasticHighProbability_informationExponent_le_log
    (horizon alternatives : Nat) (B delta : Real)
    (hhorizon : 0 < horizon) (halternatives : 0 < alternatives)
    (hB : 0 < B) (hlog : 0 < Real.log (1 / (4 * delta))) :
    let gap := stochasticHighProbabilityGap horizon alternatives B delta
    (B * Real.sqrt ((alternatives : Real) * (horizon : Real)) /
          (gap * (alternatives : Real))) * (2 * gap ^ 2) <=
      Real.log (1 / (4 * delta)) := by
  dsimp only
  let candidate : Real :=
    (1 / (2 * B)) *
      Real.sqrt ((alternatives : Real) / (horizon : Real)) *
      Real.log (1 / (4 * delta))
  have hcandidate : 0 < candidate := by
    dsimp [candidate]
    positivity
  have hgap : 0 < stochasticHighProbabilityGap
      horizon alternatives B delta := by
    unfold stochasticHighProbabilityGap
    exact lt_min (by norm_num) hcandidate
  have hgap_le : stochasticHighProbabilityGap
      horizon alternatives B delta <= candidate := by
    unfold stochasticHighProbabilityGap
    exact min_le_right _ _
  have hcoefficient : 0 <=
      2 * B * Real.sqrt ((alternatives : Real) * (horizon : Real)) /
        (alternatives : Real) := by positivity
  calc
    (B * Real.sqrt ((alternatives : Real) * (horizon : Real)) /
          (stochasticHighProbabilityGap horizon alternatives B delta *
            (alternatives : Real))) *
        (2 * stochasticHighProbabilityGap horizon alternatives B delta ^ 2) =
      (2 * B * Real.sqrt
          ((alternatives : Real) * (horizon : Real)) /
        (alternatives : Real)) *
          stochasticHighProbabilityGap horizon alternatives B delta := by
      field_simp [hgap.ne', Nat.cast_ne_zero.mpr halternatives.ne']
    _ <= (2 * B * Real.sqrt
          ((alternatives : Real) * (horizon : Real)) /
        (alternatives : Real)) * candidate :=
      mul_le_mul_of_nonneg_left hgap_le hcoefficient
    _ = Real.log (1 / (4 * delta)) := by
      have hcancel := sqrt_mul_mul_sqrt_div_eq_alternatives
        (show (0 : Real) < (horizon : Real) by exact_mod_cast hhorizon)
        (show (0 : Real) <= (alternatives : Real) by positivity)
      dsimp [candidate]
      field_simp [hB.ne', Nat.cast_ne_zero.mpr halternatives.ne']
      nlinarith

/-- The positive-logarithm branch of Lattimore--Szepesvari Theorem 17.1.
The algorithm is one common randomized nonanticipating history policy in the
base and changed environments.  The expected-regret premise is deterministic;
the conclusion is a tail probability for random pseudo-regret. -/
theorem gaussianRandomPseudoRegret_ge_theorem17_1_of_four_mul_delta_lt_one
    {alternatives horizon : Nat}
    (halternatives : 0 < alternatives) (hhorizon : 0 < horizon)
    (B delta : Real) (hB : 0 < B) (hdelta : 0 < delta)
    (hfourDelta : 4 * delta < 1)
    (algorithm : Thompson.HistoryAlgorithm (Fin (alternatives + 1)) Real)
    (hExpected : forall environment :
        UnitGaussianBanditEnvironment (alternatives + 1),
      gaussianExpectedPseudoRegretReal algorithm environment (horizon - 1) <=
        B * Real.sqrt
          ((alternatives : Real) * (horizon : Real))) :
    exists environment : UnitGaussianBanditEnvironment (alternatives + 1),
      delta <=
        (canonicalBanditHistoryMeasure algorithm
          (unitGaussianKernel environment.mean) (horizon - 1)).real
        (tailAtLeast
          (gaussianRandomPseudoRegret environment (horizon - 1))
          (stochasticHighProbabilityThreshold
            horizon alternatives B delta)) := by
  have hround : horizon - 1 + 1 = horizon :=
    Nat.sub_add_cancel hhorizon
  have harg : 1 < 1 / (4 * delta) := by
    rw [one_lt_div₀]
    · exact hfourDelta
    · positivity
  have hlog : 0 < Real.log (1 / (4 * delta)) := Real.log_pos harg
  let gap := stochasticHighProbabilityGap horizon alternatives B delta
  have hgap : 0 < gap := by
    dsimp [gap, stochasticHighProbabilityGap]
    exact lt_min (by norm_num) (by positivity)
  have hgap_le : gap <= 1 / 2 := by
    dsimp [gap, stochasticHighProbabilityGap]
    exact min_le_left _ _
  let baseEnvironment := gaussianMinimaxBaseEnvironment
    (m := alternatives) gap hgap.le hgap_le
  have hbaseExpected := hExpected baseEnvironment
  have hbaseIdentity := gaussianExpectedPseudoRegretReal_base_eq
    algorithm gap hgap.le hgap_le (horizon - 1)
  change gaussianExpectedPseudoRegretReal algorithm baseEnvironment
      (horizon - 1) <= _ at hbaseExpected
  change gaussianExpectedPseudoRegretReal algorithm baseEnvironment
      (horizon - 1) = _ at hbaseIdentity
  rw [hbaseIdentity] at hbaseExpected
  have hsumBudget :
      (∑ i : Fin alternatives,
        gaussianExpectedPullCountReal algorithm
          (gaussianMinimaxBaseMean gap) (horizon - 1) i.succ) <=
        (B * Real.sqrt
          ((alternatives : Real) * (horizon : Real))) / gap := by
    apply (le_div_iff₀ hgap).2
    simpa [mul_comm] using hbaseExpected
  obtain ⟨i, hi⟩ := exists_alternative_le_average halternatives
    (fun i : Fin alternatives =>
      gaussianExpectedPullCountReal algorithm
        (gaussianMinimaxBaseMean gap) (horizon - 1) i.succ)
    ((B * Real.sqrt
      ((alternatives : Real) * (horizon : Real))) / gap)
    hsumBudget
  have hi' :
      gaussianExpectedPullCountReal algorithm
          (gaussianMinimaxBaseMean gap) (horizon - 1) i.succ <=
        B * Real.sqrt
            ((alternatives : Real) * (horizon : Real)) /
          (gap * (alternatives : Real)) := by
    calc
      gaussianExpectedPullCountReal algorithm
          (gaussianMinimaxBaseMean gap) (horizon - 1) i.succ <=
          (B * Real.sqrt
            ((alternatives : Real) * (horizon : Real)) / gap) /
            (alternatives : Real) := hi
      _ = B * Real.sqrt
            ((alternatives : Real) * (horizon : Real)) /
          (gap * (alternatives : Real)) := by
        field_simp [hgap.ne', Nat.cast_ne_zero.mpr halternatives.ne']
  let count : ENNReal := canonicalRealizedExpectedPullCountThrough algorithm
    (unitGaussianKernel (gaussianMinimaxBaseMean gap))
    (horizon - 1) i.succ
  have hcount_ne : count ≠ ∞ := by
    exact canonicalRealizedExpectedPullCountThrough_ne_top
      algorithm (unitGaussianKernel (gaussianMinimaxBaseMean gap))
        (horizon - 1) i.succ
  have hcountReal : count.toReal =
      gaussianExpectedPullCountReal algorithm
        (gaussianMinimaxBaseMean gap) (horizon - 1) i.succ := rfl
  have hexponent : count.toReal * (2 * gap ^ 2) <=
      Real.log (1 / (4 * delta)) := by
    calc
      count.toReal * (2 * gap ^ 2) <=
          (B * Real.sqrt
              ((alternatives : Real) * (horizon : Real)) /
            (gap * (alternatives : Real))) * (2 * gap ^ 2) := by
        rw [hcountReal]
        exact mul_le_mul_of_nonneg_right hi' (by positivity)
      _ <= Real.log (1 / (4 * delta)) :=
        stochasticHighProbability_informationExponent_le_log
          horizon alternatives B delta hhorizon halternatives hB hlog
  have hKL :
      InformationTheory.klDiv
          (canonicalBanditHistoryMeasure algorithm
            (unitGaussianKernel (gaussianMinimaxBaseMean gap))
              (horizon - 1))
          (canonicalBanditHistoryMeasure algorithm
            (unitGaussianKernel (gaussianMinimaxChangedMean gap i))
              (horizon - 1)) <=
        ENNReal.ofReal (Real.log (1 / (4 * delta))) := by
    rw [klDiv_gaussianMinimax_base_changed_history]
    change count * ENNReal.ofReal (2 * gap ^ 2) <= _
    rw [← ENNReal.ofReal_toReal hcount_ne]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hexponent
  let changedEnvironment := gaussianMinimaxChangedEnvironment
    gap i hgap.le hgap_le
  let P := canonicalBanditHistoryMeasure algorithm
    (unitGaussianKernel (gaussianMinimaxBaseMean gap)) (horizon - 1)
  let Q := canonicalBanditHistoryMeasure algorithm
    (unitGaussianKernel (gaussianMinimaxChangedMean gap i)) (horizon - 1)
  let A := gaussianMinimaxBaseSmallPullEvent
    (m := alternatives) (horizon - 1)
  have htesting := bretagnolleHuber
    (P := P) (Q := Q)
    (measurableSet_gaussianMinimaxBaseSmallPullEvent (horizon - 1))
  have htesting' :
      bretagnolleHuberScale
          (ENNReal.ofReal (Real.log (1 / (4 * delta)))) <=
        P.real A + Q.real Aᶜ := by
    exact (bretagnolleHuberScale_antitone hKL).trans htesting
  have hexp : Real.exp (-Real.log (1 / (4 * delta))) = 4 * delta := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp [hdelta.ne']
  have hscale :
      bretagnolleHuberScale
          (ENNReal.ofReal (Real.log (1 / (4 * delta)))) = 2 * delta := by
    have hfinite : ENNReal.ofReal (Real.log (1 / (4 * delta))) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have htoReal :
        (ENNReal.ofReal (Real.log (1 / (4 * delta)))).toReal =
          Real.log (1 / (4 * delta)) := ENNReal.toReal_ofReal hlog.le
    unfold bretagnolleHuberScale
    rw [if_neg hfinite, htoReal, hexp]
    ring
  rw [hscale] at htesting'
  have hthreshold := horizon_mul_stochasticHighProbabilityGap_div_two
    horizon alternatives B delta hhorizon hB
  have hbaseSubset : A ⊆
      tailAtLeast
        (gaussianRandomPseudoRegret baseEnvironment (horizon - 1))
        (stochasticHighProbabilityThreshold
          horizon alternatives B delta) := by
    intro history hhistory
    change stochasticHighProbabilityThreshold
        horizon alternatives B delta <=
      gaussianRandomPseudoRegret baseEnvironment (horizon - 1) history
    rw [← hthreshold]
    have hforce := base_event_forces_gaussianPseudoRegret
      gap hgap.le hgap_le (horizon - 1) history hhistory
    have hreal := ENNReal.toReal_mono
      (finiteHistoryGaussianPseudoRegret_ne_top baseEnvironment
        (horizon - 1) history) hforce
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    simpa [gaussianRandomPseudoRegret, hround] using hreal
  have hchangedSubset : Aᶜ ⊆
      tailAtLeast
        (gaussianRandomPseudoRegret changedEnvironment (horizon - 1))
        (stochasticHighProbabilityThreshold
          horizon alternatives B delta) := by
    intro history hhistory
    change stochasticHighProbabilityThreshold
        horizon alternatives B delta <=
      gaussianRandomPseudoRegret changedEnvironment (horizon - 1) history
    rw [← hthreshold]
    have hforce := changed_complement_forces_gaussianPseudoRegret
      gap i hgap.le hgap_le (horizon - 1) history hhistory
    have hreal := ENNReal.toReal_mono
      (finiteHistoryGaussianPseudoRegret_ne_top changedEnvironment
        (horizon - 1) history) hforce
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    simpa [gaussianRandomPseudoRegret, hround] using hreal
  have hsum : 2 * delta <=
      P.real
          (tailAtLeast
            (gaussianRandomPseudoRegret baseEnvironment (horizon - 1))
            (stochasticHighProbabilityThreshold
              horizon alternatives B delta)) +
        Q.real
          (tailAtLeast
            (gaussianRandomPseudoRegret changedEnvironment (horizon - 1))
            (stochasticHighProbabilityThreshold
              horizon alternatives B delta)) := by
    exact htesting'.trans
      (add_le_add (measureReal_mono hbaseSubset)
        (measureReal_mono hchangedSubset))
  by_cases hbase : delta <=
      P.real
        (tailAtLeast
          (gaussianRandomPseudoRegret baseEnvironment (horizon - 1))
          (stochasticHighProbabilityThreshold
            horizon alternatives B delta))
  · exact ⟨baseEnvironment, hbase⟩
  · have hchanged : delta <=
        Q.real
          (tailAtLeast
            (gaussianRandomPseudoRegret changedEnvironment (horizon - 1))
            (stochasticHighProbabilityThreshold
              horizon alternatives B delta)) := by
      have hbaseLt := lt_of_not_ge hbase
      nlinarith
    exact ⟨changedEnvironment, hchanged⟩

/-- **Lattimore--Szepesvari, Theorem 17.1.**  A single policy whose
deterministic expected pseudo-regret is uniformly at most
`B * sqrt ((k-1) * n)` on the unit-cube subfamily has a unit-Gaussian
environment whose random pseudo-regret exceeds the exact source threshold
with probability at least `delta`.

This internal theorem is stronger than the printed result because it assumes
the uniform bound only on the unit-cube Gaussian subfamily used by the proof.
The public source-class wrapper below restores the printed `E^k` premise. -/
theorem gaussianRandomPseudoRegret_ge_theorem17_1_unitCube
    {alternatives horizon : Nat}
    (halternatives : 0 < alternatives) (hhorizon : 0 < horizon)
    (B delta : Real) (hB : 0 < B) (hdelta : 0 < delta)
    (hdelta_one : delta < 1)
    (algorithm : Thompson.HistoryAlgorithm (Fin (alternatives + 1)) Real)
    (hExpected : forall environment :
        UnitGaussianBanditEnvironment (alternatives + 1),
      gaussianExpectedPseudoRegretReal algorithm environment (horizon - 1) <=
        B * Real.sqrt
          ((alternatives : Real) * (horizon : Real))) :
    exists environment : UnitGaussianBanditEnvironment (alternatives + 1),
      delta <=
        (canonicalBanditHistoryMeasure algorithm
          (unitGaussianKernel environment.mean) (horizon - 1)).real
        (tailAtLeast
          (gaussianRandomPseudoRegret environment (horizon - 1))
          (stochasticHighProbabilityThreshold
            horizon alternatives B delta)) := by
  by_cases hfourDelta : 4 * delta < 1
  · exact gaussianRandomPseudoRegret_ge_theorem17_1_of_four_mul_delta_lt_one
      halternatives hhorizon B delta hB hdelta hfourDelta algorithm hExpected
  · have hone_le : 1 <= 4 * delta := le_of_not_gt hfourDelta
    have hdenom : 0 < 4 * delta := by positivity
    have harg_le : 1 / (4 * delta) <= 1 := by
      exact (div_le_one hdenom).2 hone_le
    have hlog : Real.log (1 / (4 * delta)) <= 0 :=
      Real.log_nonpos (by positivity) harg_le
    have hsourceTerm :
        (1 / B) *
            Real.sqrt ((alternatives : Real) * (horizon : Real)) *
              Real.log (1 / (4 * delta)) <= 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
    have hthreshold :
        stochasticHighProbabilityThreshold horizon alternatives B delta <= 0 := by
      unfold stochasticHighProbabilityThreshold
      have hmin : min (horizon : Real)
          ((1 / B) *
            Real.sqrt ((alternatives : Real) * (horizon : Real)) *
              Real.log (1 / (4 * delta))) <= 0 :=
        (min_le_right _ _).trans hsourceTerm
      exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hmin
    let environment := gaussianMinimaxBaseEnvironment
      (m := alternatives) 0 (by norm_num) (by norm_num)
    refine ⟨environment, ?_⟩
    have htail :
        tailAtLeast
          (gaussianRandomPseudoRegret environment (horizon - 1))
          (stochasticHighProbabilityThreshold
            horizon alternatives B delta) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro history
      exact hthreshold.trans
        (gaussianRandomPseudoRegret_nonneg environment (horizon - 1) history)
    rw [htail, probReal_univ]
    exact hdelta_one.le

/-- Theorem 17.1 with the premise quantified over the full source class
`E^k` of unit-variance Gaussian bandits whose gaps are at most one.  The hard
witness lies in the unit-cube subfamily, which is embedded into `E^k`. -/
theorem gaussianRandomPseudoRegret_ge_theorem17_1
    {alternatives horizon : Nat}
    (halternatives : 0 < alternatives) (hhorizon : 0 < horizon)
    (B delta : Real) (hB : 0 < B) (hdelta : 0 < delta)
    (hdelta_one : delta < 1)
    (algorithm : Thompson.HistoryAlgorithm (Fin (alternatives + 1)) Real)
    (hExpected : forall environment :
        GapOneGaussianBanditEnvironment (alternatives + 1),
      gapOneGaussianExpectedPseudoRegretReal algorithm environment (horizon - 1) <=
        B * Real.sqrt
          ((alternatives : Real) * (horizon : Real))) :
    exists environment : UnitGaussianBanditEnvironment (alternatives + 1),
      delta <=
        (canonicalBanditHistoryMeasure algorithm
          (unitGaussianKernel environment.mean) (horizon - 1)).real
        (tailAtLeast
          (gaussianRandomPseudoRegret environment (horizon - 1))
          (stochasticHighProbabilityThreshold
            horizon alternatives B delta)) := by
  apply gaussianRandomPseudoRegret_ge_theorem17_1_unitCube
    halternatives hhorizon B delta hB hdelta hdelta_one algorithm
  intro environment
  simpa using hExpected environment.toGapOne

/-- The square-root identity used to specialize Theorem 17.1 in Corollary
17.2.  Keeping it separate makes the source constant `B = sqrt (2 log
(1/(4δ)))` mechanically visible. -/
theorem stochasticMinimax_sourceTerm_eq
    {horizon alternatives : Nat} (delta : Real)
    (hlog : 0 < Real.log (1 / (4 * delta))) :
    (1 / Real.sqrt (2 * Real.log (1 / (4 * delta)))) *
          Real.sqrt ((alternatives : Real) * (horizon : Real)) *
          Real.log (1 / (4 * delta)) =
      Real.sqrt
        (((horizon : Real) * (alternatives : Real) / 2) *
          Real.log (1 / (4 * delta))) := by
  let L := Real.log (1 / (4 * delta))
  have hL : 0 < L := hlog
  have hsqrt : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.2 (by positivity)
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  rw [Real.sq_sqrt (by positivity)]
  have hroot : Real.sqrt ((alternatives : Real) * (horizon : Real)) ^ 2 =
      (alternatives : Real) * (horizon : Real) :=
    Real.sq_sqrt (by positivity)
  have hsqrtSq : Real.sqrt (2 * L) ^ 2 = 2 * L :=
    Real.sq_sqrt (by positivity)
  dsimp [L] at hsqrt hroot ⊢
  dsimp [L] at hsqrtSq
  field_simp [hsqrt.ne']
  nlinarith [hroot, hsqrtSq]

/-- The Theorem 17.1 threshold at the source choice of `B` is exactly the
Corollary 17.2 minimax threshold. -/
theorem stochasticHighProbabilityThreshold_at_minimax_scale
    {horizon alternatives : Nat} (delta : Real)
    (hlog : 0 < Real.log (1 / (4 * delta))) :
    stochasticHighProbabilityThreshold horizon alternatives
        (Real.sqrt (2 * Real.log (1 / (4 * delta)))) delta =
      stochasticMinimaxHighProbabilityThreshold horizon alternatives delta := by
  unfold stochasticHighProbabilityThreshold
    stochasticMinimaxHighProbabilityThreshold
  rw [stochasticMinimax_sourceTerm_eq delta hlog]

theorem stochasticMinimaxHighProbabilityThreshold_le_quarter_root
    {horizon alternatives : Nat} (delta : Real)
    (hlog : 0 <= Real.log (1 / (4 * delta))) :
    stochasticMinimaxHighProbabilityThreshold horizon alternatives delta <=
      (1 / 4 : Real) * Real.sqrt
        ((horizon : Real) * (alternatives : Real) *
          Real.log (1 / (4 * delta))) := by
  unfold stochasticMinimaxHighProbabilityThreshold
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (min_le_right _ _).trans ?_
  apply Real.sqrt_le_sqrt
  have hn : 0 <= (horizon : Real) := by positivity
  have hm : 0 <= (alternatives : Real) := by positivity
  have hproduct : 0 <=
      (horizon : Real) * (alternatives : Real) *
        Real.log (1 / (4 * delta)) := by positivity
  nlinarith

theorem minimax_expected_scale_identity
    {horizon alternatives : Nat} (delta : Real)
    (hlog : 0 <= Real.log (1 / (4 * delta))) :
    Real.sqrt (2 * Real.log (1 / (4 * delta))) *
        Real.sqrt ((alternatives : Real) * (horizon : Real)) =
      Real.sqrt 2 * Real.sqrt
        ((horizon : Real) * (alternatives : Real) *
          Real.log (1 / (4 * delta))) := by
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  rw [mul_pow, mul_pow]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  ring

/-- The analytic inequality quoted in Corollary 17.3:
`integral_0^infinity exp (-x^(1/p)) dx <= 1` for `0<p<1`.  The change of
variables identifies the integral with `Gamma (p+1)`; convexity of Gamma
between one and two gives the bound. -/
theorem integral_exp_neg_rpow_inv_le_one
    {p : Real} (hp : 0 < p) (hp_one : p < 1) :
    (∫ x : Real in Set.Ioi 0, Real.exp (-(x ^ (1 / p)))) <= 1 := by
  have hchange := integral_comp_rpow_Ioi_of_pos
    (g := fun y : Real => Real.exp (-(y ^ (1 / p)))) hp
  rw [← hchange]
  calc
    (∫ x : Real in Set.Ioi 0,
        (p * x ^ (p - 1)) • Real.exp (-((x ^ p) ^ (1 / p)))) =
      ∫ x : Real in Set.Ioi 0,
        p * (Real.exp (-x) * x ^ (p - 1)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
          have hpCancel : p * (1 / p) = 1 := by
            field_simp [hp.ne']
          rw [← Real.rpow_mul hx.le, hpCancel, Real.rpow_one]
          simp only [smul_eq_mul]
          ring
    _ = p * Real.Gamma p := by
      rw [integral_const_mul, Real.Gamma_eq_integral hp]
    _ = Real.Gamma (p + 1) := (Real.Gamma_add_one hp.ne').symm
    _ <= 1 := by
      have hsegment : p + 1 ∈ segment Real (1 : Real) 2 := by
        rw [segment_eq_uIcc, uIcc_of_le (by norm_num : (1 : Real) <= 2)]
        constructor <;> linarith
      have hgamma := Real.convexOn_Gamma.le_on_segment
        (by simp) (by norm_num) hsegment
      simpa [Real.Gamma_one, Real.Gamma_two] using hgamma

/-- **Lattimore--Szepesvari, Corollary 17.2.**  Under the exact side condition
in Eq. (17.6), every policy has a unit-Gaussian instance whose random
pseudo-regret reaches the minimax high-probability threshold with probability
at least `delta`. -/
theorem gaussianRandomPseudoRegret_ge_corollary17_2
    {alternatives horizon : Nat}
    (halternatives : 0 < alternatives) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (hside : (horizon : Real) * delta <=
      Real.sqrt
        ((horizon : Real) * (alternatives : Real) *
          Real.log (1 / (4 * delta))))
    (algorithm : Thompson.HistoryAlgorithm (Fin (alternatives + 1)) Real) :
    exists environment : UnitGaussianBanditEnvironment (alternatives + 1),
      delta <=
        (canonicalBanditHistoryMeasure algorithm
          (unitGaussianKernel environment.mean) (horizon - 1)).real
        (tailAtLeast
          (gaussianRandomPseudoRegret environment (horizon - 1))
          (stochasticMinimaxHighProbabilityThreshold
            horizon alternatives delta)) := by
  have hfourDelta : 4 * delta < 1 := by
    by_contra hnot
    have hone : 1 <= 4 * delta := le_of_not_gt hnot
    have harg : 1 / (4 * delta) <= 1 := by
      exact (div_le_one (by positivity)).2 hone
    have hlogNonpos : Real.log (1 / (4 * delta)) <= 0 :=
      Real.log_nonpos (by positivity) harg
    have hradicand :
        (horizon : Real) * (alternatives : Real) *
            Real.log (1 / (4 * delta)) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogNonpos
    rw [Real.sqrt_eq_zero_of_nonpos hradicand] at hside
    have : 0 < (horizon : Real) * delta := by positivity
    linarith
  have harg : 1 < 1 / (4 * delta) := by
    rw [one_lt_div₀]
    · exact hfourDelta
    · positivity
  have hlog : 0 < Real.log (1 / (4 * delta)) := Real.log_pos harg
  let B := Real.sqrt (2 * Real.log (1 / (4 * delta)))
  have hB : 0 < B := Real.sqrt_pos.2 (by positivity)
  by_contra hnone
  push Not at hnone
  have hExpected : forall environment :
      UnitGaussianBanditEnvironment (alternatives + 1),
      gaussianExpectedPseudoRegretReal algorithm environment (horizon - 1) <=
        B * Real.sqrt ((alternatives : Real) * (horizon : Real)) := by
    intro environment
    let mu := canonicalBanditHistoryMeasure algorithm
      (unitGaussianKernel environment.mean) (horizon - 1)
    let threshold := stochasticMinimaxHighProbabilityThreshold
      horizon alternatives delta
    have hthreshold : 0 <= threshold := by
      dsimp [threshold, stochasticMinimaxHighProbabilityThreshold]
      positivity
    have htail : mu.real
        (tailAtLeast
          (gaussianRandomPseudoRegret environment (horizon - 1)) threshold) <
        delta := by
      exact hnone environment
    have hbound : forall history,
        gaussianRandomPseudoRegret environment (horizon - 1) history <=
          (horizon : Real) := by
      intro history
      simpa [Nat.sub_add_cancel hhorizon] using
        gaussianRandomPseudoRegret_le_horizon
          environment (horizon - 1) history
    have hintegral :
        ∫ history, gaussianRandomPseudoRegret environment (horizon - 1) history ∂mu <=
          threshold + (horizon : Real) * mu.real
            (tailAtLeast
              (gaussianRandomPseudoRegret environment (horizon - 1)) threshold) := by
      exact integral_le_threshold_add_bound_mul_tailMass
        mu (gaussianRandomPseudoRegret environment (horizon - 1))
        threshold (horizon : Real)
        (measurable_gaussianRandomPseudoRegret environment (horizon - 1))
        (integrable_gaussianRandomPseudoRegret
          algorithm environment (horizon - 1))
        hthreshold hbound
    have hquarter := stochasticMinimaxHighProbabilityThreshold_le_quarter_root
      (horizon := horizon) (alternatives := alternatives) delta hlog.le
    have hsqrtTwo : (5 / 4 : Real) <= Real.sqrt 2 := by
      have hs := Real.sq_sqrt (show (0 : Real) <= 2 by norm_num)
      have hs0 := Real.sqrt_nonneg (2 : Real)
      nlinarith
    rw [← integral_gaussianRandomPseudoRegret_eq_expected
      algorithm environment (horizon - 1)]
    calc
      ∫ history, gaussianRandomPseudoRegret environment (horizon - 1) history ∂mu <=
          threshold + (horizon : Real) * mu.real
            (tailAtLeast
              (gaussianRandomPseudoRegret environment (horizon - 1)) threshold) :=
        hintegral
      _ <= threshold + (horizon : Real) * delta := by
        gcongr
      _ <= (1 / 4 : Real) * Real.sqrt
            ((horizon : Real) * (alternatives : Real) *
              Real.log (1 / (4 * delta))) +
          Real.sqrt
            ((horizon : Real) * (alternatives : Real) *
              Real.log (1 / (4 * delta))) :=
        add_le_add hquarter hside
      _ = (5 / 4 : Real) * Real.sqrt
            ((horizon : Real) * (alternatives : Real) *
              Real.log (1 / (4 * delta))) := by ring
      _ <= Real.sqrt 2 * Real.sqrt
            ((horizon : Real) * (alternatives : Real) *
              Real.log (1 / (4 * delta))) := by
        exact mul_le_mul_of_nonneg_right hsqrtTwo (by positivity)
      _ = B * Real.sqrt
            ((alternatives : Real) * (horizon : Real)) := by
        exact (minimax_expected_scale_identity
          (horizon := horizon) (alternatives := alternatives) delta hlog.le).symm
  obtain ⟨environment, htail⟩ := gaussianRandomPseudoRegret_ge_theorem17_1_unitCube
    halternatives hhorizon B delta hB hdelta hdelta_one algorithm hExpected
  rw [stochasticHighProbabilityThreshold_at_minimax_scale delta hlog] at htail
  exact (not_lt_of_ge htail) (hnone environment)

/-- Claim 17.5 in its abstract first-moment form.  If the average tail mass is
at least `delta`, some deterministic instance has tail mass at least `delta`.

The textbook suppresses the regularity needed to write the expectation.  Lean
makes it explicit as `Integrable tailMass Q`; `Q` is explicitly a probability
measure. -/
theorem exists_tailMass_ge_of_integral_ge
    {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (tailMass : Instance -> Real) (delta : Real)
    (hIntegrable : Integrable tailMass Q)
    (hAverage : delta <= ∫ x, tailMass x ∂Q) :
    exists x, delta <= tailMass x := by
  obtain ⟨x, hx⟩ := exists_integral_le hIntegrable
  exact ⟨x, hAverage.trans hx⟩

/-- Claim 17.5 specialized to the source notation `1 - F_x(u)`. -/
theorem exists_cdfTail_ge_of_integral_ge
    {Instance : Type*} [MeasurableSpace Instance]
    (Q : Measure Instance) [IsProbabilityMeasure Q]
    (cdf : Instance -> Real -> Real) (threshold delta : Real)
    (hIntegrable : Integrable (fun x => 1 - cdf x threshold) Q)
    (hAverage :
      delta <= ∫ x, 1 - cdf x threshold ∂Q) :
    exists x, delta <= 1 - cdf x threshold := by
  exact exists_tailMass_ge_of_integral_ge Q
    (fun x => 1 - cdf x threshold) delta hIntegrable hAverage

/-- Probability subtraction used after Claims 17.6 and 17.7.  If the
pull-count event has probability at least `2 * delta` and the clipping event
has probability at most `delta`, their good difference has probability at
least `delta`.

No measurability hypothesis is hidden: `Measure.real` is defined for all sets,
and `le_measureReal_diff` is an outer-measure inequality. -/
theorem measureReal_diff_ge_delta
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P]
    (pullSmall clippingBad : Set Omega) (delta : Real)
    (hPullSmall : 2 * delta <= P.real pullSmall)
    (hClippingBad : P.real clippingBad <= delta) :
    delta <= P.real (pullSmall \ clippingBad) := by
  have hDiff :
      P.real pullSmall - P.real clippingBad <=
        P.real (pullSmall \ clippingBad) :=
    le_measureReal_diff
  linarith

/-- The deterministic lower expression on the right-hand side of Eq. (17.8),
after writing the pull and clipping counts as real numbers. -/
def adversarialRegretLowerExpression
    (horizon pullCount clippingCount : Nat) (gap : Real) : Real :=
  gap *
    ((horizon : Real) - (pullCount : Real) - (clippingCount : Real))

/-- If fewer than half of the rounds pull the distinguished arm and at most a
quarter are clipped, the Eq. (17.8) lower expression is at least one quarter
of `gap * horizon`. -/
theorem adversarialRegretLowerExpression_ge_quarter
    (horizon pullCount clippingCount : Nat) (gap : Real)
    (hGap : 0 <= gap)
    (hPull : (pullCount : Real) <= (horizon : Real) / 2)
    (hClipping : (clippingCount : Real) <= (horizon : Real) / 4) :
    gap * ((horizon : Real) / 4) <=
      adversarialRegretLowerExpression horizon pullCount clippingCount gap := by
  unfold adversarialRegretLowerExpression
  apply mul_le_mul_of_nonneg_left _ hGap
  linarith

/-- The explicit transfer from Eq. (17.8) to the quarter-horizon regret
threshold.  The premise `hSource` is exactly the construction-specific part
that Chapter 17 must still supply. -/
theorem randomRegret_ge_quarter_of_clippingDecomposition
    (horizon pullCount clippingCount : Nat) (gap randomRegret : Real)
    (hGap : 0 <= gap)
    (hPull : (pullCount : Real) <= (horizon : Real) / 2)
    (hClipping : (clippingCount : Real) <= (horizon : Real) / 4)
    (hSource :
      adversarialRegretLowerExpression horizon pullCount clippingCount gap <=
        randomRegret) :
    gap * ((horizon : Real) / 4) <= randomRegret :=
  (adversarialRegretLowerExpression_ge_quarter horizon pullCount clippingCount
    gap hGap hPull hClipping).trans hSource

/-! ### The correlated clipped-Gaussian hard family and Eq. (17.8) -/

/-- Clipping to the reward interval `[0,1]`. -/
def clipUnitReward (x : Real) : Real := max 0 (min 1 x)

theorem clipUnitReward_mono {x y : Real} (hxy : x <= y) :
    clipUnitReward x <= clipUnitReward y := by
  unfold clipUnitReward
  exact max_le_max (le_refl 0) (min_le_min (le_refl 1) hxy)

theorem clipUnitReward_eq_self {x : Real} (hx0 : 0 <= x) (hx1 : x <= 1) :
    clipUnitReward x = x := by
  simp [clipUnitReward, min_eq_right hx1, max_eq_right hx0]

/-- The source hard-family shift: arm zero receives `gap`, the distinguished
nonzero arm receives `2*gap`, and every other arm receives zero. -/
def adversarialHardShift {alternatives : Nat}
    (gap : Real) (distinguished : Fin alternatives)
    (arm : Fin (alternatives + 1)) : Real :=
  if arm = 0 then gap else if arm = distinguished.succ then 2 * gap else 0

/-- The exact pre-sampled construction underlying Theorem 17.4.  One scalar
`eta t` is shared by every arm at round `t`; hence the arm rewards are
correlated within a round.  Independence and standard-Gaussian assumptions
belong to the law of the path `eta`, not to this pathwise definition. -/
def adversarialClippedGaussianReward
    {horizon alternatives : Nat}
    (eta : Fin horizon -> Real) (gap : Real)
    (distinguished : Fin alternatives)
    (t : Fin horizon) (arm : Fin (alternatives + 1)) : Real :=
  clipUnitReward (1 / 2 + eta t + adversarialHardShift gap distinguished arm)

/-- The IID centered-Gaussian path law used by the equivalent centered form
of the source construction.  Adding `1/2` in
`adversarialClippedGaussianReward` makes `1/2 + eta t` have the source law
`N(1/2, sigma^2)`. -/
noncomputable def adversarialCenteredNoiseLaw
    (horizon : Nat) (sigma : Real) : Measure (Fin horizon -> Real) :=
  Measure.pi fun _ : Fin horizon =>
    ProbabilityTheory.gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩

/-- The exact source tuning from Claim 17.6, with
`alternatives = k - 1`. -/
noncomputable def adversarialClaim17_6Gap
    (horizon alternatives : Nat) (sigma delta : Real) : Real :=
  sigma * Real.sqrt
    (((alternatives : Real) / (2 * (horizon : Real))) *
      Real.log (1 / (8 * delta)))

theorem adversarialHardShift_distinguished
    {alternatives : Nat} (gap : Real) (distinguished : Fin alternatives) :
    adversarialHardShift gap distinguished distinguished.succ = 2 * gap := by
  simp [adversarialHardShift, Fin.succ_ne_zero]

theorem adversarialHardShift_nonneg
    {alternatives : Nat} (gap : Real) (hgap : 0 <= gap)
    (distinguished : Fin alternatives) (arm : Fin (alternatives + 1)) :
    0 <= adversarialHardShift gap distinguished arm := by
  by_cases hzero : arm = 0
  · simp [adversarialHardShift, hzero, hgap]
  · by_cases hdist : arm = distinguished.succ
    · simp [adversarialHardShift, hdist, hgap]
    · simp [adversarialHardShift, hzero, hdist]

theorem adversarialHardShift_le_two_mul
    {alternatives : Nat} (gap : Real) (hgap : 0 <= gap)
    (distinguished : Fin alternatives) (arm : Fin (alternatives + 1)) :
    adversarialHardShift gap distinguished arm <= 2 * gap := by
  by_cases hzero : arm = 0
  · simp [adversarialHardShift, hzero]
    linarith
  · by_cases hdist : arm = distinguished.succ
    · simp [adversarialHardShift, hdist]
    · simp [adversarialHardShift, hzero, hdist]
      linarith

theorem adversarialHardShift_le_gap_of_ne
    {alternatives : Nat} (gap : Real) (hgap : 0 <= gap)
    (distinguished : Fin alternatives) (arm : Fin (alternatives + 1))
    (hne : arm ≠ distinguished.succ) :
    adversarialHardShift gap distinguished arm <= gap := by
  simp [adversarialHardShift, hne]
  split <;> linarith

theorem adversarialClippedGaussianReward_distinguished_mono
    {horizon alternatives : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (hgap : 0 <= gap)
    (distinguished : Fin alternatives) (t : Fin horizon)
    (arm : Fin (alternatives + 1)) :
    adversarialClippedGaussianReward eta gap distinguished t arm <=
      adversarialClippedGaussianReward eta gap distinguished t distinguished.succ := by
  apply clipUnitReward_mono
  rw [adversarialHardShift_distinguished]
  have hshift := adversarialHardShift_le_two_mul
    gap hgap distinguished arm
  linarith

/-- Away from clipping, the distinguished arm beats every other arm by at
least `gap`.  This is the pointwise engine of Eq. (17.8). -/
theorem adversarialClippedGaussianReward_gap_of_not_clipped
    {horizon alternatives : Nat}
    (eta : Fin horizon -> Real) (gap : Real)
    (hgap : 0 <= gap)
    (distinguished : Fin alternatives) (t : Fin horizon)
    (arm : Fin (alternatives + 1)) (hne : arm ≠ distinguished.succ)
    (hgood : |eta t| < 1 / 2 - 2 * gap) :
    gap <= adversarialClippedGaussianReward eta gap distinguished t distinguished.succ -
      adversarialClippedGaussianReward eta gap distinguished t arm := by
  have heta := (abs_lt.mp hgood)
  have hshift0 := adversarialHardShift_nonneg gap hgap distinguished arm
  have hshift2 := adversarialHardShift_le_two_mul gap hgap distinguished arm
  have hi0 : 0 <= 1 / 2 + eta t +
      adversarialHardShift gap distinguished arm := by
    linarith
  have hi1 : 1 / 2 + eta t +
      adversarialHardShift gap distinguished arm <= 1 := by
    linarith
  have hd0 : 0 <= 1 / 2 + eta t + 2 * gap := by linarith
  have hd1 : 1 / 2 + eta t + 2 * gap <= 1 := by linarith
  have hd : adversarialClippedGaussianReward eta gap distinguished t
      distinguished.succ = 1 / 2 + eta t + 2 * gap := by
    unfold adversarialClippedGaussianReward
    rw [adversarialHardShift_distinguished,
      clipUnitReward_eq_self hd0 hd1]
  have hi : adversarialClippedGaussianReward eta gap distinguished t arm =
      1 / 2 + eta t + adversarialHardShift gap distinguished arm := by
    unfold adversarialClippedGaussianReward
    rw [clipUnitReward_eq_self hi0 hi1]
  rw [hd, hi]
  have hshiftGap := adversarialHardShift_le_gap_of_ne
    gap hgap distinguished arm hne
  linarith

def adversarialPullCountReal
    {horizon alternatives : Nat}
    (actions : Fin horizon -> Fin (alternatives + 1))
    (distinguished : Fin alternatives) : Real :=
  ∑ t, if actions t = distinguished.succ then 1 else 0

def adversarialClippingCountReal
    {horizon : Nat} (eta : Fin horizon -> Real) (gap : Real) : Real :=
  ∑ t, if 1 / 2 - 2 * gap <= |eta t| then 1 else 0

def adversarialComparatorRegret
    {horizon alternatives : Nat}
    (reward : Fin horizon -> Fin (alternatives + 1) -> Real)
    (actions : Fin horizon -> Fin (alternatives + 1))
    (comparator : Fin (alternatives + 1)) : Real :=
  ∑ t : Fin horizon, (reward t comparator - reward t (actions t))

/-- Adversarial random regret: the best fixed arm in hindsight minus the
reward collected along the realized action path. -/
noncomputable def adversarialRandomRegret
    {horizon alternatives : Nat}
    (reward : Fin horizon -> Fin (alternatives + 1) -> Real)
    (actions : Fin horizon -> Fin (alternatives + 1)) : Real :=
  (Finset.univ : Finset (Fin (alternatives + 1))).sup'
    ⟨0, Finset.mem_univ 0⟩
    (adversarialComparatorRegret reward actions)

theorem adversarialComparatorRegret_le_randomRegret
    {horizon alternatives : Nat}
    (reward : Fin horizon -> Fin (alternatives + 1) -> Real)
    (actions : Fin horizon -> Fin (alternatives + 1))
    (comparator : Fin (alternatives + 1)) :
    adversarialComparatorRegret reward actions comparator <=
      adversarialRandomRegret reward actions := by
  unfold adversarialRandomRegret
  exact Finset.le_sup' _ (Finset.mem_univ comparator)

/-- **Equation (17.8), construction level.**  For every realized shared-noise
path and every action path, regret against the distinguished arm is bounded
below by `gap * (n - T_i(n) - C)`, where `C` counts clipping rounds. -/
theorem adversarialComparatorRegret_ge_eq17_8
    {horizon alternatives : Nat}
    (eta : Fin horizon -> Real) (gap : Real)
    (hgap : 0 <= gap)
    (distinguished : Fin alternatives)
    (actions : Fin horizon -> Fin (alternatives + 1)) :
    gap * ((horizon : Real) -
        adversarialPullCountReal actions distinguished -
        adversarialClippingCountReal eta gap) <=
      adversarialComparatorRegret
        (adversarialClippedGaussianReward eta gap distinguished)
        actions distinguished.succ := by
  have hterm : forall t : Fin horizon,
      gap * (1 - (if actions t = distinguished.succ then 1 else 0) -
          (if 1 / 2 - 2 * gap <= |eta t| then 1 else 0)) <=
        adversarialClippedGaussianReward eta gap distinguished t distinguished.succ -
          adversarialClippedGaussianReward eta gap distinguished t (actions t) := by
    intro t
    by_cases hpull : actions t = distinguished.succ
    · rw [hpull, if_pos rfl]
      split <;> simp_all
    · by_cases hclip : 1 / 2 - 2 * gap <= |eta t|
      · rw [if_neg hpull, if_pos hclip]
        norm_num
        exact adversarialClippedGaussianReward_distinguished_mono
          eta gap hgap distinguished t (actions t)
      · rw [if_neg hpull, if_neg hclip]
        norm_num
        exact adversarialClippedGaussianReward_gap_of_not_clipped
          eta gap hgap distinguished t (actions t) hpull
          (lt_of_not_ge hclip)
  calc
    gap * ((horizon : Real) -
        adversarialPullCountReal actions distinguished -
        adversarialClippingCountReal eta gap) =
      ∑ t : Fin horizon,
        gap * (1 - (if actions t = distinguished.succ then 1 else 0) -
          (if 1 / 2 - 2 * gap <= |eta t| then 1 else 0)) := by
        rw [show (horizon : Real) = ∑ _t : Fin horizon, (1 : Real) by simp]
        unfold adversarialPullCountReal adversarialClippingCountReal
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
          Finset.mul_sum]
    _ <= adversarialComparatorRegret
        (adversarialClippedGaussianReward eta gap distinguished)
        actions distinguished.succ := by
      unfold adversarialComparatorRegret
      exact Finset.sum_le_sum fun t _ => hterm t

/-- Eq. (17.8) in the textbook's actual random-regret form. -/
theorem adversarialRandomRegret_ge_eq17_8
    {horizon alternatives : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (hgap : 0 <= gap)
    (distinguished : Fin alternatives)
    (actions : Fin horizon -> Fin (alternatives + 1)) :
    gap * ((horizon : Real) -
        adversarialPullCountReal actions distinguished -
        adversarialClippingCountReal eta gap) <=
      adversarialRandomRegret
        (adversarialClippedGaussianReward eta gap distinguished) actions :=
  (adversarialComparatorRegret_ge_eq17_8
    eta gap hgap distinguished actions).trans
      (adversarialComparatorRegret_le_randomRegret
        (adversarialClippedGaussianReward eta gap distinguished)
        actions distinguished.succ)

end

end LowerBounds
end BanditRLProof
