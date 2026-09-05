import BanditRLProof.LowerBounds.InstanceDependent
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.Linarith

/-!
# High-probability lower-bound interfaces

This module formalizes the source-faithful threshold surfaces and reusable
probability/algebra leaves from Lattimore--Szepesvari, *Bandit Algorithms*
(2020), Part IV, Chapter 17.

The file closes Theorem 17.1 and Corollaries 17.2--17.3 on the canonical adaptive
history law, and keeps their random pseudo-regret separate from deterministic
expected pseudo-regret.  It also formalizes Claim 17.5, the exact correlated
clipped-Gaussian path construction, and Eq. (17.8) for adversarial random
regret. Claim 17.7 is closed at the textbook constants. The user-approved
correction of Claim 17.6 uses a non-strict half-pull event. Corrected Theorem
17.4 has `0 < delta <= 1/32`, `c=1/160`, `C=64`, a deterministic bounded
reward-table witness, and the strict CDF-complement tail. The same-policy
coupling is proved, and fixed-table random regret is measurable and integrable;
the false printed strict claim and full confidence domain are not asserted.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory Set
open scoped ENNReal NNReal
open ProbabilityTheory

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

/-- The stochastic random pseudo-regret on the full source class `E^k`.
Unlike `gapOneGaussianExpectedPseudoRegretReal`, this is a random variable on
the realized finite history. -/
noncomputable def gapOneGaussianRandomPseudoRegret
    {K : Nat} (environment : GapOneGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) : Real :=
  ∑ arm : Fin K,
    (environment.mean environment.bestArm - environment.mean arm) *
      finiteHistoryPullCountReal lastRound history arm

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

@[simp]
theorem gapOneGaussianRandomPseudoRegret_toGapOne
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) :
    gapOneGaussianRandomPseudoRegret environment.toGapOne lastRound history =
      gaussianRandomPseudoRegret environment lastRound history := by
  rw [gaussianRandomPseudoRegret,
    finiteHistoryGaussianPseudoRegret_toReal]
  rfl

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

/-- Integrating an all-confidence stretched-exponential tail gives the
first-moment bound used by Corollary 17.3.  The strict source tail is retained
at the caller; only its weak consequence is needed under the integral. -/
theorem integral_le_scale_of_all_rpow_log_tail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (quantity : Omega -> Real) (scale p : Real)
    (hscale : 0 < scale) (hp : 0 < p) (hp_one : p < 1)
    (hintegrable : Integrable quantity mu)
    (hnonneg : forall omega, 0 <= quantity omega)
    (htail : forall delta : Real, 0 < delta -> delta < 1 ->
      mu.real
        (tailAtLeast quantity
          (scale * (Real.log (1 / delta)) ^ p)) < delta) :
    (∫ omega, quantity omega ∂mu) <= scale := by
  let tail : Real -> Real := fun threshold =>
    mu.real {omega | threshold <= quantity omega}
  have htail_antitone : Antitone tail := by
    intro a b hab
    exact measureReal_mono fun omega homega => hab.trans homega
  have htail_meas : Measurable tail := htail_antitone.measurable
  have hscaled_tail_meas : Measurable (fun x : Real => tail (scale * x)) :=
    htail_meas.comp (measurable_const.mul measurable_id)
  let envelope : Real -> Real := fun x => Real.exp (-(x ^ (1 / p)))
  have hp_inv : (1 : Real) <= 1 / p := by
    rw [le_div_iff₀ hp]
    simpa using hp_one.le
  have henvelope_integrable : IntegrableOn envelope (Set.Ioi 0) := by
    simpa [envelope] using
      (integrableOn_rpow_mul_exp_neg_rpow
        (p := 1 / p) (s := 0) (by norm_num) hp_inv)
  have htail_envelope : forall x : Real, x ∈ Set.Ioi (0 : Real) ->
      tail (scale * x) < envelope x := by
    intro x hx
    let delta : Real := Real.exp (-(x ^ (1 / p)))
    have hxpow : 0 < x ^ (1 / p) := Real.rpow_pos_of_pos hx (1 / p)
    have hdelta : 0 < delta := Real.exp_pos _
    have hdelta_one : delta < 1 := by
      dsimp [delta]
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hxpow)
    have hlog : Real.log (1 / delta) = x ^ (1 / p) := by
      dsimp [delta]
      rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    have hpower : (Real.log (1 / delta)) ^ p = x := by
      rw [hlog, ← Real.rpow_mul hx.le]
      have hcancel : (1 / p) * p = 1 := by
        field_simp [hp.ne']
      rw [hcancel, Real.rpow_one]
    have h := htail delta hdelta hdelta_one
    change mu.real (tailAtLeast quantity (scale * x)) < delta
    rw [← hpower]
    exact h
  have hscaled_tail_integrable :
      IntegrableOn (fun x : Real => tail (scale * x)) (Set.Ioi 0) := by
    apply henvelope_integrable.mono'
    · exact hscaled_tail_meas.aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact (htail_envelope x hx).le
  rw [hintegrable.integral_eq_integral_meas_le
    (Filter.Eventually.of_forall hnonneg)]
  change (∫ threshold in Set.Ioi 0, tail threshold) <= scale
  have hchange := integral_comp_mul_left_Ioi tail 0 hscale
  simp only [mul_zero, smul_eq_mul] at hchange
  calc
    (∫ threshold in Set.Ioi 0, tail threshold) =
        scale * ∫ x in Set.Ioi 0, tail (scale * x) := by
      rw [hchange]
      field_simp [hscale.ne']
    _ <= scale * ∫ x in Set.Ioi 0, envelope x := by
      apply mul_le_mul_of_nonneg_left _ hscale.le
      exact setIntegral_mono_on hscaled_tail_integrable
        henvelope_integrable measurableSet_Ioi fun x hx =>
          (htail_envelope x hx).le
    _ <= scale * 1 := by
      apply mul_le_mul_of_nonneg_left _ hscale.le
      simpa [envelope] using integral_exp_neg_rpow_inv_le_one hp hp_one
    _ = scale := by ring

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

/-- **Lattimore--Szepesvari, Corollary 17.3.**  No single policy has a
strictly smaller than `delta` random-pseudo-regret tail at every horizon,
confidence level, and environment in the full gap-at-most-one Gaussian class
when the logarithmic exponent lies in `(0,1)`. -/
theorem noUniformGaussianRandomPseudoRegretTail_corollary17_3
    {alternatives : Nat} (halternatives : 0 < alternatives)
    (p B : Real) (hp : 0 < p) (hp_one : p < 1) (hB : 0 < B) :
    ¬ exists algorithm : Thompson.HistoryAlgorithm (Fin (alternatives + 1)) Real,
      forall horizon : Nat, 0 < horizon ->
      forall delta : Real, 0 < delta -> delta < 1 ->
      forall environment : GapOneGaussianBanditEnvironment (alternatives + 1),
        (canonicalBanditHistoryMeasure algorithm
          (unitGaussianKernel environment.mean) (horizon - 1)).real
          (tailAtLeast
            (gapOneGaussianRandomPseudoRegret environment (horizon - 1))
            (B * Real.sqrt
                ((alternatives : Real) * (horizon : Real)) *
              (Real.log (1 / delta)) ^ p)) < delta := by
  rintro ⟨algorithm, huniform⟩
  let q : Real := (1 - p) / p
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos (sub_pos.mpr hp_one) hp
  have hlogFour : 0 < Real.log (4 : Real) := Real.log_pos (by norm_num)
  have heventuallyPower : ∀ᶠ x : Real in Filter.atTop,
      4 * B ^ 2 + Real.log 4 < x ^ q :=
    (tendsto_rpow_atTop hq).eventually (Filter.eventually_gt_atTop _)
  have heventuallyOne : ∀ᶠ x : Real in Filter.atTop, 1 <= x :=
    Filter.eventually_ge_atTop 1
  obtain ⟨x, hxpower, hxone⟩ : exists x : Real,
      4 * B ^ 2 + Real.log 4 < x ^ q ∧ 1 <= x := by
    exact (heventuallyPower.and heventuallyOne).exists
  have hx : 0 < x := zero_lt_one.trans_le hxone
  have hpowerIdentity : x ^ (1 / p) = x * x ^ q := by
    have hexponent : (1 / p : Real) = 1 + q := by
      dsimp [q]
      field_simp [hp.ne']
      ring
    rw [hexponent, Real.rpow_add hx, Real.rpow_one]
  have hpowerLarge :
      4 * B ^ 2 * x + Real.log 4 < x ^ (1 / p) := by
    rw [hpowerIdentity]
    have hmul := mul_lt_mul_of_pos_left hxpower hx
    nlinarith [sq_nonneg B]
  let theoremDelta : Real := Real.exp (-(4 * B ^ 2 * x)) / 4
  let upperDelta : Real := Real.exp (-(x ^ (1 / p)))
  have htheoremDelta : 0 < theoremDelta := by
    dsimp [theoremDelta]
    positivity
  have htheoremDelta_one : theoremDelta < 1 := by
    dsimp [theoremDelta]
    have hexp_le : Real.exp (-(4 * B ^ 2 * x)) <= 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 <= 4 * B ^ 2 * x := by positivity
      linarith
    nlinarith
  have hupperDelta : 0 < upperDelta := by
    dsimp [upperDelta]
    positivity
  have hupperDelta_one : upperDelta < 1 := by
    dsimp [upperDelta]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hx _))
  have hupperDelta_le : upperDelta <= theoremDelta := by
    have hexp : Real.exp (-(x ^ (1 / p))) <=
        Real.exp (-(4 * B ^ 2 * x + Real.log 4)) := by
      rw [Real.exp_le_exp]
      linarith
    calc
      upperDelta = Real.exp (-(x ^ (1 / p))) := rfl
      _ <= Real.exp (-(4 * B ^ 2 * x + Real.log 4)) := hexp
      _ = theoremDelta := by
        dsimp [theoremDelta]
        rw [neg_add, Real.exp_add]
        simp [Real.exp_neg, Real.exp_log]
        rw [div_eq_mul_inv]
  obtain ⟨horizon, hhorizonBound⟩ := exists_nat_ge
    (16 * B ^ 2 * (alternatives : Real) * x ^ 2)
  have hhorizonReal : 0 < (horizon : Real) := by
    have hconstant : 0 <
        16 * B ^ 2 * (alternatives : Real) * x ^ 2 := by
      positivity
    exact hconstant.trans_le hhorizonBound
  have hhorizon : 0 < horizon := by exact_mod_cast hhorizonReal
  let scale : Real :=
    B * Real.sqrt ((alternatives : Real) * (horizon : Real))
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hExpected : forall environment :
      UnitGaussianBanditEnvironment (alternatives + 1),
      gaussianExpectedPseudoRegretReal algorithm environment (horizon - 1) <=
        B * Real.sqrt ((alternatives : Real) * (horizon : Real)) := by
    intro environment
    rw [← integral_gaussianRandomPseudoRegret_eq_expected
      algorithm environment (horizon - 1)]
    exact integral_le_scale_of_all_rpow_log_tail
      (canonicalBanditHistoryMeasure algorithm
        (unitGaussianKernel environment.mean) (horizon - 1))
      (gaussianRandomPseudoRegret environment (horizon - 1))
      scale p hscale hp hp_one
      (integrable_gaussianRandomPseudoRegret
        algorithm environment (horizon - 1))
      (gaussianRandomPseudoRegret_nonneg environment (horizon - 1))
      (by
        intro delta hdelta hdelta_one
        have h := huniform horizon hhorizon delta hdelta hdelta_one
          environment.toGapOne
        have hrandom :
            gapOneGaussianRandomPseudoRegret environment.toGapOne
                (horizon - 1) =
              gaussianRandomPseudoRegret environment (horizon - 1) := by
          funext history
          exact gapOneGaussianRandomPseudoRegret_toGapOne
            environment (horizon - 1) history
        rw [show environment.toGapOne.mean = environment.mean by rfl,
          hrandom] at h
        simpa [scale] using h)
  obtain ⟨environment, hlower⟩ :=
    gaussianRandomPseudoRegret_ge_theorem17_1_unitCube
      halternatives hhorizon B theoremDelta hB htheoremDelta
        htheoremDelta_one algorithm hExpected
  have hlogTheorem : Real.log (1 / (4 * theoremDelta)) =
      4 * B ^ 2 * x := by
    have hfour : 4 * theoremDelta = Real.exp (-(4 * B ^ 2 * x)) := by
      dsimp [theoremDelta]
      ring
    rw [hfour, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hsource_le :
      4 * B * Real.sqrt
          ((alternatives : Real) * (horizon : Real)) * x <=
        (horizon : Real) := by
    rw [← sq_le_sq₀ (by positivity) hhorizonReal.le]
    have hsqrtSq :
        Real.sqrt ((alternatives : Real) * (horizon : Real)) ^ 2 =
          (alternatives : Real) * (horizon : Real) :=
      Real.sq_sqrt (by positivity)
    rw [mul_pow, mul_pow, mul_pow, hsqrtSq]
    nlinarith [hhorizonBound]
  have hthreshold :
      stochasticHighProbabilityThreshold horizon alternatives B theoremDelta =
        scale * x := by
    unfold stochasticHighProbabilityThreshold
    rw [hlogTheorem]
    have hsource :
        (1 / B) *
            Real.sqrt ((alternatives : Real) * (horizon : Real)) *
              (4 * B ^ 2 * x) =
          4 * B * Real.sqrt
            ((alternatives : Real) * (horizon : Real)) * x := by
      field_simp [hB.ne']
    rw [hsource, min_eq_right hsource_le]
    dsimp [scale]
    ring
  have hlogUpper : Real.log (1 / upperDelta) = x ^ (1 / p) := by
    dsimp [upperDelta]
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hupperPower : (Real.log (1 / upperDelta)) ^ p = x := by
    rw [hlogUpper, ← Real.rpow_mul hx.le]
    have hcancel : (1 / p : Real) * p = 1 := by
      field_simp [hp.ne']
    rw [hcancel, Real.rpow_one]
  have hupper := huniform horizon hhorizon upperDelta hupperDelta
    hupperDelta_one environment.toGapOne
  have hrandom :
      gapOneGaussianRandomPseudoRegret environment.toGapOne (horizon - 1) =
        gaussianRandomPseudoRegret environment (horizon - 1) := by
    funext history
    exact gapOneGaussianRandomPseudoRegret_toGapOne
      environment (horizon - 1) history
  rw [show environment.toGapOne.mean = environment.mean by rfl,
    hrandom, hupperPower, ← hthreshold] at hupper
  exact (not_lt_of_ge hupperDelta_le) (hlower.trans_lt hupper)

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

/-- One observed arm's marginal in the clipped Gaussian construction.
The joint reward matrix still uses a shared noise coordinate for all arms. -/
noncomputable def adversarialClippedArmLaw (sigma shift : Real) : Measure Real :=
  (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩).map
    (fun x => clipUnitReward (1 / 2 + x + shift))

theorem measurable_adversarialClippedArmMap (shift : Real) :
    Measurable (fun x : Real => clipUnitReward (1 / 2 + x + shift)) := by
  unfold clipUnitReward
  fun_prop

instance instAdversarialClippedArmLawProbability (sigma shift : Real) :
    IsProbabilityMeasure (adversarialClippedArmLaw sigma shift) := by
  unfold adversarialClippedArmLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_adversarialClippedArmMap shift).aemeasurable

/-- Finite-arm observation kernel, parameterized also for the base family
used in Claim 17.6. -/
noncomputable abbrev adversarialClippedKernel {K : Nat}
    (sigma : Real) (shift : Fin K -> Real) : Kernel (Fin K) Real :=
  Kernel.ofFunOfCountable (fun arm => adversarialClippedArmLaw sigma (shift arm))

instance instAdversarialClippedKernelMarkov {K : Nat}
    (sigma : Real) (shift : Fin K -> Real) :
    IsMarkovKernel (adversarialClippedKernel sigma shift) where
  isProbabilityMeasure arm := instAdversarialClippedArmLawProbability sigma (shift arm)

/-- The observable history law under a fixed randomized policy and the
clipped Gaussian feedback kernel. This is not a law on full reward matrices. -/
noncomputable def adversarialClippedHistoryLaw {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) (lastRound : Nat) :
    Measure (History.FinitePairHistory (Fin K) Real lastRound) :=
  canonicalBanditHistoryMeasure algorithm (adversarialClippedKernel sigma shift) lastRound

instance instAdversarialClippedHistoryLawProbability {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) (lastRound : Nat) :
    IsProbabilityMeasure (adversarialClippedHistoryLaw algorithm sigma shift lastRound) := by
  unfold adversarialClippedHistoryLaw
  infer_instance

/-- A coordinate of the shared-noise matrix has exactly the arm marginal
used by the observation kernel. This retains the original product noise law. -/
theorem adversarialCenteredNoiseLaw_reward_marginal
    {horizon alternatives : Nat} (sigma gap : Real)
    (distinguished : Fin alternatives) (t : Fin horizon)
    (arm : Fin (alternatives + 1)) :
    (adversarialCenteredNoiseLaw horizon sigma).map
      (fun eta => adversarialClippedGaussianReward eta gap distinguished t arm) =
      adversarialClippedArmLaw sigma (adversarialHardShift gap distinguished arm) := by
  unfold adversarialCenteredNoiseLaw adversarialClippedArmLaw
    adversarialClippedGaussianReward
  have hm := measurable_adversarialClippedArmMap
    (adversarialHardShift gap distinguished arm)
  have he := (measurePreserving_eval (fun _ : Fin horizon =>
    gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) t).map_eq
  conv_rhs => rw [← he, Measure.map_map hm (measurable_pi_apply t)]
  rfl

/-- Clip the observed reward coordinates while retaining every action. -/
def adversarialClipHistory {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    History.FinitePairHistory (Fin K) Real n :=
  fun t => ((history t).1, clipUnitReward (history t).2)

theorem measurable_adversarialClipHistory {K : Nat} (n : Nat) :
    Measurable (adversarialClipHistory (K := K) n) := by
  unfold adversarialClipHistory clipUnitReward
  fun_prop

/-- Lift the original policy to unbounded observations by feeding it only
the clipped history. This construction is independent of the hard instance. -/
noncomputable def adversarialClipHistoryAlgorithm {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) :
    Thompson.HistoryAlgorithm (Fin K) Real where
  policy n := (algorithm.policy n).comap (adversarialClipHistory n)
    (measurable_adversarialClipHistory n)
  initialAction := algorithm.initialAction

theorem adversarialClipHistoryAlgorithm_policy_apply {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    (adversarialClipHistoryAlgorithm algorithm).policy n history =
      algorithm.policy n (adversarialClipHistory n history) := by
  rw [adversarialClipHistoryAlgorithm, Kernel.comap_apply]

theorem adversarialClipHistory_pullCount {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    finiteHistoryPullCountENNReal n (adversarialClipHistory n history) arm =
      finiteHistoryPullCountENNReal n history arm := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : Thompson.pairHistoryPrefix (adversarialClipHistory (n + 1) history) =
        adversarialClipHistory n (Thompson.pairHistoryPrefix history) := rfl
    simp only [finiteHistoryPullCountENNReal, hp, ih]
    rfl

theorem adversarialClipHistory_pullCountReal {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    finiteHistoryPullCountReal n (adversarialClipHistory n history) arm =
      finiteHistoryPullCountReal n history arm := by
  unfold finiteHistoryPullCountReal
  rw [adversarialClipHistory_pullCount]

/-- Unclipped feedback law used with the lifted policy. -/
noncomputable abbrev adversarialUnclippedKernel {K : Nat}
    (sigma : Real) (shift : Fin K -> Real) : Kernel (Fin K) Real :=
  Kernel.ofFunOfCountable (fun arm =>
    (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩).map
      (fun x => 1 / 2 + x + shift arm))

instance instAdversarialUnclippedKernelMarkov {K : Nat}
    (sigma : Real) (shift : Fin K -> Real) :
    IsMarkovKernel (adversarialUnclippedKernel sigma shift) where
  isProbabilityMeasure arm := Measure.isProbabilityMeasure_map (by fun_prop)

theorem adversarialClippedKernel_eq_map {K : Nat}
    (sigma : Real) (shift : Fin K -> Real) :
    adversarialClippedKernel sigma shift =
      (adversarialUnclippedKernel sigma shift).map clipUnitReward := by
  have hc : Measurable clipUnitReward := by unfold clipUnitReward; fun_prop
  ext arm : 1
  rw [Kernel.map_apply _ hc]
  change (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩).map
      (fun x => clipUnitReward (1 / 2 + x + shift arm)) =
    ((gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩).map
      (fun x => 1 / 2 + x + shift arm)).map clipUnitReward
  rw [Measure.map_map hc (by fun_prop)]
  rfl

/-- Initial action/reward law transport for the original and lifted policy. -/
theorem adversarialClipped_initialPairLaw {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) :
    algorithm.initialAction ⊗ₘ adversarialClippedKernel sigma shift =
      ((adversarialClipHistoryAlgorithm algorithm).initialAction ⊗ₘ
        adversarialUnclippedKernel sigma shift).map (Prod.map id clipUnitReward) := by
  rw [adversarialClippedKernel_eq_map]
  exact Measure.compProd_map (by unfold clipUnitReward; fun_prop)

/-- The exact observable history transport at the first observation. -/
theorem adversarialClippedHistoryLaw_zero {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) :
    adversarialClippedHistoryLaw algorithm sigma shift 0 =
      (canonicalBanditHistoryMeasure (adversarialClipHistoryAlgorithm algorithm)
        (adversarialUnclippedKernel sigma shift) 0).map (adversarialClipHistory 0) := by
  unfold adversarialClippedHistoryLaw
  rw [canonicalBanditHistoryMeasure_zero, canonicalBanditHistoryMeasure_zero,
    adversarialClipped_initialPairLaw]
  have hp : Measurable (Prod.map (id : Fin K -> Fin K) clipUnitReward) := by
    unfold clipUnitReward
    fun_prop
  rw [Measure.map_map (pairHistoryZeroMeasurableEquiv (Fin K) Real).measurable hp,
    Measure.map_map (measurable_adversarialClipHistory 0)
      (pairHistoryZeroMeasurableEquiv (Fin K) Real).measurable]
  rfl

/-- Pointwise transport of the next action/reward pair after a history. -/
theorem adversarialClipped_historyStepLaw {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    Thompson.historyStepKernel algorithm
        (stationaryBanditHistoryEnvironment (adversarialClippedKernel sigma shift)) n
        (adversarialClipHistory n history) =
      (Thompson.historyStepKernel (adversarialClipHistoryAlgorithm algorithm)
        (stationaryBanditHistoryEnvironment (adversarialUnclippedKernel sigma shift)) n
        history).map (Prod.map id clipUnitReward) := by
  have hs (armLaw : Kernel (Fin K) Real) [IsMarkovKernel armLaw]
      (h : History.FinitePairHistory (Fin K) Real n) :
      Kernel.sectR ((stationaryBanditHistoryEnvironment armLaw).feedback n) h = armLaw := by
    ext arm : 1
    rw [Kernel.sectR_apply, stationaryBanditHistoryEnvironment_feedback_apply]
  unfold Thompson.historyStepKernel
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR, hs, hs,
    adversarialClipHistoryAlgorithm_policy_apply, adversarialClippedKernel_eq_map]
  exact Measure.compProd_map (by unfold clipUnitReward; fun_prop)

/-- Integrate the pointwise next-pair transport over any prefix law. -/
theorem adversarialClipped_prefixStepLaw {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) (n : Nat)
    (P : Measure (History.FinitePairHistory (Fin K) Real n)) [IsProbabilityMeasure P] :
    P.map (adversarialClipHistory n) ⊗ₘ
      Thompson.historyStepKernel algorithm
        (stationaryBanditHistoryEnvironment (adversarialClippedKernel sigma shift)) n =
    (P ⊗ₘ Thompson.historyStepKernel (adversarialClipHistoryAlgorithm algorithm)
      (stationaryBanditHistoryEnvironment (adversarialUnclippedKernel sigma shift)) n).map
        (Prod.map (adversarialClipHistory n) (Prod.map id clipUnitReward)) := by
  let C := adversarialClipHistory (K := K) n
  let D := Prod.map (id : Fin K -> Fin K) clipUnitReward
  let A := Thompson.historyStepKernel algorithm
    (stationaryBanditHistoryEnvironment (adversarialClippedKernel sigma shift)) n
  let B := Thompson.historyStepKernel (adversarialClipHistoryAlgorithm algorithm)
    (stationaryBanditHistoryEnvironment (adversarialUnclippedKernel sigma shift)) n
  have hC : Measurable C := measurable_adversarialClipHistory n
  have hD : Measurable D := by unfold D clipUnitReward; fun_prop
  haveI : IsProbabilityMeasure (P.map C) := Measure.isProbabilityMeasure_map hC.aemeasurable
  change P.map C ⊗ₘ A = (P ⊗ₘ B).map (Prod.map C D)
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (hC.prodMap hD) hs,
    Measure.compProd_apply (hs.preimage (hC.prodMap hD)),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hC]
  apply lintegral_congr
  intro h
  have hstep : A (C h) = (B h).map D :=
    adversarialClipped_historyStepLaw algorithm sigma shift n h
  rw [hstep, Measure.map_apply hD (hs.preimage measurable_prodMk_left)]
  rfl

/-- Exact transport of the entire finite observed history under the same
original policy and its clipped-history lift. -/
theorem adversarialClippedHistoryLaw_eq_map {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) (n : Nat) :
    adversarialClippedHistoryLaw algorithm sigma shift n =
      (canonicalBanditHistoryMeasure (adversarialClipHistoryAlgorithm algorithm)
        (adversarialUnclippedKernel sigma shift) n).map (adversarialClipHistory n) := by
  induction n with
  | zero => exact adversarialClippedHistoryLaw_zero algorithm sigma shift
  | succ n ih =>
    change canonicalBanditHistoryMeasure algorithm
      (adversarialClippedKernel sigma shift) (n + 1) = _
    rw [canonicalBanditHistoryMeasure_succ, canonicalBanditHistoryMeasure_succ]
    change (adversarialClippedHistoryLaw algorithm sigma shift n ⊗ₘ _).map _ = _
    rw [ih, adversarialClipped_prefixStepLaw]
    have hm : Measurable
        (Prod.map (adversarialClipHistory (K := K) n)
          (Prod.map (id : Fin K -> Fin K) clipUnitReward)) := by
      apply (measurable_adversarialClipHistory n).prodMap
      unfold clipUnitReward
      fun_prop
    rw [Measure.map_map (pairHistorySuccMeasurableEquiv (Fin K) Real n).measurable hm,
      Measure.map_map (measurable_adversarialClipHistory (n + 1))
        (pairHistorySuccMeasurableEquiv (Fin K) Real n).measurable]
    congr 1
    funext input t
    simp only [Function.comp_apply,
      pairHistorySuccMeasurableEquiv_apply, adversarialClipHistory]
    unfold History.extendPairHistorySucc
    split <;> rfl

/-- Pull-count events are preserved by the full history transport. -/
theorem adversarialClippedHistoryLaw_pullSmall {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) (n : Nat) (arm : Fin K)
    (threshold : Real) :
    (adversarialClippedHistoryLaw algorithm sigma shift n)
      {h | finiteHistoryPullCountReal n h arm < threshold} =
    (canonicalBanditHistoryMeasure (adversarialClipHistoryAlgorithm algorithm)
      (adversarialUnclippedKernel sigma shift) n)
      {h | finiteHistoryPullCountReal n h arm < threshold} := by
  rw [adversarialClippedHistoryLaw_eq_map, Measure.map_apply
    (measurable_adversarialClipHistory n)
    (measurableSet_lt (measurable_finiteHistoryPullCountReal n arm) measurable_const)]
  congr 1
  ext h
  simp only [Set.mem_preimage, Set.mem_setOf_eq, adversarialClipHistory_pullCountReal]

/-- Identify the unbounded observation marginal as the exact shifted Gaussian. -/
theorem adversarialUnclippedKernel_apply {K : Nat}
    (sigma : Real) (shift : Fin K -> Real) (arm : Fin K) :
    adversarialUnclippedKernel sigma shift arm =
      gaussianReal (1 / 2 + shift arm) ⟨sigma ^ 2, sq_nonneg sigma⟩ := by
  change (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩).map
    (fun x => 1 / 2 + x + shift arm) = _
  have hf : (fun x : Real => 1 / 2 + x + shift arm) =
      (fun x => x + (1 / 2 + shift arm)) := by funext x; ring
  rw [hf, gaussianReal_map_add_const]
  simp

/-- Equal nonzero variance Gaussian KL, obtained by scaling the unit
variance theorem through a measurable equivalence. Mathlib candidate. -/
theorem klDiv_gaussianReal_common_scale (sigma mu nu : Real) (hs : sigma ≠ 0) :
    InformationTheory.klDiv
      (gaussianReal mu ⟨sigma ^ 2, sq_nonneg sigma⟩)
      (gaussianReal nu ⟨sigma ^ 2, sq_nonneg sigma⟩) =
      ENNReal.ofReal ((mu - nu) ^ 2 / (2 * sigma ^ 2)) := by
  let e : Real ≃ᵐ Real := (Homeomorph.mulLeft₀ sigma hs).toMeasurableEquiv
  have hm (a : Real) : (unitGaussianArm (a / sigma)).map e =
      gaussianReal a ⟨sigma ^ 2, sq_nonneg sigma⟩ := by
    change (gaussianReal (a / sigma) 1).map (fun x => sigma * x) = _
    rw [gaussianReal_map_const_mul]
    have ha : sigma * (a / sigma) = a := by field_simp
    simp [ha]
  rw [← hm mu, ← hm nu, klDiv_map_measurableEquiv, klDiv_gaussianReal_one]
  congr 1
  field_simp

/-- Directed per-arm information for the unbounded hard-family observations. -/
theorem klDiv_adversarialUnclippedKernel {K : Nat}
    (sigma : Real) (hs : sigma ≠ 0) (shift referenceShift : Fin K -> Real)
    (arm : Fin K) :
    InformationTheory.klDiv (adversarialUnclippedKernel sigma shift arm)
      (adversarialUnclippedKernel sigma referenceShift arm) =
      ENNReal.ofReal ((shift arm - referenceShift arm) ^ 2 / (2 * sigma ^ 2)) := by
  rw [adversarialUnclippedKernel_apply, adversarialUnclippedKernel_apply,
    klDiv_gaussianReal_common_scale sigma _ _ hs]
  congr 1
  ring

/-- Exact first-law pull-count information identity for Claim 17.6's
unclipped hard family. The same lifted policy is used on both sides. -/
theorem klDiv_adversarialUnclipped_base_changed_history
    {m : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (hs : sigma ≠ 0) (i : Fin m) (n : Nat) :
    InformationTheory.klDiv
      (canonicalBanditHistoryMeasure (adversarialClipHistoryAlgorithm algorithm)
        (adversarialUnclippedKernel sigma (gaussianMinimaxBaseMean gap)) n)
      (canonicalBanditHistoryMeasure (adversarialClipHistoryAlgorithm algorithm)
        (adversarialUnclippedKernel sigma (adversarialHardShift gap i)) n) =
    canonicalRealizedExpectedPullCountThrough (adversarialClipHistoryAlgorithm algorithm)
      (adversarialUnclippedKernel sigma (gaussianMinimaxBaseMean gap)) n i.succ *
      ENNReal.ofReal (2 * gap ^ 2 / sigma ^ 2) := by
  have harm (arm : Fin (m + 1)) :
      InformationTheory.klDiv
        (adversarialUnclippedKernel sigma (gaussianMinimaxBaseMean gap) arm)
        (adversarialUnclippedKernel sigma (adversarialHardShift gap i) arm) =
        if arm = i.succ then ENNReal.ofReal (2 * gap ^ 2 / sigma ^ 2) else 0 := by
    rw [klDiv_adversarialUnclippedKernel sigma hs]
    by_cases hi : arm = i.succ
    · subst arm
      simp only [adversarialHardShift, gaussianMinimaxBaseMean,
        Fin.succ_ne_zero, if_false, ite_true, eq_self]
      congr 1
      ring
    · rw [if_neg hi]
      by_cases h0 : arm = 0
      · simp [adversarialHardShift, gaussianMinimaxBaseMean, h0]
      · simp [adversarialHardShift, gaussianMinimaxBaseMean, h0, hi]
  rw [banditHistoryRelativeEntropy_eq_expectedPulls_sum]
  simp_rw [harm, mul_ite, mul_zero]
  simp

/-- The exact source tuning from Claim 17.6, with
`alternatives = k - 1`. -/
noncomputable def adversarialClaim17_6Gap
    (horizon alternatives : Nat) (sigma delta : Real) : Real :=
  sigma * Real.sqrt
    (((alternatives : Real) / (2 * (horizon : Real))) *
      Real.log (1 / (8 * delta)))

/-- Include the base instance as arm zero, as required by Claim 17.6. -/
def adversarialFullHardShift {m : Nat} (gap : Real)
    (distinguished arm : Fin (m + 1)) : Real :=
  if arm = 0 then gap else if arm = distinguished then 2 * gap else 0

theorem adversarialFullHardShift_zero {m : Nat} (gap : Real) :
    adversarialFullHardShift (m := m) gap 0 = gaussianMinimaxBaseMean gap := by
  funext arm
  by_cases h : arm = 0 <;> simp [adversarialFullHardShift, gaussianMinimaxBaseMean, h]

theorem adversarialFullHardShift_succ {m : Nat} (gap : Real) (i : Fin m) :
    adversarialFullHardShift gap i.succ = adversarialHardShift gap i := rfl

/-- Source gap tuning cancels the least-arm information bound exactly. -/
theorem adversarialClaim17_6Gap_information_calibration
    {horizon m : Nat} (hn : 0 < horizon) (hm : 0 < m)
    (sigma delta : Real) (hs : sigma ≠ 0) (hd : 0 < delta) (hd8 : delta < 1 / 8) :
    ((horizon : Real) / m) *
      (2 * (adversarialClaim17_6Gap horizon m sigma delta) ^ 2 / sigma ^ 2) =
      Real.log (1 / (8 * delta)) := by
  have hl : 0 <= Real.log (1 / (8 * delta)) := by
    apply Real.log_nonneg
    rw [one_le_div (by positivity)]
    linarith
  have hrad : 0 <= ((m : Real) / (2 * horizon)) * Real.log (1 / (8 * delta)) :=
    mul_nonneg (by positivity) hl
  unfold adversarialClaim17_6Gap
  rw [mul_pow, Real.sq_sqrt hrad]
  field_simp [hs, Nat.cast_ne_zero.mpr (ne_of_gt hn), Nat.cast_ne_zero.mpr (ne_of_gt hm)]

/-- Conservation of expected pulls for the lifted policy's unbounded law. -/
theorem sum_adversarialUnclipped_expectedPulls {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (sigma : Real) (shift : Fin K -> Real) (n : Nat) :
    (∑ arm : Fin K, canonicalRealizedExpectedPullCountThrough
      (adversarialClipHistoryAlgorithm algorithm)
      (adversarialUnclippedKernel sigma shift) n arm) = n + 1 := by
  classical
  unfold canonicalRealizedExpectedPullCountThrough
  rw [← MeasureTheory.lintegral_finset_sum]
  · simp_rw [sum_finiteHistoryPullCountENNReal]
    simp
  · intro arm _
    exact measurable_finiteHistoryPullCountENNReal n arm

/-- Corrected Claim 17.6: the source strict inequality must be non-strict.
The witness ranges over the base instance as well as all changed instances. -/
theorem adversarialClippedHistory_pull_le_half_claim17_6
    {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (n : Nat) (sigma delta : Real) (hs : sigma ≠ 0)
    (hd : 0 < delta) (hd8 : delta < 1 / 8) :
    ∃ arm : Fin (m + 1), 2 * delta <=
      (adversarialClippedHistoryLaw algorithm sigma
        (adversarialFullHardShift (adversarialClaim17_6Gap (n + 1) m sigma delta) arm) n).real
        {h | finiteHistoryPullCountReal n h arm <= ((n + 1 : Nat) : Real) / 2} := by
  classical
  let gap := adversarialClaim17_6Gap (n + 1) m sigma delta
  let lifted := adversarialClipHistoryAlgorithm algorithm
  let base := adversarialUnclippedKernel sigma (gaussianMinimaxBaseMean (m := m) gap)
  let P := canonicalBanditHistoryMeasure lifted base n
  let A : Set (History.FinitePairHistory (Fin (m + 1)) Real n) :=
    {h | finiteHistoryPullCountReal n h (0 : Fin (m + 1)) <=
    ((n + 1 : Nat) : Real) / 2}
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_finiteHistoryPullCountReal n 0) measurable_const
  have transport (shift : Fin (m + 1) -> Real) (arm : Fin (m + 1)) :
      (adversarialClippedHistoryLaw algorithm sigma shift n).real
        {h | finiteHistoryPullCountReal n h arm <= ((n + 1 : Nat) : Real) / 2} =
      (canonicalBanditHistoryMeasure lifted (adversarialUnclippedKernel sigma shift) n).real
        {h | finiteHistoryPullCountReal n h arm <= ((n + 1 : Nat) : Real) / 2} := by
    unfold Measure.real
    rw [adversarialClippedHistoryLaw_eq_map, Measure.map_apply
      (measurable_adversarialClipHistory n)
      (measurableSet_le (measurable_finiteHistoryPullCountReal n arm) measurable_const)]
    congr 2
    ext h
    simp only [Set.mem_preimage, Set.mem_setOf_eq, adversarialClipHistory_pullCountReal]
  by_cases hb : 2 * delta <= P.real A
  · refine ⟨0, ?_⟩
    rw [adversarialFullHardShift_zero, transport]
    exact hb
  have hb' : P.real A < 2 * delta := lt_of_not_ge hb
  let count := fun arm => canonicalRealizedExpectedPullCountThrough lifted base n arm
  have hc (arm) : count arm ≠ ∞ :=
    canonicalRealizedExpectedPullCountThrough_ne_top lifted base n arm
  have htotal : (∑ arm, (count arm).toReal) = ((n + 1 : Nat) : Real) := by
    rw [← ENNReal.toReal_sum (fun arm _ => hc arm)]
    change (∑ arm, canonicalRealizedExpectedPullCountThrough lifted base n arm).toReal = _
    rw [sum_canonicalRealizedExpectedPullCountThrough_general]
    simp [ENNReal.toReal_add]
  obtain ⟨i, hi⟩ := exists_leastExploredAlternative hm
    (fun arm => (count arm).toReal) (n + 1) (fun _ => ENNReal.toReal_nonneg) htotal
  let Q := canonicalBanditHistoryMeasure lifted
    (adversarialUnclippedKernel sigma (adversarialHardShift gap i)) n
  have hl : 0 <= Real.log (1 / (8 * delta)) := by
    apply Real.log_nonneg
    rw [one_le_div (by positivity)]
    linarith
  have hexponent : (count i.succ).toReal * (2 * gap ^ 2 / sigma ^ 2) <=
      Real.log (1 / (8 * delta)) := by
    calc
      _ <= (((n + 1 : Nat) : Real) / m) * (2 * gap ^ 2 / sigma ^ 2) :=
        mul_le_mul_of_nonneg_right hi (by positivity)
      _ = _ := adversarialClaim17_6Gap_information_calibration
        (Nat.succ_pos n) hm sigma delta hs hd hd8
  have hKL : InformationTheory.klDiv P Q <= ENNReal.ofReal (Real.log (1 / (8 * delta))) := by
    rw [klDiv_adversarialUnclipped_base_changed_history algorithm sigma gap hs i n]
    change count i.succ * ENNReal.ofReal (2 * gap ^ 2 / sigma ^ 2) <= _
    rw [← ENNReal.ofReal_toReal (hc i.succ), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hexponent
  have htest := (bretagnolleHuberScale_antitone hKL).trans (bretagnolleHuber (P := P) (Q := Q) hA)
  have hexp : Real.exp (-Real.log (1 / (8 * delta))) = 8 * delta := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hscale : bretagnolleHuberScale (ENNReal.ofReal (Real.log (1 / (8 * delta)))) =
      4 * delta := by
    unfold bretagnolleHuberScale
    rw [if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hl, hexp]
    ring
  rw [hscale] at htest
  have hsub : Aᶜ ⊆ {h | finiteHistoryPullCountReal n h i.succ <= ((n + 1 : Nat) : Real) / 2} := by
    intro h hh
    have hh' : ((n + 1 : Nat) : Real) / 2 < finiteHistoryPullCountReal n h 0 :=
      lt_of_not_ge hh
    have ht := sum_finiteHistoryPullCountReal n h
    rw [Fin.sum_univ_succ] at ht
    have hi' := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin m => finiteHistoryPullCountReal n h j.succ)
      (fun j _ => finiteHistoryPullCountReal_nonneg n h j.succ) (Finset.mem_univ i)
    change finiteHistoryPullCountReal n h i.succ <= _
    push_cast at ht hh' ⊢
    linarith
  refine ⟨i.succ, ?_⟩
  rw [adversarialFullHardShift_succ, transport]
  have hmono : Q.real Aᶜ <= Q.real
      {h | finiteHistoryPullCountReal n h i.succ <= ((n + 1 : Nat) : Real) / 2} :=
    measureReal_mono hsub (by finiteness)
  change 2 * delta <= Q.real _
  linarith

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

/-- The Bernoulli indicator of a clipped round in the construction for
Theorem 17.4. -/
def adversarialClipIndicator (gap x : Real) : Real :=
  if 1 / 2 - 2 * gap <= |x| then 1 else 0

theorem measurable_adversarialClipIndicator (gap : Real) :
    Measurable (adversarialClipIndicator gap) := by
  unfold adversarialClipIndicator
  exact Measurable.ite (measurableSet_le measurable_const measurable_abs)
    measurable_const measurable_const

theorem adversarialClipIndicator_mem_Icc (gap x : Real) :
    adversarialClipIndicator gap x ∈ Set.Icc 0 1 := by
  unfold adversarialClipIndicator
  split <;> simp

/-- The one-dimensional Gaussian tail estimate used in Claim 17.7.  It is
proved from Mathlib's sub-Gaussian Chernoff bound; the final numerical step is
the degree-five lower Taylor bound for `exp (25/8)`. -/
theorem gaussianReal_tenth_abs_quarter_le_eighth :
    (gaussianReal 0 ⟨(1 / 10 : Real) ^ 2, sq_nonneg _⟩).real
        {x : Real | (1 / 4 : Real) <= |x|} <= 1 / 8 := by
  let variance : NNReal := ⟨(1 / 10 : Real) ^ 2, sq_nonneg _⟩
  let G : Measure Real := gaussianReal 0 variance
  have hsg : HasSubgaussianMGF id variance G := by
    constructor
    · intro t
      simpa [G, id] using
        (integrable_exp_mul_gaussianReal (μ := 0) (v := variance) t)
    · intro t
      dsimp [G]
      rw [mgf_id_gaussianReal]
      norm_num
  have hpos := hsg.measure_ge_le
    (ε := (1 / 4 : Real)) (by norm_num)
  have hneg := hsg.neg.measure_ge_le
    (ε := (1 / 4 : Real)) (by norm_num)
  have hsplit : {x : Real | (1 / 4 : Real) <= |x|} =
      {x : Real | (1 / 4 : Real) <= x} ∪
        {x : Real | (1 / 4 : Real) <= -x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [le_abs]
  change G.real {x : Real | (1 / 4 : Real) <= |x|} <= 1 / 8
  rw [hsplit]
  calc
    G.real ({x : Real | (1 / 4 : Real) <= x} ∪
        {x : Real | (1 / 4 : Real) <= -x}) <=
      G.real {x : Real | (1 / 4 : Real) <= x} +
        G.real {x : Real | (1 / 4 : Real) <= -x} := measureReal_union_le _ _
    _ <= Real.exp (-(25 / 8 : Real)) +
        Real.exp (-(25 / 8 : Real)) := by
      apply add_le_add
      · norm_num [variance, G, id, div_eq_mul_inv] at hpos ⊢
        exact hpos
      · norm_num [variance, G, id, div_eq_mul_inv] at hneg ⊢
        exact hneg
    _ = 2 * Real.exp (-(25 / 8 : Real)) := by ring
    _ <= 1 / 8 := by
      have hseries := Real.sum_le_exp_of_nonneg
        (show (0 : Real) <= 25 / 8 by norm_num) 5
      norm_num [Finset.sum_range_succ] at hseries ⊢
      have hmul := mul_le_mul_of_nonneg_right hseries
        (Real.exp_pos (-(25 / 8 : Real))).le
      rw [← Real.exp_add] at hmul
      norm_num at hmul
      nlinarith [Real.exp_pos (-(25 / 8 : Real))]

/-- Each coordinate under the IID product law has the stated Gaussian
marginal, specialized to the clipping indicator needed for Claim 17.7. -/
theorem integral_adversarialClipIndicator_eq
    {horizon : Nat} (gap : Real) (t : Fin horizon) :
    ∫ eta, adversarialClipIndicator gap (eta t)
        ∂(adversarialCenteredNoiseLaw horizon (1 / 10)) =
      (gaussianReal 0 ⟨(1 / 10 : Real) ^ 2, sq_nonneg _⟩).real
        {x : Real | 1 / 2 - 2 * gap <= |x|} := by
  let A : Set Real := {x : Real | 1 / 2 - 2 * gap <= |x|}
  have hA : MeasurableSet A := measurableSet_le measurable_const measurable_abs
  have hmInd : Measurable (A.indicator (fun _ : Real => (1 : Real))) :=
    measurable_const.indicator hA
  have hfun : adversarialClipIndicator gap = A.indicator 1 := by
    funext x
    simp only [adversarialClipIndicator, Set.indicator, Pi.one_apply]
    split <;> simp_all [A]
  rw [hfun]
  unfold adversarialCenteredNoiseLaw
  let mp := MeasureTheory.measurePreserving_eval
    (fun _ : Fin horizon => gaussianReal 0
      ⟨(1 / 10 : Real) ^ 2, sq_nonneg _⟩) t
  have hi := MeasureTheory.integral_map (μ := Measure.pi fun _ : Fin horizon =>
      gaussianReal 0 ⟨(1 / 10 : Real) ^ 2, sq_nonneg _⟩)
    (f := A.indicator 1) (measurable_pi_apply t).aemeasurable
    hmInd.aestronglyMeasurable
  calc
    _ = ∫ x, A.indicator 1 x ∂(gaussianReal 0
        ⟨(1 / 10 : Real) ^ 2, sq_nonneg _⟩) := by
      simpa only [mp.map_eq] using hi.symm
    _ = _ := integral_indicator_one hA

/-- **Claim 17.7.**  Under the source variance `sigma = 1/10`, if
`gap < 1/8` and `n >= 32 log(1/delta)`, at most a `delta` fraction of noise
paths have at least `n/4` clipped rounds. -/
theorem adversarialClippingCount_tail_claim17_7
    {horizon : Nat} (hhorizon : 0 < horizon)
    (delta gap : Real) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hgap_lt : gap < 1 / 8)
    (horizon_condition : 32 * Real.log (1 / delta) <= horizon) :
    (adversarialCenteredNoiseLaw horizon (1 / 10)).real
      {eta | (horizon : Real) / 4 <=
        adversarialClippingCountReal eta gap} <= delta := by
  let P : Measure (Fin horizon -> Real) :=
    adversarialCenteredNoiseLaw horizon (1 / 10)
  let raw : Fin horizon -> (Fin horizon -> Real) -> Real :=
    fun t eta => adversarialClipIndicator gap (eta t)
  let X : Fin horizon -> (Fin horizon -> Real) -> Real :=
    fun t eta => raw t eta - ∫ zeta, raw t zeta ∂P
  haveI : IsProbabilityMeasure P := by
    dsimp [P, adversarialCenteredNoiseLaw]
    infer_instance
  have hraw_meas (t : Fin horizon) : Measurable (raw t) := by
    exact (measurable_adversarialClipIndicator gap).comp
      (measurable_pi_apply t)
  have hIndep : iIndepFun X P := by
    have hbase : iIndepFun
        (fun t (eta : Fin horizon -> Real) => id (eta t)) P := by
      unfold P adversarialCenteredNoiseLaw
      exact iIndepFun_pi (fun _ => aemeasurable_id)
    have hc := hbase.comp
      (fun t x => adversarialClipIndicator gap x -
        ∫ zeta, raw t zeta ∂P)
      (fun _ => (measurable_adversarialClipIndicator gap).sub
        measurable_const)
    simpa only [X, raw, Function.comp_apply, id_eq] using hc
  have hSubG (t : Fin horizon) :
      HasSubgaussianMGF (X t) (1 / 4 : NNReal) P := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := raw t)
      (hraw_meas t).aemeasurable
      (ae_of_all P fun eta => adversarialClipIndicator_mem_Icc gap (eta t))
    norm_num at h ⊢
    simpa only [X] using h
  have hmean (t : Fin horizon) : ∫ eta, raw t eta ∂P <= 1 / 8 := by
    rw [show (∫ eta, raw t eta ∂P) =
        ∫ eta, adversarialClipIndicator gap (eta t)
          ∂(adversarialCenteredNoiseLaw horizon (1 / 10)) by rfl]
    rw [integral_adversarialClipIndicator_eq gap t]
    calc
      _ <= (gaussianReal 0 ⟨(1 / 10 : Real) ^ 2, sq_nonneg _⟩).real
          {x : Real | (1 / 4 : Real) <= |x|} := by
        apply measureReal_mono (h₂ := by finiteness)
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        linarith
      _ <= 1 / 8 := gaussianReal_tenth_abs_quarter_le_eighth
  have hmean_sum : ∑ t : Fin horizon, ∫ eta, raw t eta ∂P <=
      (horizon : Real) / 8 := by
    calc
      _ <= ∑ _t : Fin horizon, (1 / 8 : Real) :=
        Finset.sum_le_sum fun t _ => hmean t
      _ = (horizon : Real) / 8 := by simp; ring
  have hHoeffding : P.real {eta | (horizon : Real) / 8 <= ∑ t, X t eta} <=
      Real.exp (-(horizon : Real) / 32) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndep
      (s := (Finset.univ : Finset (Fin horizon)))
      (c := fun _ => (1 / 4 : NNReal))
      (fun t _ => hSubG t)
      (show 0 <= (horizon : Real) / 8 by positivity)
    have hcsum : ((↑(∑ _t : Fin horizon, (1 / 4 : NNReal)) : NNReal) : Real) =
        (horizon : Real) / 4 := by simp; ring
    rw [hcsum] at h
    calc
      _ <= Real.exp (-((horizon : Real) / 8) ^ 2 /
          (2 * ((horizon : Real) / 4))) := h
      _ = Real.exp (-(horizon : Real) / 32) := by
        congr 1
        field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hhorizon)]
        ring
  have hEvent :
      {eta | (horizon : Real) / 4 <= adversarialClippingCountReal eta gap} ⊆
        {eta | (horizon : Real) / 8 <= ∑ t, X t eta} := by
    intro eta heta
    change (horizon : Real) / 4 <=
      adversarialClippingCountReal eta gap at heta
    change (horizon : Real) / 8 <= ∑ t, X t eta
    have hraw_count : (∑ t, raw t eta) =
        adversarialClippingCountReal eta gap := by
      rfl
    have hcenter : (∑ t, X t eta) =
        (∑ t, raw t eta) - ∑ t, ∫ zeta, raw t zeta ∂P := by
      simp only [X, Finset.sum_sub_distrib]
    rw [hcenter, hraw_count]
    linarith
  have hlog_nonneg : 0 <= Real.log (1 / delta) := by
    apply Real.log_nonneg
    rw [one_le_div hdelta]
    exact hdelta1.le
  change P.real _ <= delta
  calc
    P.real _ <= P.real {eta | (horizon : Real) / 8 <= ∑ t, X t eta} :=
      measureReal_mono hEvent (by finiteness)
    _ <= Real.exp (-(horizon : Real) / 32) := hHoeffding
    _ <= delta := by
      have hlog : Real.log (1 / delta) <= (horizon : Real) / 32 := by
        nlinarith
      calc
        _ <= Real.exp (-Real.log (1 / delta)) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = delta := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp

/-- The textbook clipping count: a round is counted when at least one arm
has reward at a boundary of the unit interval. -/
noncomputable def adversarialBoundaryClippingCountReal
    {horizon alternatives : Nat} (eta : Fin horizon -> Real) (gap : Real)
    (distinguished : Fin alternatives) : Real :=
  ∑ t, if ∃ arm : Fin (alternatives + 1),
    adversarialClippedGaussianReward eta gap distinguished t arm = 0 ∨
      adversarialClippedGaussianReward eta gap distinguished t arm = 1
    then 1 else 0

theorem adversarialBoundaryClippingCountReal_le
    {horizon alternatives : Nat} (eta : Fin horizon -> Real) (gap : Real)
    (hgap : 0 <= gap) (distinguished : Fin alternatives) :
    adversarialBoundaryClippingCountReal eta gap distinguished <=
      adversarialClippingCountReal eta gap := by
  classical
  apply Finset.sum_le_sum
  intro t _
  by_cases hc : 1 / 2 - 2 * gap <= |eta t|
  · simp only [if_pos hc]
    split <;> norm_num
  · have habs := abs_lt.mp (lt_of_not_ge hc)
    have hno : ¬ ∃ arm : Fin (alternatives + 1),
        adversarialClippedGaussianReward eta gap distinguished t arm = 0 ∨
          adversarialClippedGaussianReward eta gap distinguished t arm = 1 := by
      rintro ⟨arm, ha⟩
      have hs0 := adversarialHardShift_nonneg gap hgap distinguished arm
      have hs2 := adversarialHardShift_le_two_mul gap hgap distinguished arm
      have hlo : 0 < 1 / 2 + eta t + adversarialHardShift gap distinguished arm := by
        linarith
      have hhi : 1 / 2 + eta t + adversarialHardShift gap distinguished arm < 1 := by
        linarith
      have heq : adversarialClippedGaussianReward eta gap distinguished t arm =
          1 / 2 + eta t + adversarialHardShift gap distinguished arm :=
        clipUnitReward_eq_self hlo.le hhi.le
      rw [heq] at ha
      rcases ha with ha | ha <;> linarith
    simp only [if_neg hc, if_neg hno, le_refl]

/-- Claim 17.7 for the literal boundary event in the textbook. -/
theorem adversarialBoundaryClippingCount_tail_claim17_7
    {horizon alternatives : Nat} (hhorizon : 0 < horizon)
    (delta gap : Real) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hgap : 0 <= gap) (hgap_lt : gap < 1 / 8)
    (distinguished : Fin alternatives)
    (horizon_condition : 32 * Real.log (1 / delta) <= horizon) :
    (adversarialCenteredNoiseLaw horizon (1 / 10)).real
      {eta | (horizon : Real) / 4 <=
        adversarialBoundaryClippingCountReal eta gap distinguished} <= delta := by
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw horizon (1 / 10)) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  refine (measureReal_mono (s₂ := {eta | (horizon : Real) / 4 <=
      adversarialClippingCountReal eta gap}) ?_).trans
    (adversarialClippingCount_tail_claim17_7 hhorizon delta gap hdelta hdelta1
      hgap_lt horizon_condition)
  intro eta heta
  exact heta.trans (adversarialBoundaryClippingCountReal_le eta gap hgap distinguished)

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

private theorem clipUnitReward_eq_self_of_ne_endpoints (x : Real)
    (h0 : clipUnitReward x ≠ 0) (h1 : clipUnitReward x ≠ 1) :
    clipUnitReward x = x := by
  have hx0 : 0 <= x := by
    by_contra h
    have hx : x <= 0 := le_of_lt (lt_of_not_ge h)
    have he : clipUnitReward x = 0 := by
      unfold clipUnitReward
      rw [min_eq_right (show x <= 1 by linarith), max_eq_left hx]
    exact h0 he
  have hx1 : x <= 1 := by
    by_contra h
    have hx : 1 <= x := le_of_lt (lt_of_not_ge h)
    have he : clipUnitReward x = 1 := by simp [clipUnitReward, min_eq_left hx]
    exact h1 he
  exact clipUnitReward_eq_self hx0 hx1

/-- Exact Eq. (17.8), with the textbook's actual boundary count. -/
theorem adversarialRandomRegret_ge_boundary_eq17_8
    {horizon alternatives : Nat} (eta : Fin horizon -> Real) (gap : Real)
    (hgap : 0 <= gap) (distinguished : Fin alternatives)
    (actions : Fin horizon -> Fin (alternatives + 1)) :
    gap * ((horizon : Real) - adversarialPullCountReal actions distinguished -
      adversarialBoundaryClippingCountReal eta gap distinguished) <=
      adversarialRandomRegret
        (adversarialClippedGaussianReward eta gap distinguished) actions := by
  classical
  let bad := fun t => ∃ arm : Fin (alternatives + 1),
    adversarialClippedGaussianReward eta gap distinguished t arm = 0 ∨
      adversarialClippedGaussianReward eta gap distinguished t arm = 1
  have hterm (t : Fin horizon) :
      gap * (1 - (if actions t = distinguished.succ then 1 else 0) -
        (if bad t then 1 else 0)) <=
        adversarialClippedGaussianReward eta gap distinguished t distinguished.succ -
          adversarialClippedGaussianReward eta gap distinguished t (actions t) := by
    by_cases hp : actions t = distinguished.succ
    · rw [hp, if_pos rfl]
      split <;> simp_all
    · by_cases hb : bad t
      · rw [if_neg hp, if_pos hb]
        norm_num
        exact adversarialClippedGaussianReward_distinguished_mono
          eta gap hgap distinguished t (actions t)
      · have heq (arm : Fin (alternatives + 1)) :
            adversarialClippedGaussianReward eta gap distinguished t arm =
              1 / 2 + eta t + adversarialHardShift gap distinguished arm := by
          apply clipUnitReward_eq_self_of_ne_endpoints
          · intro h
            exact hb ⟨arm, Or.inl h⟩
          · intro h
            exact hb ⟨arm, Or.inr h⟩
        rw [if_neg hp, if_neg hb, heq, heq, adversarialHardShift_distinguished]
        have hs := adversarialHardShift_le_gap_of_ne gap hgap distinguished (actions t) hp
        linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hterm t)
  have hleft : (∑ t : Fin horizon,
      gap * (1 - (if actions t = distinguished.succ then 1 else 0) -
        (if bad t then 1 else 0))) =
      gap * ((horizon : Real) - adversarialPullCountReal actions distinguished -
        adversarialBoundaryClippingCountReal eta gap distinguished) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp [adversarialPullCountReal, adversarialBoundaryClippingCountReal, bad]
  rw [hleft] at hsum
  exact hsum.trans (adversarialComparatorRegret_le_randomRegret
    (adversarialClippedGaussianReward eta gap distinguished) actions distinguished.succ)

/-- The shared-noise matrix for every witness, including the base arm. -/
def adversarialFullClippedReward {horizon m : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (i : Fin (m + 1))
    (t : Fin horizon) (arm : Fin (m + 1)) : Real :=
  clipUnitReward (1 / 2 + eta t + adversarialFullHardShift gap i arm)

theorem adversarialFullHardShift_bounds {m : Nat} (gap : Real) (hg : 0 <= gap)
    (i arm : Fin (m + 1)) :
    0 <= adversarialFullHardShift gap i arm ∧
      adversarialFullHardShift gap i arm <= 2 * gap := by
  unfold adversarialFullHardShift
  split <;> (try split) <;> constructor <;> linarith

theorem adversarialFullHardShift_separation {m : Nat} (gap : Real) (hg : 0 <= gap)
    (i arm : Fin (m + 1)) (hi : arm ≠ i) :
    gap <= adversarialFullHardShift gap i i - adversarialFullHardShift gap i arm := by
  by_cases h0 : i = 0
  · subst i
    simp [adversarialFullHardShift, hi]
  · by_cases ha : arm = 0
    · simp [adversarialFullHardShift, h0, ha]
      linarith
    · simp [adversarialFullHardShift, h0, ha, hi]
      linarith

theorem adversarialFullClippedReward_best {horizon m : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (hg : 0 <= gap)
    (i : Fin (m + 1)) (t : Fin horizon) (arm : Fin (m + 1)) :
    adversarialFullClippedReward eta gap i t arm <=
      adversarialFullClippedReward eta gap i t i := by
  by_cases hi : arm = i
  · subst arm; rfl
  · have hs := adversarialFullHardShift_separation gap hg i arm hi
    unfold adversarialFullClippedReward clipUnitReward
    exact max_le_max_left _ (min_le_min_left _ (by linarith))

noncomputable def adversarialFullBoundaryCount {horizon m : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (i : Fin (m + 1)) : Real :=
  ∑ t, if ∃ arm, adversarialFullClippedReward eta gap i t arm = 0 ∨
    adversarialFullClippedReward eta gap i t arm = 1 then 1 else 0

/-- Literal boundary-count Eq. (17.8), now also valid for the base witness. -/
theorem adversarialFullRandomRegret_ge_boundary_eq17_8 {horizon m : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (hg : 0 <= gap)
    (i : Fin (m + 1)) (actions : Fin horizon -> Fin (m + 1)) :
    gap * ((horizon : Real) - (∑ t, if actions t = i then 1 else 0) -
      adversarialFullBoundaryCount eta gap i) <=
      adversarialRandomRegret (adversarialFullClippedReward eta gap i) actions := by
  classical
  let bad := fun t => ∃ arm, adversarialFullClippedReward eta gap i t arm = 0 ∨
    adversarialFullClippedReward eta gap i t arm = 1
  have ht (t : Fin horizon) :
      gap * (1 - (if actions t = i then 1 else 0) - (if bad t then 1 else 0)) <=
      adversarialFullClippedReward eta gap i t i -
        adversarialFullClippedReward eta gap i t (actions t) := by
    by_cases hp : actions t = i
    · rw [hp, if_pos rfl]
      split <;> simp_all
    · by_cases hb : bad t
      · rw [if_neg hp, if_pos hb]
        norm_num
        exact adversarialFullClippedReward_best eta gap hg i t (actions t)
      · have he (arm) : adversarialFullClippedReward eta gap i t arm =
            1 / 2 + eta t + adversarialFullHardShift gap i arm := by
          apply clipUnitReward_eq_self_of_ne_endpoints
          · intro h; exact hb ⟨arm, Or.inl h⟩
          · intro h; exact hb ⟨arm, Or.inr h⟩
        rw [if_neg hp, if_neg hb, he, he]
        have hs := adversarialFullHardShift_separation gap hg i (actions t) hp
        linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  have he : (∑ t : Fin horizon,
      gap * (1 - (if actions t = i then 1 else 0) - (if bad t then 1 else 0))) =
      gap * ((horizon : Real) - (∑ t, if actions t = i then 1 else 0) -
        adversarialFullBoundaryCount eta gap i) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp [adversarialFullBoundaryCount, bad]
  rw [he] at hsum
  exact hsum.trans (adversarialComparatorRegret_le_randomRegret
    (adversarialFullClippedReward eta gap i) actions i)

theorem adversarialFullBoundaryCount_le {horizon m : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (hg : 0 <= gap) (i : Fin (m + 1)) :
    adversarialFullBoundaryCount eta gap i <= adversarialClippingCountReal eta gap := by
  classical
  apply Finset.sum_le_sum
  intro t _
  by_cases hc : 1 / 2 - 2 * gap <= |eta t|
  · simp only [if_pos hc]
    split <;> norm_num
  · have habs := abs_lt.mp (lt_of_not_ge hc)
    have hno : ¬ ∃ arm, adversarialFullClippedReward eta gap i t arm = 0 ∨
        adversarialFullClippedReward eta gap i t arm = 1 := by
      rintro ⟨arm, ha⟩
      obtain ⟨hs0, hs2⟩ := adversarialFullHardShift_bounds gap hg i arm
      have hlo : 0 < 1 / 2 + eta t + adversarialFullHardShift gap i arm := by linarith
      have hhi : 1 / 2 + eta t + adversarialFullHardShift gap i arm < 1 := by linarith
      have he : adversarialFullClippedReward eta gap i t arm =
          1 / 2 + eta t + adversarialFullHardShift gap i arm :=
        clipUnitReward_eq_self hlo.le hhi.le
      rw [he] at ha
      rcases ha with ha | ha <;> linarith
    simp only [if_neg hc, if_neg hno, le_refl]

/-- Claim 17.7 for every member of the corrected Claim 17.6 witness family. -/
theorem adversarialFullBoundaryCount_tail_claim17_7 {horizon m : Nat}
    (hn : 0 < horizon) (delta gap : Real) (hd : 0 < delta) (hd1 : delta < 1)
    (hg : 0 <= gap) (hg8 : gap < 1 / 8) (i : Fin (m + 1))
    (horizon_condition : 32 * Real.log (1 / delta) <= horizon) :
    (adversarialCenteredNoiseLaw horizon (1 / 10)).real
      {eta | (horizon : Real) / 4 <= adversarialFullBoundaryCount eta gap i} <= delta := by
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw horizon (1 / 10)) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  refine (measureReal_mono (s₂ := {eta | (horizon : Real) / 4 <=
    adversarialClippingCountReal eta gap}) ?_).trans
    (adversarialClippingCount_tail_claim17_7 hn delta gap hd hd1 hg8 horizon_condition)
  intro eta heta
  exact heta.trans (adversarialFullBoundaryCount_le eta gap hg i)

/-- A deterministic oblivious reward table. Only its finite prefix is used. -/
abbrev AdversarialRewardTable (K : Nat) := Nat -> Fin K -> Real

/-- Feedback from a fixed table, with the table retained as a kernel parameter. -/
noncomputable def adversarialTableInitialFeedback {K : Nat} :
    Kernel (AdversarialRewardTable K × Fin K) Real :=
  Kernel.deterministic (fun input => input.1 0 input.2) (by
    apply measurable_from_prod_countable_left
    intro arm
    exact (measurable_pi_apply arm).comp (measurable_pi_apply 0))

instance {K : Nat} : IsMarkovKernel (adversarialTableInitialFeedback (K := K)) := by
  unfold adversarialTableInitialFeedback
  infer_instance

noncomputable def adversarialTableNextFeedback {K : Nat} (n : Nat) :
    Kernel ((AdversarialRewardTable K × History.FinitePairHistory (Fin K) Real n) × Fin K) Real :=
  Kernel.deterministic (fun input => input.1.1 (n + 1) input.2) (by
    apply measurable_from_prod_countable_left
    intro arm
    exact (measurable_pi_apply arm).comp ((measurable_pi_apply (n + 1)).comp measurable_fst))

instance {K : Nat} (n : Nat) : IsMarkovKernel (adversarialTableNextFeedback (K := K) n) := by
  unfold adversarialTableNextFeedback
  infer_instance

/-- The original policy observes exactly its action/reward prefix. -/
noncomputable def adversarialTableStepKernel {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat) :
    Kernel (AdversarialRewardTable K × History.FinitePairHistory (Fin K) Real n) (Fin K × Real) :=
  (algorithm.policy n).prodMkLeft (AdversarialRewardTable K) ⊗ₖ
    adversarialTableNextFeedback n

instance {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat) :
    IsMarkovKernel (adversarialTableStepKernel algorithm n) := by
  unfold adversarialTableStepKernel
  infer_instance

/-- Conditional history distribution under each fixed oblivious table.
This is a measurable kernel, so averaging over random tables is well-defined. -/
noncomputable def adversarialTableHistoryKernel {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) :
    (n : Nat) -> Kernel (AdversarialRewardTable K) (History.FinitePairHistory (Fin K) Real n)
  | 0 => ((Kernel.const (AdversarialRewardTable K) algorithm.initialAction) ⊗ₖ
      adversarialTableInitialFeedback).map (pairHistoryZeroMeasurableEquiv (Fin K) Real)
  | n + 1 => ((adversarialTableHistoryKernel algorithm n) ⊗ₖ
      adversarialTableStepKernel algorithm n).map (pairHistorySuccMeasurableEquiv (Fin K) Real n)

instance adversarialTableHistoryKernel_isMarkov {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat) :
    IsMarkovKernel (adversarialTableHistoryKernel algorithm n) := by
  induction n with
  | zero =>
    unfold adversarialTableHistoryKernel
    exact Kernel.IsMarkovKernel.map _ (pairHistoryZeroMeasurableEquiv (Fin K) Real).measurable
  | succ n ih =>
    letI := ih
    unfold adversarialTableHistoryKernel
    exact Kernel.IsMarkovKernel.map _ (pairHistorySuccMeasurableEquiv (Fin K) Real n).measurable

/-- Fixing the table gives exactly the original policy and deterministic feedback. -/
theorem adversarialTableStepKernel_apply {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat)
    (table : AdversarialRewardTable K) (history : History.FinitePairHistory (Fin K) Real n) :
    adversarialTableStepKernel algorithm n (table, history) =
      algorithm.policy n history ⊗ₘ
        Kernel.deterministic (table (n + 1)) (measurable_of_countable _) := by
  unfold adversarialTableStepKernel
  rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.prodMkLeft_apply]
  congr 1

theorem adversarialTableHistoryKernel_zero {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (table : AdversarialRewardTable K) :
    adversarialTableHistoryKernel algorithm 0 table =
      (algorithm.initialAction ⊗ₘ
        Kernel.deterministic (table 0) (measurable_of_countable _)).map
          (pairHistoryZeroMeasurableEquiv (Fin K) Real) := by
  unfold adversarialTableHistoryKernel
  rw [Kernel.map_apply _ (pairHistoryZeroMeasurableEquiv (Fin K) Real).measurable,
    Kernel.compProd_apply_eq_compProd_sectR, Kernel.const_apply]
  congr 2

theorem adversarialTableHistoryKernel_succ {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat)
    (table : AdversarialRewardTable K) :
    adversarialTableHistoryKernel algorithm (n + 1) table =
      ((adversarialTableHistoryKernel algorithm n table) ⊗ₘ
        Kernel.sectR (adversarialTableStepKernel algorithm n) table).map
          (pairHistorySuccMeasurableEquiv (Fin K) Real n) := by
  conv_lhs => unfold adversarialTableHistoryKernel
  rw [Kernel.map_apply _ (pairHistorySuccMeasurableEquiv (Fin K) Real n).measurable,
    Kernel.compProd_apply_eq_compProd_sectR]

/-- Future reward rows cannot affect an already observed history. -/
theorem adversarialTableHistoryKernel_prefix_congr {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat)
    (table other : AdversarialRewardTable K)
    (heq : ∀ t, t <= n -> table t = other t) :
    adversarialTableHistoryKernel algorithm n table =
      adversarialTableHistoryKernel algorithm n other := by
  induction n with
  | zero =>
    rw [adversarialTableHistoryKernel_zero, adversarialTableHistoryKernel_zero,
      heq 0 (by omega)]
  | succ n ih =>
    rw [adversarialTableHistoryKernel_succ, adversarialTableHistoryKernel_succ,
      ih (fun t ht => heq t (by omega))]
    have hk : Kernel.sectR (adversarialTableStepKernel algorithm n) table =
        Kernel.sectR (adversarialTableStepKernel algorithm n) other := by
      ext history : 1
      rw [Kernel.sectR_apply, Kernel.sectR_apply,
        adversarialTableStepKernel_apply, adversarialTableStepKernel_apply, heq (n + 1) le_rfl]
    rw [hk]

/-- Extend the finite shared-noise matrix by zero rows after its horizon. -/
def adversarialFullRewardTable {horizon m : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (i : Fin (m + 1)) :
    AdversarialRewardTable (m + 1) :=
  fun t arm => if ht : t < horizon then adversarialFullClippedReward eta gap i ⟨t, ht⟩ arm else 0

theorem measurable_adversarialFullRewardTable {horizon m : Nat}
    (gap : Real) (i : Fin (m + 1)) :
    Measurable (fun eta : Fin horizon -> Real => adversarialFullRewardTable eta gap i) := by
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro arm
  unfold adversarialFullRewardTable
  split
  · unfold adversarialFullClippedReward clipUnitReward
    fun_prop
  · exact measurable_const

theorem adversarialFullRewardTable_at {horizon m : Nat}
    (eta : Fin horizon -> Real) (gap : Real) (i : Fin (m + 1)) (t : Fin horizon) :
    adversarialFullRewardTable eta gap i t = adversarialFullClippedReward eta gap i t := by
  funext arm
  simp [adversarialFullRewardTable, t.isLt]

/-- Conditional policy history kernel parameterized by the finite noise path. -/
noncomputable def adversarialNoiseHistoryKernel {horizon m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (i : Fin (m + 1)) (n : Nat) :
    Kernel (Fin horizon -> Real) (History.FinitePairHistory (Fin (m + 1)) Real n) :=
  (adversarialTableHistoryKernel algorithm n).comap
    (fun eta => adversarialFullRewardTable eta gap i) (measurable_adversarialFullRewardTable gap i)

instance {horizon m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (i : Fin (m + 1)) (n : Nat) :
    IsMarkovKernel (adversarialNoiseHistoryKernel (horizon := horizon) algorithm gap i n) := by
  unfold adversarialNoiseHistoryKernel
  infer_instance

/-- Shared-noise matrix and the original randomized policy on one joint space. -/
noncomputable def adversarialNoiseHistoryJoint {horizon m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) (n : Nat) :
    Measure ((Fin horizon -> Real) × History.FinitePairHistory (Fin (m + 1)) Real n) :=
  adversarialCenteredNoiseLaw horizon sigma ⊗ₘ adversarialNoiseHistoryKernel algorithm gap i n

instance {horizon m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) (n : Nat) :
    IsProbabilityMeasure (adversarialNoiseHistoryJoint (horizon := horizon) algorithm sigma gap i n) := by
  unfold adversarialNoiseHistoryJoint adversarialCenteredNoiseLaw
  infer_instance

theorem adversarialNoiseHistoryJoint_noise_marginal {horizon m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) (n : Nat) :
    (adversarialNoiseHistoryJoint (horizon := horizon) algorithm sigma gap i n).fst =
      adversarialCenteredNoiseLaw horizon sigma := by
  unfold adversarialNoiseHistoryJoint
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw horizon sigma) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  exact Measure.fst_compProd _ _

/-- Resampling an unobserved noise coordinate leaves the prefix law unchanged. -/
theorem adversarialNoiseHistoryKernel_update_future {horizon m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (i : Fin (m + 1)) (n : Nat) (eta : Fin horizon -> Real)
    (j : Fin horizon) (hj : n < j.val) (x : Real) :
    adversarialNoiseHistoryKernel algorithm gap i n (Function.update eta j x) =
      adversarialNoiseHistoryKernel algorithm gap i n eta := by
  unfold adversarialNoiseHistoryKernel
  rw [Kernel.comap_apply, Kernel.comap_apply]
  apply adversarialTableHistoryKernel_prefix_congr
  intro t ht
  funext arm
  unfold adversarialFullRewardTable
  split
  · rename_i hb
    have hne : (⟨t, hb⟩ : Fin horizon) ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      change t = j.val at hv
      omega
    simp [adversarialFullClippedReward, Function.update_of_ne hne]
  · rfl

/-- Isolate any coordinate of the shared Gaussian noise as a product factor. -/
theorem adversarialCenteredNoiseLaw_split {N : Nat} (sigma : Real) (j : Fin (N + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Real) j)
      (adversarialCenteredNoiseLaw (N + 1) sigma)
      ((gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩).prod
        (adversarialCenteredNoiseLaw N sigma)) := by
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) j

/-- In split coordinates, the prefix history law is independent of the future factor. -/
theorem adversarialNoiseHistoryKernel_split_future {N m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (i : Fin (m + 1)) (n : Nat) (j : Fin (N + 1)) (hj : n < j.val)
    (rest : Fin N -> Real) (x y : Real) :
    adversarialNoiseHistoryKernel algorithm gap i n (j.insertNth x rest) =
      adversarialNoiseHistoryKernel algorithm gap i n (j.insertNth y rest) := by
  unfold adversarialNoiseHistoryKernel
  rw [Kernel.comap_apply, Kernel.comap_apply]
  apply adversarialTableHistoryKernel_prefix_congr
  intro t ht
  funext arm
  unfold adversarialFullRewardTable
  split
  · rename_i hb
    have hlt : (⟨t, hb⟩ : Fin (N + 1)) < j := by
      change t < j.val
      omega
    simp only [adversarialFullClippedReward, Fin.insertNth_apply_below hlt]
  · rfl

/-- Tonelli in the independent-coordinate representation of the hard noise law. -/
theorem lintegral_adversarialCenteredNoiseLaw_split {N : Nat}
    (sigma : Real) (j : Fin (N + 1))
    (f : (Fin (N + 1) -> Real) -> ENNReal) (hf : Measurable f) :
    (∫⁻ eta, f eta ∂adversarialCenteredNoiseLaw (N + 1) sigma) =
      ∫⁻ x, ∫⁻ rest, f (j.insertNth x rest) ∂adversarialCenteredNoiseLaw N sigma
        ∂gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Real) j
  have he := (adversarialCenteredNoiseLaw_split sigma j).symm
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw N sigma) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  rw [MeasurePreserving.lintegral_map_equiv f e.symm he]
  exact lintegral_prod _ (hf.comp e.symm.measurable).aemeasurable

theorem adversarialCenteredNoiseLaw_full_reward_marginal
    {horizon m : Nat} (sigma gap : Real) (i : Fin (m + 1))
    (t : Fin horizon) (arm : Fin (m + 1)) :
    (adversarialCenteredNoiseLaw horizon sigma).map
      (fun eta => adversarialFullClippedReward eta gap i t arm) =
      adversarialClippedArmLaw sigma (adversarialFullHardShift gap i arm) := by
  unfold adversarialCenteredNoiseLaw adversarialClippedArmLaw adversarialFullClippedReward
  have hm := measurable_adversarialClippedArmMap (adversarialFullHardShift gap i arm)
  have he := (measurePreserving_eval (fun _ : Fin horizon =>
    gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) t).map_eq
  conv_rhs => rw [← he, Measure.map_map hm (measurable_pi_apply t)]
  rfl

theorem lintegral_adversarialTableHistoryKernel_zero {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (table : AdversarialRewardTable K)
    (f : History.FinitePairHistory (Fin K) Real 0 -> ENNReal) (hf : Measurable f) :
    (∫⁻ h, f h ∂adversarialTableHistoryKernel algorithm 0 table) =
      ∫⁻ arm, f (pairHistoryZeroMeasurableEquiv (Fin K) Real (arm, table 0 arm))
        ∂algorithm.initialAction := by
  rw [adversarialTableHistoryKernel_zero,
    lintegral_map hf (pairHistoryZeroMeasurableEquiv (Fin K) Real).measurable,
    Measure.lintegral_compProd (show Measurable (fun a => f
      (pairHistoryZeroMeasurableEquiv (Fin K) Real a)) from
        hf.comp (pairHistoryZeroMeasurableEquiv (Fin K) Real).measurable)]
  simp only [Kernel.lintegral_deterministic]

/-- The initial matrix mixture has exactly the canonical clipped observation law. -/
theorem lintegral_adversarialNoiseHistoryKernel_zero {N m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1))
    (f : History.FinitePairHistory (Fin (m + 1)) Real 0 -> ENNReal) (hf : Measurable f) :
    (∫⁻ eta, ∫⁻ h, f h ∂adversarialNoiseHistoryKernel (horizon := N + 1) algorithm gap i 0 eta
      ∂adversarialCenteredNoiseLaw (N + 1) sigma) =
      ∫⁻ h, f h ∂adversarialClippedHistoryLaw algorithm sigma (adversarialFullHardShift gap i) 0 := by
  let e := pairHistoryZeroMeasurableEquiv (Fin (m + 1)) Real
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw (N + 1) sigma) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  have hz (eta : Fin (N + 1) -> Real) :
      (∫⁻ h, f h ∂adversarialNoiseHistoryKernel algorithm gap i 0 eta) =
      ∫⁻ arm, f (e (arm, adversarialFullClippedReward eta gap i 0 arm))
        ∂algorithm.initialAction := by
    unfold adversarialNoiseHistoryKernel
    rw [Kernel.comap_apply, lintegral_adversarialTableHistoryKernel_zero algorithm _ f hf]
    simp [adversarialFullRewardTable, e]
  simp_rw [hz]
  have hm : Measurable (fun p : (Fin (N + 1) -> Real) × Fin (m + 1) =>
      f (e (p.2, adversarialFullClippedReward p.1 gap i 0 p.2))) := by
    apply measurable_from_prod_countable_left
    intro arm
    apply hf.comp
    apply e.measurable.comp
    apply measurable_const.prodMk
    unfold adversarialFullClippedReward clipUnitReward
    fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  unfold adversarialClippedHistoryLaw
  rw [canonicalBanditHistoryMeasure_zero, lintegral_map hf e.measurable,
    Measure.lintegral_compProd (show Measurable (fun a => f (e a)) from hf.comp e.measurable)]
  apply lintegral_congr
  intro arm
  have hfm : Measurable (fun x : Real => f (e (arm, x))) :=
    hf.comp (e.measurable.comp (measurable_const.prodMk measurable_id))
  have hrm : Measurable (fun eta : Fin (N + 1) -> Real =>
      adversarialFullClippedReward eta gap i 0 arm) := by
    unfold adversarialFullClippedReward clipUnitReward
    fun_prop
  rw [← lintegral_map hfm hrm, adversarialCenteredNoiseLaw_full_reward_marginal]
  rfl

/-- Initial case of the joint-space history marginal identification. -/
theorem adversarialNoiseHistoryJoint_history_marginal_zero {N m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) :
    (adversarialNoiseHistoryJoint (horizon := N + 1) algorithm sigma gap i 0).snd =
      adversarialClippedHistoryLaw algorithm sigma (adversarialFullHardShift gap i) 0 := by
  apply Measure.ext_of_lintegral
  intro f hf
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw (N + 1) sigma) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  unfold Measure.snd adversarialNoiseHistoryJoint
  rw [lintegral_map hf measurable_snd,
    Measure.lintegral_compProd (show Measurable
      (fun p : (Fin (N + 1) -> Real) × History.FinitePairHistory (Fin (m + 1)) Real 0 => f p.2)
      from hf.comp measurable_snd)]
  exact lintegral_adversarialNoiseHistoryKernel_zero algorithm sigma gap i f hf

/-- Conditional table-history recursion, with deterministic feedback integrated out. -/
theorem lintegral_adversarialTableHistoryKernel_succ {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (table : AdversarialRewardTable K)
    (n : Nat) (f : History.FinitePairHistory (Fin K) Real (n + 1) -> ENNReal)
    (hf : Measurable f) :
    (∫⁻ h, f h ∂adversarialTableHistoryKernel algorithm (n + 1) table) =
      ∫⁻ h, ∫⁻ arm, f (pairHistorySuccMeasurableEquiv (Fin K) Real n
        (h, (arm, table (n + 1) arm))) ∂algorithm.policy n h
        ∂adversarialTableHistoryKernel algorithm n table := by
  let e := pairHistorySuccMeasurableEquiv (Fin K) Real n
  rw [adversarialTableHistoryKernel_succ, lintegral_map hf e.measurable,
    Measure.lintegral_compProd (show Measurable (fun p => f (e p)) from hf.comp e.measurable)]
  apply lintegral_congr
  intro h
  rw [Kernel.sectR_apply, adversarialTableStepKernel_apply,
    Measure.lintegral_compProd (show Measurable (fun p => f (e (h, p))) from
      hf.comp (e.measurable.comp (measurable_const.prodMk measurable_id)))]
  simp only [Kernel.lintegral_deterministic]
  rfl

/-- Integrate fresh shared noise against a fixed prefix law and the same policy. -/
theorem lintegral_adversarialFreshNoise_step {K : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin K) Real) (n : Nat)
    (P : Measure (History.FinitePairHistory (Fin K) Real n)) [IsProbabilityMeasure P]
    (sigma : Real) (shift : Fin K -> Real)
    (f : History.FinitePairHistory (Fin K) Real n × (Fin K × Real) -> ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, ∫⁻ h, ∫⁻ arm, f (h, (arm, clipUnitReward (1 / 2 + x + shift arm)))
      ∂algorithm.policy n h ∂P ∂gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) =
      ∫⁻ h, ∫⁻ pair, f (h, pair)
        ∂Thompson.historyStepKernel algorithm
          (stationaryBanditHistoryEnvironment (adversarialClippedKernel sigma shift)) n h ∂P := by
  let G := gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩
  let H := History.FinitePairHistory (Fin K) Real n
  let F := fun (x : Real) (p : H × Fin K) =>
    f (p.1, (p.2, clipUnitReward (1 / 2 + x + shift p.2)))
  have hm : Measurable (Function.uncurry F) := by
    apply hf.comp
    have hs : Measurable shift := measurable_of_countable shift
    unfold clipUnitReward
    fun_prop
  have hex (x : Real) : (∫⁻ h, ∫⁻ arm, F x (h, arm) ∂algorithm.policy n h ∂P) =
      ∫⁻ p, F x p ∂P ⊗ₘ algorithm.policy n :=
    (Measure.lintegral_compProd (hm.comp (measurable_const.prodMk measurable_id))).symm
  change (∫⁻ x, ∫⁻ h, ∫⁻ arm, F x (h, arm) ∂algorithm.policy n h ∂P ∂G) = _
  simp_rw [hex]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  rw [Measure.lintegral_compProd hm.lintegral_prod_left]
  apply lintegral_congr
  intro h
  have hsect : Kernel.sectR
      ((stationaryBanditHistoryEnvironment (adversarialClippedKernel sigma shift)).feedback n) h =
      adversarialClippedKernel sigma shift := by
    ext arm : 1
    rw [Kernel.sectR_apply, stationaryBanditHistoryEnvironment_feedback_apply]
  rw [Thompson.historyStepKernel, Kernel.compProd_apply_eq_compProd_sectR, hsect,
    Measure.lintegral_compProd (show Measurable (fun pair => f (h, pair)) from
      hf.comp (measurable_const.prodMk measurable_id))]
  apply lintegral_congr
  intro arm
  change (∫⁻ x, f (h, (arm, clipUnitReward (1 / 2 + x + shift arm))) ∂G) =
    ∫⁻ r, f (h, (arm, r)) ∂adversarialClippedArmLaw sigma (shift arm)
  unfold adversarialClippedArmLaw
  rw [lintegral_map (show Measurable (fun r => f (h, (arm, r))) from
    hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    (measurable_adversarialClippedArmMap (shift arm))]

/-- Successor history integration on each fixed remaining-noise slice. -/
theorem lintegral_adversarialNoiseHistoryKernel_succ_slice {N m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) (n : Nat) (hn : n + 1 < N + 1)
    (rest : Fin N -> Real)
    (f : History.FinitePairHistory (Fin (m + 1)) Real (n + 1) -> ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, ∫⁻ h, f h ∂adversarialNoiseHistoryKernel algorithm gap i (n + 1)
      ((⟨n + 1, hn⟩ : Fin (N + 1)).insertNth x rest)
      ∂gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) =
    ∫⁻ h, ∫⁻ pair, f (pairHistorySuccMeasurableEquiv (Fin (m + 1)) Real n (h, pair))
      ∂Thompson.historyStepKernel algorithm (stationaryBanditHistoryEnvironment
        (adversarialClippedKernel sigma (adversarialFullHardShift gap i))) n h
      ∂adversarialNoiseHistoryKernel algorithm gap i n
        ((⟨n + 1, hn⟩ : Fin (N + 1)).insertNth 0 rest) := by
  let j : Fin (N + 1) := ⟨n + 1, hn⟩
  let e := pairHistorySuccMeasurableEquiv (Fin (m + 1)) Real n
  have hz (x : Real) :
      (∫⁻ h, f h ∂adversarialNoiseHistoryKernel algorithm gap i (n + 1) (j.insertNth x rest)) =
      ∫⁻ h, ∫⁻ arm, f (e (h, (arm, clipUnitReward (1 / 2 + x + adversarialFullHardShift gap i arm))))
        ∂algorithm.policy n h ∂adversarialNoiseHistoryKernel algorithm gap i n (j.insertNth 0 rest) := by
    conv_lhs =>
      unfold adversarialNoiseHistoryKernel
      rw [Kernel.comap_apply, lintegral_adversarialTableHistoryKernel_succ algorithm _ n f hf]
    have hc := adversarialNoiseHistoryKernel_split_future algorithm gap i n j
      (show n < j.val by dsimp [j]; omega) rest x 0
    unfold adversarialNoiseHistoryKernel at hc
    rw [Kernel.comap_apply, Kernel.comap_apply] at hc
    rw [hc]
    apply lintegral_congr
    intro h
    apply lintegral_congr
    intro arm
    have hr : adversarialFullRewardTable (j.insertNth x rest) gap i (n + 1) arm =
        clipUnitReward (1 / 2 + x + adversarialFullHardShift gap i arm) := by
      simp [adversarialFullRewardTable, hn, adversarialFullClippedReward, j]
    rw [hr]
  change (∫⁻ x, ∫⁻ h, f h ∂adversarialNoiseHistoryKernel algorithm gap i (n + 1)
    (j.insertNth x rest) ∂gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) = _
  simp_rw [hz]
  exact lintegral_adversarialFreshNoise_step algorithm n
    (adversarialNoiseHistoryKernel algorithm gap i n (j.insertNth 0 rest))
    sigma (adversarialFullHardShift gap i) (fun p => f (e p)) (hf.comp e.measurable)

/-- Full-noise successor recursion after integrating the independent next coordinate. -/
theorem lintegral_adversarialNoiseHistoryKernel_succ {N m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) (n : Nat) (hn : n + 1 < N + 1)
    (f : History.FinitePairHistory (Fin (m + 1)) Real (n + 1) -> ENNReal)
    (hf : Measurable f) :
    (∫⁻ eta, ∫⁻ h, f h ∂adversarialNoiseHistoryKernel (horizon := N + 1) algorithm gap i (n + 1) eta
      ∂adversarialCenteredNoiseLaw (N + 1) sigma) =
    ∫⁻ eta, ∫⁻ h, ∫⁻ pair, f (pairHistorySuccMeasurableEquiv (Fin (m + 1)) Real n (h, pair))
      ∂Thompson.historyStepKernel algorithm (stationaryBanditHistoryEnvironment
        (adversarialClippedKernel sigma (adversarialFullHardShift gap i))) n h
      ∂adversarialNoiseHistoryKernel algorithm gap i n eta
      ∂adversarialCenteredNoiseLaw (N + 1) sigma := by
  let j : Fin (N + 1) := ⟨n + 1, hn⟩
  let e := pairHistorySuccMeasurableEquiv (Fin (m + 1)) Real n
  let step := Thompson.historyStepKernel algorithm (stationaryBanditHistoryEnvironment
    (adversarialClippedKernel sigma (adversarialFullHardShift gap i))) n
  let B := fun h => ∫⁻ pair, f (e (h, pair)) ∂step h
  let A := fun eta : Fin (N + 1) -> Real =>
    ∫⁻ h, f h ∂adversarialNoiseHistoryKernel algorithm gap i (n + 1) eta
  let C := fun eta : Fin (N + 1) -> Real =>
    ∫⁻ h, B h ∂adversarialNoiseHistoryKernel algorithm gap i n eta
  have hA : Measurable A := hf.lintegral_kernel
  have hB : Measurable B :=
    (show Measurable (Function.uncurry (fun h pair => f (e (h, pair)))) from
      hf.comp e.measurable).lintegral_kernel_prod_right
  have hC : Measurable C := hB.lintegral_kernel
  have hfuture (x : Real) (rest : Fin N -> Real) : C (j.insertNth x rest) = C (j.insertNth 0 rest) := by
    unfold C
    rw [adversarialNoiseHistoryKernel_split_future algorithm gap i n j
      (show n < j.val by dsimp [j]; omega) rest x 0]
  have hCsplit : (∫⁻ eta, C eta ∂adversarialCenteredNoiseLaw (N + 1) sigma) =
      ∫⁻ rest, C (j.insertNth 0 rest) ∂adversarialCenteredNoiseLaw N sigma := by
    rw [lintegral_adversarialCenteredNoiseLaw_split sigma j C hC]
    simp_rw [hfuture]
    simp
  change (∫⁻ eta, A eta ∂adversarialCenteredNoiseLaw (N + 1) sigma) =
    ∫⁻ eta, C eta ∂adversarialCenteredNoiseLaw (N + 1) sigma
  rw [hCsplit, lintegral_adversarialCenteredNoiseLaw_split sigma j A hA]
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw N sigma) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  have hs : Measurable (fun p : Real × (Fin N -> Real) => A (j.insertNth p.1 p.2)) :=
    hA.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Real) j).symm.measurable
  rw [lintegral_lintegral_swap hs.aemeasurable]
  apply lintegral_congr
  intro rest
  exact lintegral_adversarialNoiseHistoryKernel_succ_slice algorithm sigma gap i n hn rest f hf

/-- All observed finite prefixes have the canonical clipped history law. -/
theorem lintegral_adversarialNoiseHistoryKernel_eq_clipped {N m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) (n : Nat) (hn : n < N + 1)
    (f : History.FinitePairHistory (Fin (m + 1)) Real n -> ENNReal) (hf : Measurable f) :
    (∫⁻ eta, ∫⁻ h, f h ∂adversarialNoiseHistoryKernel (horizon := N + 1) algorithm gap i n eta
      ∂adversarialCenteredNoiseLaw (N + 1) sigma) =
      ∫⁻ h, f h ∂adversarialClippedHistoryLaw algorithm sigma (adversarialFullHardShift gap i) n := by
  induction n with
  | zero => exact lintegral_adversarialNoiseHistoryKernel_zero algorithm sigma gap i f hf
  | succ n ih =>
    let e := pairHistorySuccMeasurableEquiv (Fin (m + 1)) Real n
    let step := Thompson.historyStepKernel algorithm (stationaryBanditHistoryEnvironment
      (adversarialClippedKernel sigma (adversarialFullHardShift gap i))) n
    let B := fun h => ∫⁻ pair, f (e (h, pair)) ∂step h
    have hB : Measurable B :=
      (show Measurable (Function.uncurry (fun h pair => f (e (h, pair)))) from
        hf.comp e.measurable).lintegral_kernel_prod_right
    rw [lintegral_adversarialNoiseHistoryKernel_succ algorithm sigma gap i n hn f hf]
    change (∫⁻ eta, ∫⁻ h, B h ∂adversarialNoiseHistoryKernel algorithm gap i n eta
      ∂adversarialCenteredNoiseLaw (N + 1) sigma) = _
    rw [ih (by omega) B hB]
    unfold adversarialClippedHistoryLaw
    rw [canonicalBanditHistoryMeasure_succ, lintegral_map hf e.measurable,
      Measure.lintegral_compProd (show Measurable (fun p => f (e p)) from hf.comp e.measurable)]

/-- Full matrix-policy coupling: its history marginal is exactly Claim 17.6's law. -/
theorem adversarialNoiseHistoryJoint_history_marginal {N m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (sigma gap : Real) (i : Fin (m + 1)) (n : Nat) (hn : n < N + 1) :
    (adversarialNoiseHistoryJoint (horizon := N + 1) algorithm sigma gap i n).snd =
      adversarialClippedHistoryLaw algorithm sigma (adversarialFullHardShift gap i) n := by
  apply Measure.ext_of_lintegral
  intro f hf
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw (N + 1) sigma) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  unfold Measure.snd adversarialNoiseHistoryJoint
  rw [lintegral_map hf measurable_snd,
    Measure.lintegral_compProd (show Measurable
      (fun p : (Fin (N + 1) -> Real) × History.FinitePairHistory (Fin (m + 1)) Real n => f p.2)
      from hf.comp measurable_snd)]
  exact lintegral_adversarialNoiseHistoryKernel_eq_clipped algorithm sigma gap i n hn f hf

/-- Corrected Claim 17.6 on the shared-noise matrix and policy joint space. -/
theorem adversarialNoiseHistoryJoint_pull_le_half_claim17_6 {m : Nat}
    (hm : 0 < m) (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (n : Nat) (sigma delta : Real) (hs : sigma ≠ 0)
    (hd : 0 < delta) (hd8 : delta < 1 / 8) :
    ∃ i : Fin (m + 1), 2 * delta <=
      (adversarialNoiseHistoryJoint (horizon := n + 1) algorithm sigma
        (adversarialClaim17_6Gap (n + 1) m sigma delta) i n).real
        {p | finiteHistoryPullCountReal n p.2 i <= ((n + 1 : Nat) : Real) / 2} := by
  obtain ⟨i, hi⟩ := adversarialClippedHistory_pull_le_half_claim17_6 hm algorithm n sigma delta hs hd hd8
  refine ⟨i, ?_⟩
  let A := {h : History.FinitePairHistory (Fin (m + 1)) Real n |
    finiteHistoryPullCountReal n h i <= ((n + 1 : Nat) : Real) / 2}
  have hA : MeasurableSet A := measurableSet_le
    (measurable_finiteHistoryPullCountReal n i) measurable_const
  have he := congrArg (fun μ => μ A) (adversarialNoiseHistoryJoint_history_marginal
    algorithm sigma (adversarialClaim17_6Gap (n + 1) m sigma delta) i n (Nat.lt_succ_self n))
  unfold Measure.snd at he
  dsimp only at he
  rw [Measure.map_apply measurable_snd hA] at he
  change 2 * delta <= ((adversarialNoiseHistoryJoint (horizon := n + 1) algorithm sigma
    (adversarialClaim17_6Gap (n + 1) m sigma delta) i n) (Prod.snd ⁻¹' A)).toReal
  rw [he]
  exact hi

theorem measurable_adversarialClippingCountReal {horizon : Nat} (gap : Real) :
    Measurable (fun eta : Fin horizon -> Real => adversarialClippingCountReal eta gap) := by
  change Measurable (fun eta : Fin horizon -> Real => ∑ t : Fin horizon, adversarialClipIndicator gap (eta t))
  exact Finset.measurable_sum _ (fun t _ =>
    (measurable_adversarialClipIndicator gap).comp (measurable_pi_apply t))

theorem adversarialNoiseHistoryJoint_clipping_tail {horizon m : Nat}
    (hn : 0 < horizon) (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (delta gap : Real) (hd : 0 < delta) (hd1 : delta < 1) (hg8 : gap < 1 / 8)
    (i : Fin (m + 1)) (n : Nat) (horizon_condition : 32 * Real.log (1 / delta) <= horizon) :
    (adversarialNoiseHistoryJoint (horizon := horizon) algorithm (1 / 10) gap i n).real
      {p | (horizon : Real) / 4 <= adversarialClippingCountReal p.1 gap} <= delta := by
  let B := {eta : Fin horizon -> Real | (horizon : Real) / 4 <= adversarialClippingCountReal eta gap}
  have hB : MeasurableSet B := measurableSet_le measurable_const (measurable_adversarialClippingCountReal gap)
  have he := congrArg (fun μ => μ B)
    (adversarialNoiseHistoryJoint_noise_marginal (horizon := horizon) algorithm (1 / 10) gap i n)
  unfold Measure.fst at he
  dsimp only at he
  rw [Measure.map_apply measurable_fst hB] at he
  change ((adversarialNoiseHistoryJoint (horizon := horizon) algorithm (1 / 10) gap i n)
    (Prod.fst ⁻¹' B)).toReal <= delta
  rw [he]
  exact adversarialClippingCount_tail_claim17_7 hn delta gap hd hd1 hg8 horizon_condition

/-- Pull-small and literally few clipped rounds hold jointly with probability at least delta. -/
theorem adversarialNoiseHistoryJoint_good_event {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) (n : Nat)
    (delta : Real) (hd : 0 < delta) (hd8 : delta < 1 / 8)
    (hg8 : adversarialClaim17_6Gap (n + 1) m (1 / 10) delta < 1 / 8)
    (horizon_condition : 32 * Real.log (1 / delta) <= ((n + 1 : Nat) : Real)) :
    ∃ i : Fin (m + 1), delta <=
      (adversarialNoiseHistoryJoint (horizon := n + 1) algorithm (1 / 10)
        (adversarialClaim17_6Gap (n + 1) m (1 / 10) delta) i n).real
        {p | finiteHistoryPullCountReal n p.2 i <= ((n + 1 : Nat) : Real) / 2 ∧
          adversarialFullBoundaryCount p.1 (adversarialClaim17_6Gap (n + 1) m (1 / 10) delta) i <
            ((n + 1 : Nat) : Real) / 4} := by
  let gap := adversarialClaim17_6Gap (n + 1) m (1 / 10) delta
  have hg : 0 <= gap := by unfold gap adversarialClaim17_6Gap; positivity
  obtain ⟨i, hi⟩ := adversarialNoiseHistoryJoint_pull_le_half_claim17_6 hm algorithm n
    (1 / 10) delta (by norm_num) hd hd8
  let P := adversarialNoiseHistoryJoint (horizon := n + 1) algorithm (1 / 10) gap i n
  let A := {p : (Fin (n + 1) -> Real) × History.FinitePairHistory (Fin (m + 1)) Real n |
    finiteHistoryPullCountReal n p.2 i <= ((n + 1 : Nat) : Real) / 2}
  let B := {p : (Fin (n + 1) -> Real) × History.FinitePairHistory (Fin (m + 1)) Real n |
    ((n + 1 : Nat) : Real) / 4 <= adversarialClippingCountReal p.1 gap}
  have hclip : P.real B <= delta := adversarialNoiseHistoryJoint_clipping_tail
    (Nat.succ_pos n) algorithm delta gap hd (by linarith) hg8 i n horizon_condition
  have hgood := measureReal_diff_ge_delta P A B delta hi hclip
  refine ⟨i, hgood.trans (measureReal_mono ?_ (by finiteness))⟩
  intro p hp
  refine ⟨hp.1, ?_⟩
  have hc : adversarialClippingCountReal p.1 gap < ((n + 1 : Nat) : Real) / 4 :=
    lt_of_not_ge hp.2
  exact (adversarialFullBoundaryCount_le p.1 gap hg i).trans_lt hc

/-- The realized action path, indexed by the actual number of observations. -/
def adversarialHistoryActions {K : Nat} (n : Nat)
    (h : History.FinitePairHistory (Fin K) Real n) : Fin (n + 1) -> Fin K :=
  fun t => (h ⟨t.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp t.isLt)⟩).1

theorem adversarialHistoryActions_pullCountENNReal {K : Nat} (n : Nat)
    (h : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    finiteHistoryPullCountENNReal n h arm =
      ∑ t, if adversarialHistoryActions n h t = arm then (1 : ENNReal) else 0 := by
  induction n with
  | zero =>
    change finiteHistoryPullCountENNReal 0 h arm =
      ∑ t : Fin 1, if adversarialHistoryActions 0 h t = arm then (1 : ENNReal) else 0
    rw [Fin.sum_univ_one]
    simp only [finiteHistoryPullCountENNReal]
    rfl
  | succ n ih =>
    rw [finiteHistoryPullCountENNReal, ih]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    rfl

theorem adversarialHistoryActions_pullCountReal {K : Nat} (n : Nat)
    (h : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    finiteHistoryPullCountReal n h arm =
      ∑ t, if adversarialHistoryActions n h t = arm then (1 : Real) else 0 := by
  unfold finiteHistoryPullCountReal
  rw [adversarialHistoryActions_pullCountENNReal, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro t _
    split <;> simp
  · intro t _
    split <;> simp

/-- Eq. (17.8) on the same history coordinates as the joint good event. -/
theorem adversarialHistory_randomRegret_ge_quarter {m : Nat} (n : Nat)
    (eta : Fin (n + 1) -> Real) (gap : Real) (hg : 0 <= gap) (i : Fin (m + 1))
    (h : History.FinitePairHistory (Fin (m + 1)) Real n)
    (hp : finiteHistoryPullCountReal n h i <= ((n + 1 : Nat) : Real) / 2)
    (hc : adversarialFullBoundaryCount eta gap i <= ((n + 1 : Nat) : Real) / 4) :
    gap * (((n + 1 : Nat) : Real) / 4) <=
      adversarialRandomRegret (adversarialFullClippedReward eta gap i) (adversarialHistoryActions n h) := by
  have he := adversarialFullRandomRegret_ge_boundary_eq17_8 eta gap hg i (adversarialHistoryActions n h)
  rw [← adversarialHistoryActions_pullCountReal] at he
  have ha : ((n + 1 : Nat) : Real) / 4 <=
      ((n + 1 : Nat) : Real) - finiteHistoryPullCountReal n h i - adversarialFullBoundaryCount eta gap i := by
    linarith
  exact (mul_le_mul_of_nonneg_left ha hg).trans he

/-- Random-regret tail on the coupled hard matrix, before final constant calibration. -/
theorem adversarialNoiseHistoryJoint_randomRegret_tail {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) (n : Nat)
    (delta : Real) (hd : 0 < delta) (hd8 : delta < 1 / 8)
    (hg8 : adversarialClaim17_6Gap (n + 1) m (1 / 10) delta < 1 / 8)
    (horizon_condition : 32 * Real.log (1 / delta) <= ((n + 1 : Nat) : Real)) :
    ∃ i : Fin (m + 1), delta <=
      (adversarialNoiseHistoryJoint (horizon := n + 1) algorithm (1 / 10)
        (adversarialClaim17_6Gap (n + 1) m (1 / 10) delta) i n).real
        {p | adversarialClaim17_6Gap (n + 1) m (1 / 10) delta * (((n + 1 : Nat) : Real) / 4) <=
          adversarialRandomRegret
            (adversarialFullClippedReward p.1 (adversarialClaim17_6Gap (n + 1) m (1 / 10) delta) i)
            (adversarialHistoryActions n p.2)} := by
  obtain ⟨i, hi⟩ := adversarialNoiseHistoryJoint_good_event hm algorithm n delta hd hd8 hg8 horizon_condition
  refine ⟨i, hi.trans (measureReal_mono ?_ (by finiteness))⟩
  intro p hp
  exact adversarialHistory_randomRegret_ge_quarter n p.1
    (adversarialClaim17_6Gap (n + 1) m (1 / 10) delta)
    (by unfold adversarialClaim17_6Gap; positivity) i p.2 hp.1 hp.2.le

/-- First-moment extraction for a measurable kernel event. Mathlib candidate. -/
theorem exists_kernel_section_mass_ge {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (κ : Kernel X Y) [IsMarkovKernel κ]
    (E : Set (X × Y)) (hE : MeasurableSet E) (delta : Real)
    (hd : delta <= (μ ⊗ₘ κ).real E) :
    ∃ x, delta <= (κ x).real (Prod.mk x ⁻¹' E) := by
  let mass := fun x => κ x (Prod.mk x ⁻¹' E)
  have hm : Measurable mass := Kernel.measurable_kernel_prodMk_left hE
  have hi : Integrable (fun x => (mass x).toReal) μ := by
    apply Integrable.of_bound hm.ennreal_toReal.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one
  apply exists_tailMass_ge_of_integral_ge μ (fun x => (mass x).toReal) delta hi
  rw [integral_toReal hm.aemeasurable (ae_of_all μ (fun x => by
    change κ x (Prod.mk x ⁻¹' E) < ∞
    finiteness))]
  rw [show (∫⁻ x, mass x ∂μ) = (μ ⊗ₘ κ) E from (Measure.compProd_apply hE).symm]
  exact hd

theorem measurable_adversarialRandomRegret {horizon m : Nat}
    (actions : Fin horizon -> Fin (m + 1)) :
    Measurable (fun reward : Fin horizon -> Fin (m + 1) -> Real => adversarialRandomRegret reward actions) := by
  unfold adversarialRandomRegret
  have hm (arm : Fin (m + 1)) : Measurable (fun reward : Fin horizon -> Fin (m + 1) -> Real =>
      adversarialComparatorRegret reward actions arm) := by
    unfold adversarialComparatorRegret
    exact Finset.measurable_sum _ (fun t _ =>
      ((measurable_pi_apply arm).comp (measurable_pi_apply t)).sub
        ((measurable_pi_apply (actions t)).comp (measurable_pi_apply t)))
  convert
    (Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (m + 1))))
      ⟨0, Finset.mem_univ 0⟩ (fun arm _ => hm arm)) using 1
  funext reward
  exact (Finset.sup'_apply (s := (Finset.univ : Finset (Fin (m + 1))))
    ⟨0, Finset.mem_univ 0⟩
    (fun arm (r : Fin horizon -> Fin (m + 1) -> Real) => adversarialComparatorRegret r actions arm) reward).symm

theorem measurable_adversarialJointRandomRegret {m : Nat} (n : Nat)
    (gap : Real) (i : Fin (m + 1)) :
    Measurable (fun p : (Fin (n + 1) -> Real) × History.FinitePairHistory (Fin (m + 1)) Real n =>
      adversarialRandomRegret (adversarialFullClippedReward p.1 gap i) (adversarialHistoryActions n p.2)) := by
  let X := (Fin (n + 1) -> Real) × History.FinitePairHistory (Fin (m + 1)) Real n
  have hsel (t : Fin (n + 1)) : Measurable
      (fun p : (Fin (n + 1) -> Real) × Fin (m + 1) => adversarialFullClippedReward p.1 gap i t p.2) := by
    apply measurable_from_prod_countable_left
    intro arm
    unfold adversarialFullClippedReward clipUnitReward
    fun_prop
  have hm (arm : Fin (m + 1)) : Measurable (fun p : X =>
      adversarialComparatorRegret (adversarialFullClippedReward p.1 gap i) (adversarialHistoryActions n p.2) arm) := by
    unfold adversarialComparatorRegret
    apply Finset.measurable_sum
    intro t _
    apply Measurable.sub
    · exact (hsel t).comp (measurable_fst.prodMk measurable_const)
    · have ha : Measurable (fun p : X => adversarialHistoryActions n p.2 t) := by
        unfold adversarialHistoryActions
        exact measurable_fst.comp ((measurable_pi_apply _).comp measurable_snd)
      exact (hsel t).comp (measurable_fst.prodMk ha)
  unfold adversarialRandomRegret
  convert (Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (m + 1))))
    ⟨0, Finset.mem_univ 0⟩ (fun arm _ => hm arm)) using 1
  funext p
  exact (Finset.sup'_apply (s := (Finset.univ : Finset (Fin (m + 1))))
    ⟨0, Finset.mem_univ 0⟩ (fun arm (p : X) =>
      adversarialComparatorRegret (adversarialFullClippedReward p.1 gap i) (adversarialHistoryActions n p.2) arm) p).symm

/-- A deterministic bounded reward table realizes the uncalibrated random-regret tail. -/
theorem exists_adversarialTable_randomRegret_tail {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) (n : Nat)
    (delta : Real) (hd : 0 < delta) (hd8 : delta < 1 / 8)
    (hg8 : adversarialClaim17_6Gap (n + 1) m (1 / 10) delta < 1 / 8)
    (horizon_condition : 32 * Real.log (1 / delta) <= ((n + 1 : Nat) : Real)) :
    ∃ table : AdversarialRewardTable (m + 1),
      (∀ t arm, table t arm ∈ Set.Icc (0 : Real) 1) ∧
      delta <= (adversarialTableHistoryKernel algorithm n table).real
        {h | adversarialClaim17_6Gap (n + 1) m (1 / 10) delta * (((n + 1 : Nat) : Real) / 4) <=
          adversarialRandomRegret (fun t : Fin (n + 1) => table t.val) (adversarialHistoryActions n h)} := by
  let gap := adversarialClaim17_6Gap (n + 1) m (1 / 10) delta
  obtain ⟨i, hi⟩ := adversarialNoiseHistoryJoint_randomRegret_tail hm algorithm n delta hd hd8 hg8 horizon_condition
  let E := {p : (Fin (n + 1) -> Real) × History.FinitePairHistory (Fin (m + 1)) Real n |
    gap * (((n + 1 : Nat) : Real) / 4) <=
      adversarialRandomRegret (adversarialFullClippedReward p.1 gap i) (adversarialHistoryActions n p.2)}
  have hE : MeasurableSet E := measurableSet_le measurable_const (measurable_adversarialJointRandomRegret n gap i)
  haveI : IsProbabilityMeasure (adversarialCenteredNoiseLaw (n + 1) (1 / 10)) := by
    unfold adversarialCenteredNoiseLaw
    infer_instance
  obtain ⟨eta, heta⟩ := exists_kernel_section_mass_ge
    (adversarialCenteredNoiseLaw (n + 1) (1 / 10)) (adversarialNoiseHistoryKernel algorithm gap i n) E hE delta hi
  refine ⟨adversarialFullRewardTable eta gap i, ?_, ?_⟩
  · intro t arm
    unfold adversarialFullRewardTable
    split
    · unfold adversarialFullClippedReward clipUnitReward
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    · exact ⟨le_rfl, by norm_num⟩
  · have ht : (fun t : Fin (n + 1) => adversarialFullRewardTable eta gap i t.val) =
        adversarialFullClippedReward eta gap i := by
      funext t
      exact adversarialFullRewardTable_at eta gap i t
    rw [ht]
    exact heta

/-- Explicit logarithmic comparison on the corrected confidence domain. -/
theorem adversarialConfidence_log_calibration (delta : Real)
    (hd : 0 < delta) (hd32 : delta <= 1 / 32) :
    0 < Real.log (1 / (2 * delta)) ∧
    Real.log (1 / (2 * delta)) / 2 <= Real.log (1 / (8 * delta)) ∧
    Real.log (1 / delta) <= 2 * Real.log (1 / (2 * delta)) ∧
    Real.log (1 / (8 * delta)) <= Real.log (1 / (2 * delta)) := by
  have h4 : (4 : Real) <= 1 / (8 * delta) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hl4 : Real.log 4 <= Real.log (1 / (8 * delta)) :=
    Real.log_le_log (by norm_num) h4
  have h42 : Real.log (2 : Real) <= Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h2pos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have he2 : Real.log (1 / (2 * delta)) = Real.log 4 + Real.log (1 / (8 * delta)) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
    ring
  have he1 : Real.log (1 / delta) = Real.log 2 + Real.log (1 / (2 * delta)) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem adversarialClaim17_6Gap_tenth_sq {N m : Nat}
    (hN : 0 < N) (hm : 0 < m) (delta : Real) (hd : 0 < delta) (hd8 : delta < 1 / 8) :
    (adversarialClaim17_6Gap N m (1 / 10) delta) ^ 2 =
      (m : Real) * Real.log (1 / (8 * delta)) / (200 * N) := by
  have hl : 0 <= Real.log (1 / (8 * delta)) := by
    apply Real.log_nonneg
    rw [one_le_div (by positivity)]
    linarith
  unfold adversarialClaim17_6Gap
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (by positivity) hl)]
  field_simp
  ring

/-- The source clipping and gap conditions follow from a source-form horizon bound. -/
theorem adversarialHorizon_calibration {N m : Nat} (hN : 0 < N) (hm : 0 < m)
    (delta : Real) (hd : 0 < delta) (hd32 : delta <= 1 / 32)
    (horizon : 64 * ((m + 1 : Nat) : Real) * Real.log (1 / (2 * delta)) <= N) :
    adversarialClaim17_6Gap N m (1 / 10) delta < 1 / 8 ∧
      32 * Real.log (1 / delta) <= N := by
  obtain ⟨hlpos, hlhalf, hlone, hlmono⟩ := adversarialConfidence_log_calibration delta hd hd32
  have hm0 : (0 : Real) <= m := Nat.cast_nonneg m
  have hm1 : (1 : Real) <= (m + 1 : Nat) := by exact_mod_cast (by omega : 1 <= m + 1)
  have hb : 64 * Real.log (1 / (2 * delta)) <= N :=
    (mul_le_mul_of_nonneg_right (by nlinarith : (64 : Real) <= 64 * ((m + 1 : Nat) : Real)) hlpos.le).trans horizon
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hlmono hm0
    have hb' : (m : Real) * Real.log (1 / (8 * delta)) <= (N : Real) / 64 := by
      push_cast at horizon
      nlinarith
    have hsq := adversarialClaim17_6Gap_tenth_sq hN hm delta hd (by linarith)
    have hNpos : (0 : Real) < N := by exact_mod_cast hN
    have hsqbound : (adversarialClaim17_6Gap N m (1 / 10) delta)^2 <= 1 / 12800 := by
      rw [hsq, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith [sq_nonneg (adversarialClaim17_6Gap N m (1 / 10) delta - 1 / 8)]
  · linarith

/-- Strict slack converts the construction's non-strict event to a CDF-complement event. -/
theorem adversarialThreshold_calibration {N m : Nat} (hN : 0 < N) (hm : 0 < m)
    (delta : Real) (hd : 0 < delta) (hd32 : delta <= 1 / 32) :
    adversarialHighProbabilityThreshold N (m + 1) (1 / 160) delta <
      adversarialClaim17_6Gap N m (1 / 10) delta * ((N : Real) / 4) := by
  obtain ⟨hlpos, hlhalf, hlone, hlmono⟩ := adversarialConfidence_log_calibration delta hd hd32
  have hNpos : (0 : Real) < N := by exact_mod_cast hN
  have hmpos : (0 : Real) < m := by exact_mod_cast hm
  have hm2 : ((m + 1 : Nat) : Real) <= 2 * m := by exact_mod_cast (by omega : m + 1 <= 2 * m)
  have hl8 : 0 < Real.log (1 / (8 * delta)) := by linarith
  have hmul : ((m + 1 : Nat) : Real) * Real.log (1 / (2 * delta)) <=
      4 * m * Real.log (1 / (8 * delta)) := by
    have h1 := mul_le_mul_of_nonneg_right hm2 hlpos.le
    have h2 := mul_le_mul_of_nonneg_left (show Real.log (1 / (2 * delta)) <=
      2 * Real.log (1 / (8 * delta)) by linarith) (show 0 <= 2 * (m : Real) by positivity)
    nlinarith
  have hstrict : (N : Real) * (m + 1 : Nat) * Real.log (1 / (2 * delta)) <
      8 * N * m * Real.log (1 / (8 * delta)) := by
    have hb := mul_le_mul_of_nonneg_left hmul hNpos.le
    have hp : 0 < (N : Real) * m * Real.log (1 / (8 * delta)) := by positivity
    nlinarith
  have hs := adversarialClaim17_6Gap_tenth_sq hN hm delta hd (by linarith)
  have hright : (adversarialClaim17_6Gap N m (1 / 10) delta * ((N : Real) / 4)) ^ 2 =
      (N : Real) * m * Real.log (1 / (8 * delta)) / 3200 := by
    rw [mul_pow, hs]
    field_simp
    ring
  have hleft : (adversarialHighProbabilityThreshold N (m + 1) (1 / 160) delta)^2 =
      ((N : Real) * (m + 1 : Nat) * Real.log (1 / (2 * delta))) / 25600 := by
    unfold adversarialHighProbabilityThreshold
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  apply (sq_lt_sq₀ (by unfold adversarialHighProbabilityThreshold; positivity)
    (by unfold adversarialClaim17_6Gap; positivity)).mp
  rw [hleft, hright]
  nlinarith

/-- **Corrected Theorem 17.4.** Explicit constants and confidence domain;
the event is strict random regret, for a deterministic bounded reward table. -/
theorem exists_adversarialTable_randomRegret_gt_theorem17_4 {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) (n : Nat)
    (delta : Real) (hd : 0 < delta) (hd32 : delta <= 1 / 32)
    (horizon : 64 * ((m + 1 : Nat) : Real) * Real.log (1 / (2 * delta)) <= ((n + 1 : Nat) : Real)) :
    ∃ table : AdversarialRewardTable (m + 1),
      (∀ t arm, table t arm ∈ Set.Icc (0 : Real) 1) ∧
      delta <= (adversarialTableHistoryKernel algorithm n table).real
        {h | adversarialHighProbabilityThreshold (n + 1) (m + 1) (1 / 160) delta <
          adversarialRandomRegret (fun t : Fin (n + 1) => table t.val) (adversarialHistoryActions n h)} := by
  obtain ⟨hg8, hclip⟩ := adversarialHorizon_calibration (Nat.succ_pos n) hm delta hd hd32 horizon
  obtain ⟨table, htable, ht⟩ := exists_adversarialTable_randomRegret_tail hm algorithm n delta hd
    (by linarith) hg8 hclip
  refine ⟨table, htable, ht.trans (measureReal_mono ?_ (by finiteness))⟩
  intro h hh
  exact (adversarialThreshold_calibration (Nat.succ_pos n) hm delta hd hd32).trans_le hh

def adversarialTableRandomRegret {m : Nat} (table : AdversarialRewardTable (m + 1)) (n : Nat)
    (h : History.FinitePairHistory (Fin (m + 1)) Real n) : Real :=
  adversarialRandomRegret (fun t : Fin (n + 1) => table t.val) (adversarialHistoryActions n h)

/-- Deterministic expectation, separate from the pathwise random-regret variable. -/
noncomputable def adversarialTableExpectedRegret {m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (table : AdversarialRewardTable (m + 1)) (n : Nat) : Real :=
  ∫ h, adversarialTableRandomRegret table n h ∂adversarialTableHistoryKernel algorithm n table

noncomputable def adversarialTableCDF {m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (table : AdversarialRewardTable (m + 1)) (n : Nat) (u : Real) : Real :=
  (adversarialTableHistoryKernel algorithm n table).real {h | adversarialTableRandomRegret table n h <= u}

theorem measurable_adversarialTableRandomRegret {m : Nat}
    (table : AdversarialRewardTable (m + 1)) (n : Nat) :
    Measurable (adversarialTableRandomRegret table n) := by
  let H := History.FinitePairHistory (Fin (m + 1)) Real n
  let reward := fun t : Fin (n + 1) => table t.val
  have hm (arm : Fin (m + 1)) : Measurable (fun h : H =>
      adversarialComparatorRegret reward (adversarialHistoryActions n h) arm) := by
    unfold adversarialComparatorRegret
    apply Finset.measurable_sum
    intro t _
    apply measurable_const.sub
    have ha : Measurable (fun h : H => adversarialHistoryActions n h t) :=
      measurable_fst.comp (measurable_pi_apply _)
    exact (measurable_of_countable (reward t)).comp ha
  unfold adversarialTableRandomRegret adversarialRandomRegret
  convert (Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (m + 1))))
    ⟨0, Finset.mem_univ 0⟩ (fun arm _ => hm arm)) using 1
  funext h
  exact (Finset.sup'_apply (s := (Finset.univ : Finset (Fin (m + 1))))
    ⟨0, Finset.mem_univ 0⟩ (fun arm (h : H) =>
      adversarialComparatorRegret reward (adversarialHistoryActions n h) arm) h).symm

/-- A fixed finite reward table has only finitely many possible action-path
regrets, so its expectation is a genuine integrable random variable. -/
theorem integrable_adversarialTableRandomRegret {m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (table : AdversarialRewardTable (m + 1)) (n : Nat) :
    Integrable (adversarialTableRandomRegret table n)
      (adversarialTableHistoryKernel algorithm n table) := by
  let reward := fun t : Fin (n + 1) => table t.val
  refine Integrable.of_bound
    (measurable_adversarialTableRandomRegret table n).aestronglyMeasurable
    (∑ actions : Fin (n + 1) → Fin (m + 1), ‖adversarialRandomRegret reward actions‖)
    (ae_of_all _ fun h => ?_)
  exact Finset.single_le_sum (fun actions _ => norm_nonneg _)
    (Finset.mem_univ (adversarialHistoryActions n h))

theorem adversarialTable_strictTail_eq_one_sub_CDF {m : Nat}
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (table : AdversarialRewardTable (m + 1)) (n : Nat) (u : Real) :
    (adversarialTableHistoryKernel algorithm n table).real
      {h | u < adversarialTableRandomRegret table n h} = 1 - adversarialTableCDF algorithm table n u := by
  have he : {h | u < adversarialTableRandomRegret table n h} =
      {h | adversarialTableRandomRegret table n h <= u}ᶜ := by ext h; simp
  rw [he, measureReal_compl (measurableSet_le (measurable_adversarialTableRandomRegret table n) measurable_const)]
  simp [adversarialTableCDF]

/-- Corrected Theorem 17.4 in the source's CDF-complement notation. -/
theorem adversarialRandomRegret_ge_theorem17_4 {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) (n : Nat)
    (delta : Real) (hd : 0 < delta) (hd32 : delta <= 1 / 32)
    (horizon : 64 * ((m + 1 : Nat) : Real) * Real.log (1 / (2 * delta)) <= ((n + 1 : Nat) : Real)) :
    ∃ table : AdversarialRewardTable (m + 1),
      (∀ t arm, table t arm ∈ Set.Icc (0 : Real) 1) ∧
      delta <= 1 - adversarialTableCDF algorithm table n
        (adversarialHighProbabilityThreshold (n + 1) (m + 1) (1 / 160) delta) := by
  obtain ⟨table, htable, ht⟩ := exists_adversarialTable_randomRegret_gt_theorem17_4 hm algorithm n delta hd hd32 horizon
  refine ⟨table, htable, ?_⟩
  rw [← adversarialTable_strictTail_eq_one_sub_CDF]
  exact ht

end

end LowerBounds
end BanditRLProof
