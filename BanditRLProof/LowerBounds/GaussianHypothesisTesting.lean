import BanditRLProof.LowerBounds.BasicIdeas
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian two-point testing for Chapter 13

This module formalizes the distribution-level threshold test used at the start
of Lattimore--Szepesvári, Chapter 13.1.  The source observes that a sample mean
from `n` independent unit-variance Gaussian observations has variance `1 / n`.
We expose that Gaussian mean-observation law, identify the two error events,
and prove the standard Chernoff upper bound `exp (-n * gap^2 / 8)` for both
hypotheses and therefore for their maximum error probability.

This is a genuine probability theorem, but it is not the sharper two-sided
Mills-ratio estimate displayed as Eq. (13.1).  The latter remains a separate
source obligation and is not inferred from this upper bound.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

/-- Variance `1 / n` of the mean of `n` unit-variance observations. -/
def gaussianSampleMeanVariance (sampleSize : Nat) : NNReal :=
  ⟨(sampleSize : Real)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg sampleSize)⟩

/-- The source's sample-mean variance is nondegenerate for a positive sample size. -/
theorem gaussianSampleMeanVariance_pos
    (sampleSize : Nat) (hsampleSize : 0 < sampleSize) :
    0 < gaussianSampleMeanVariance sampleSize := by
  change 0 < (sampleSize : Real)⁻¹
  exact inv_pos.mpr (Nat.cast_pos.mpr hsampleSize)

/-- The Gaussian law stated in Chapter 13.1 for the sample mean observation. -/
noncomputable def gaussianSampleMeanLaw
    (sampleSize : Nat) (mean : Real) : Measure Real :=
  gaussianReal mean (gaussianSampleMeanVariance sampleSize)

/-- Canonical joint law of `n` independent `N(mean, 1)` observations. -/
noncomputable def gaussianIIDObservationLaw
    (sampleSize : Nat) (mean : Real) : Measure (Fin sampleSize → Real) :=
  Measure.pi (fun _ => gaussianReal mean 1)

/-- Arithmetic mean of a finite coordinate family. -/
def gaussianCoordinateAverage (sampleSize : Nat)
    (observations : Fin sampleSize → Real) : Real :=
  (∑ i, observations i) / (sampleSize : Real)

/-- The sum of the canonical iid observations has mean `n * mean` and variance `n`. -/
theorem gaussianIIDSumLaw (sampleSize : Nat) (mean : Real) :
    (gaussianIIDObservationLaw sampleSize mean).map
        (fun observations => ∑ i, observations i) =
      gaussianReal ((sampleSize : Real) * mean) (sampleSize : NNReal) := by
  unfold gaussianIIDObservationLaw
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_sum_pi_eq_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change (charFun (gaussianReal mean 1) t) ^ sampleSize = _
  rw [charFun_gaussianReal, charFun_gaussianReal]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/--
The arithmetic mean under the canonical product law of `n > 0` independent
`N(mean, 1)` observations has exactly the source law `N(mean, 1 / n)`.
-/
theorem gaussianIIDSampleMeanLaw
    (sampleSize : Nat) (mean : Real) (hsampleSize : 0 < sampleSize) :
    (gaussianIIDObservationLaw sampleSize mean).map
        (gaussianCoordinateAverage sampleSize) =
      gaussianSampleMeanLaw sampleSize mean := by
  have hcast : (sampleSize : Real) ≠ 0 := Nat.cast_ne_zero.mpr hsampleSize.ne'
  rw [show gaussianCoordinateAverage sampleSize =
      (fun total : Real => total / (sampleSize : Real)) ∘
        (fun observations => ∑ i, observations i) by rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [gaussianIIDSumLaw, gaussianReal_map_div_const]
  unfold gaussianSampleMeanLaw gaussianSampleMeanVariance
  congr
  · field_simp
  · ext
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_mk]
    field_simp

/--
Threshold rule for the two hypotheses `mean = 0` and `mean = gap`.
Ties are assigned to `gap`, matching the source's zero-mean error event
`sampleMean >= gap / 2`; for a nondegenerate Gaussian law, the tie has mass
zero.
-/
def twoPointGaussianThresholdDecision (gap observation : Real) : Real :=
  if gap / 2 ≤ observation then gap else 0

/-- Under the zero-mean hypothesis, the threshold rule errs exactly above the midpoint. -/
theorem twoPointGaussianThresholdDecision_zero_error_event
    {gap : Real} (hgap : 0 < gap) :
    {observation | twoPointGaussianThresholdDecision gap observation ≠ 0} =
      Set.Ici (gap / 2) := by
  ext observation
  by_cases hthreshold : gap / 2 ≤ observation
  · simp [twoPointGaussianThresholdDecision, hthreshold, hgap.ne']
  · simp [twoPointGaussianThresholdDecision, hthreshold]

/-- Under the positive-mean hypothesis, errors occur exactly below the midpoint. -/
theorem twoPointGaussianThresholdDecision_gap_error_event
    {gap : Real} (hgap : 0 < gap) :
    {observation | twoPointGaussianThresholdDecision gap observation ≠ gap} =
      Set.Iio (gap / 2) := by
  ext observation
  by_cases hthreshold : gap / 2 ≤ observation
  · simp [twoPointGaussianThresholdDecision, hthreshold]
  · simp only [twoPointGaussianThresholdDecision, if_neg hthreshold,
      Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · intro _
      exact lt_of_not_ge hthreshold
    · intro _
      exact ne_of_lt hgap

/-- Error probability of the threshold decision under the zero-mean sample-mean law. -/
noncomputable def gaussianSampleMeanZeroErrorProbability
    (sampleSize : Nat) (gap : Real) : Real :=
  (gaussianSampleMeanLaw sampleSize 0).real
    {observation | twoPointGaussianThresholdDecision gap observation ≠ 0}

/-- Error probability of the threshold decision under the positive-mean sample-mean law. -/
noncomputable def gaussianSampleMeanGapErrorProbability
    (sampleSize : Nat) (gap : Real) : Real :=
  (gaussianSampleMeanLaw sampleSize gap).real
    {observation | twoPointGaussianThresholdDecision gap observation ≠ gap}

/-- A centered real Gaussian has its variance as a sub-Gaussian proxy. -/
theorem hasSubgaussianMGF_id_gaussianReal_zero (variance : NNReal) :
    HasSubgaussianMGF id variance (gaussianReal 0 variance) := by
  constructor
  · intro t
    simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := variance) t)
  · intro t
    rw [mgf_id_gaussianReal]
    simp

/-- Reflection around the mean turns `N(gap, variance)` into a centered sub-Gaussian. -/
theorem hasSubgaussianMGF_gap_sub_id_gaussianReal
    (gap : Real) (variance : NNReal) :
    HasSubgaussianMGF (fun observation => gap - observation) variance
      (gaussianReal gap variance) := by
  rw [← HasSubgaussianMGF.id_map_iff (by fun_prop)]
  rw [gaussianReal_map_const_sub]
  simpa using hasSubgaussianMGF_id_gaussianReal_zero variance

/-- Chernoff upper bound for a centered Gaussian right tail. -/
theorem gaussianReal_zero_Ici_le_exp_neg_sq_div_two_variance
    (variance : NNReal) (threshold : Real) (hthreshold : 0 ≤ threshold) :
    (gaussianReal 0 variance).real (Set.Ici threshold) ≤
      Real.exp (-threshold ^ 2 / (2 * (variance : Real))) := by
  simpa only [Set.mem_Ici, id_eq] using
    (hasSubgaussianMGF_id_gaussianReal_zero variance).measure_ge_le hthreshold

/-- The positive-mean midpoint error has the same Chernoff exponent by reflection. -/
theorem gaussianReal_gap_Iio_half_le_exp_neg_sq_div_two_variance
    (gap : Real) (variance : NNReal) (hgap : 0 < gap) :
    (gaussianReal gap variance).real (Set.Iio (gap / 2)) ≤
      Real.exp (-(gap / 2) ^ 2 / (2 * (variance : Real))) := by
  have hsubset :
      Set.Iio (gap / 2) ⊆
        {observation | gap / 2 ≤ gap - observation} := by
    intro observation hobservation
    simp only [Set.mem_Iio] at hobservation
    simp only [Set.mem_setOf_eq]
    linarith
  calc
    (gaussianReal gap variance).real (Set.Iio (gap / 2)) ≤
        (gaussianReal gap variance).real
          {observation | gap / 2 ≤ gap - observation} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-(gap / 2) ^ 2 / (2 * (variance : Real))) :=
      (hasSubgaussianMGF_gap_sub_id_gaussianReal gap variance).measure_ge_le
        (by positivity)

/--
For the Chapter 13.1 zero-mean branch, the midpoint threshold has error at
most `exp (-n * gap^2 / 8)` under the stated `N(0, 1/n)` sample-mean law.
-/
theorem gaussianSampleMeanZeroErrorProbability_le_exp
    (sampleSize : Nat) (gap : Real) (hgap : 0 < gap) :
    gaussianSampleMeanZeroErrorProbability sampleSize gap ≤
      Real.exp (-(sampleSize : Real) * gap ^ 2 / 8) := by
  rw [gaussianSampleMeanZeroErrorProbability,
    twoPointGaussianThresholdDecision_zero_error_event hgap]
  unfold gaussianSampleMeanLaw gaussianSampleMeanVariance
  calc
    (gaussianReal 0
        ⟨(sampleSize : Real)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg sampleSize)⟩).real
        (Set.Ici (gap / 2)) ≤
        Real.exp (-(gap / 2) ^ 2 / (2 * (sampleSize : Real)⁻¹)) := by
          simpa only [NNReal.coe_mk] using
            gaussianReal_zero_Ici_le_exp_neg_sq_div_two_variance
              ⟨(sampleSize : Real)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg sampleSize)⟩
              (gap / 2) (by positivity)
    _ = Real.exp (-(sampleSize : Real) * gap ^ 2 / 8) := by
      congr 1
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

/--
For the positive-mean branch, the same midpoint rule has the identical
`exp (-n * gap^2 / 8)` Chernoff upper bound.
-/
theorem gaussianSampleMeanGapErrorProbability_le_exp
    (sampleSize : Nat) (gap : Real) (hgap : 0 < gap) :
    gaussianSampleMeanGapErrorProbability sampleSize gap ≤
      Real.exp (-(sampleSize : Real) * gap ^ 2 / 8) := by
  rw [gaussianSampleMeanGapErrorProbability,
    twoPointGaussianThresholdDecision_gap_error_event hgap]
  unfold gaussianSampleMeanLaw gaussianSampleMeanVariance
  calc
    (gaussianReal gap
        ⟨(sampleSize : Real)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg sampleSize)⟩).real
        (Set.Iio (gap / 2)) ≤
        Real.exp (-(gap / 2) ^ 2 / (2 * (sampleSize : Real)⁻¹)) := by
          simpa only [NNReal.coe_mk] using
            gaussianReal_gap_Iio_half_le_exp_neg_sq_div_two_variance gap
              ⟨(sampleSize : Real)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg sampleSize)⟩ hgap
    _ = Real.exp (-(sampleSize : Real) * gap ^ 2 / 8) := by
      congr 1
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

/-- Worst of the two midpoint-decision error probabilities. -/
noncomputable def gaussianSampleMeanThresholdRisk
    (sampleSize : Nat) (gap : Real) : Real :=
  max (gaussianSampleMeanZeroErrorProbability sampleSize gap)
    (gaussianSampleMeanGapErrorProbability sampleSize gap)

/-- Both Gaussian hypotheses obey the same source-shaped Chernoff exponent. -/
theorem gaussianSampleMeanThresholdRisk_le_exp
    (sampleSize : Nat) (gap : Real) (hgap : 0 < gap) :
    gaussianSampleMeanThresholdRisk sampleSize gap ≤
      Real.exp (-(sampleSize : Real) * gap ^ 2 / 8) := by
  exact max_le
    (gaussianSampleMeanZeroErrorProbability_le_exp sampleSize gap hgap)
    (gaussianSampleMeanGapErrorProbability_le_exp sampleSize gap hgap)

end

end LowerBounds
end BanditRLProof
